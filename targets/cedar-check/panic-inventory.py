#!/usr/bin/env python3
"""Inventory of the code reachable from `Evaluator::interpret` in the M1
cedar-check dylib, for the no-panic proof (Examples/Cedar/NoPanic).

    targets/cedar-check/panic-inventory.py [--dylib D] [--out-dir DIR] [--root REGEX]

Walks the direct call graph (`bl`, and `b` to another symbol's start, i.e. a
tail call) from the root, using `llvm-nm-18 -n` T/t symbols as function
boundaries (a function runs from its symbol to the next distinct symbol
address). It does not descend into

  * panic sinks: functions whose demangled name is a panic entry point
    (core::panicking::*, unwrap_failed, slice index failures, alloc error
    handlers, anything containing `panic`, `unwrap_failed`, `expect_failed`);
  * externals: calls into __stubs (libSystem imports) and the allocator shims
    (`__rust_alloc` & co., `__rdl_*`, `_rust_*`);

and records the call sites to both. It also records inline traps (`brk`,
`udf`), indirect branches (`blr`, `br`; a `br` fed by an `adr` jump-table
computation is classified as a switch), code addresses taken with
`adr`/`adrp+add` (candidate indirect-call targets), and anomalies (calls into
the middle of a function, conditional branches leaving the function). It
computes the SCCs of the reachable call graph (Tarjan, which yields them
bottom-up: callees before callers).

Writes Examples/Cedar/NoPanic/INVENTORY.md (plus INVENTORY-sites.md when the
per-site detail would make it too long) and Examples/Cedar/NoPanic/inventory.json.

Needs llvm-nm-18, llvm-objdump-18 and llvm-otool-18.
"""
import argparse
from bisect import bisect_right
import collections
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def sh(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


# --------------------------------------------------------------------------
# Rust symbol demangling (v0 `_R...` and legacy `_ZN...E`)
# --------------------------------------------------------------------------

B62 = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
BASIC = {'a': 'i8', 'b': 'bool', 'c': 'char', 'd': 'f64', 'e': 'str', 'f': 'f32',
         'h': 'u8', 'i': 'isize', 'j': 'usize', 'l': 'i32', 'm': 'u32', 'n': 'i128',
         'o': 'u128', 's': 'i16', 't': 'u16', 'x': 'i64', 'y': 'u64', 'z': '!',
         'u': '()', 'v': '...', 'p': '_'}
SIGNED = set('ailnsx')


class V0:
    def __init__(self, s):
        self.s, self.i, self.depth = s, 0, 0

    def peek(self):
        return self.s[self.i] if self.i < len(self.s) else ''

    def next(self):
        c = self.s[self.i]
        self.i += 1
        return c

    def eat(self, c):
        if self.peek() == c:
            self.i += 1
            return True
        return False

    def base62(self):
        if self.eat('_'):
            return 0
        x = 0
        while True:
            c = self.next()
            if c == '_':
                return x + 1
            x = x * 62 + B62.index(c)

    def disamb(self):
        return self.base62() + 1 if self.eat('s') else 0

    def decimal(self):
        j = self.i
        if self.eat('0'):
            return 0
        while self.peek().isdigit():
            self.i += 1
        if j == self.i:
            raise ValueError('decimal')
        return int(self.s[j:self.i])

    def uident(self):
        puny = self.eat('u')
        n = self.decimal()
        self.eat('_')
        name = self.s[self.i:self.i + n]
        self.i += n
        return name + ('{puny}' if puny else '')

    def ident(self):
        d = self.disamb()
        return d, self.uident()

    def backref(self, f):
        pos = self.base62()
        save = self.i
        self.i = pos
        self.depth += 1
        if self.depth > 200:
            raise ValueError('backref depth')
        r = f()
        self.depth -= 1
        self.i = save
        return r

    def path(self):
        c = self.next()
        if c == 'C':
            return self.ident()[1]
        if c == 'N':
            ns = self.next()
            p = self.path()
            d, name = self.ident()
            if ns.isupper():
                kind = {'C': 'closure', 'S': 'shim'}.get(ns, ns)
                return f'{p}::{{{kind}{":" + name if name else ""}#{d}}}'
            return f'{p}::{name}' if name else p
        if c == 'M':
            self.disamb()
            self.path()
            return f'<{self.type()}>'
        if c == 'X':
            self.disamb()
            self.path()
            t = self.type()
            return f'<{t} as {self.path()}>'
        if c == 'Y':
            t = self.type()
            return f'<{t} as {self.path()}>'
        if c == 'I':
            p = self.path()
            args = []
            while not self.eat('E'):
                args.append(self.generic_arg())
            return f'{p}<{", ".join(a for a in args if a is not None)}>' if any(
                a is not None for a in args) else p
        if c == 'B':
            return self.backref(self.path)
        raise ValueError(f'path tag {c!r}')

    def generic_arg(self):
        if self.eat('L'):
            self.base62()
            return None  # lifetimes are noise here
        if self.eat('K'):
            return self.const()
        return self.type()

    def const(self):
        if self.eat('B'):
            return self.backref(self.const)
        if self.eat('p'):
            return '_'
        t = self.next()
        if t in BASIC:
            neg = self.eat('n')
            j = self.i
            while self.peek() != '_':
                self.i += 1
            h = self.s[j:self.i]
            self.i += 1
            if t == 'b':
                return 'true' if h == '1' else 'false'
            if t == 'c':
                return repr(chr(int(h or '0', 16)))
            if t == 'e':
                try:
                    return repr(bytes.fromhex(h).decode())
                except ValueError:
                    return '"?"'
            v = int(h or '0', 16)
            return str(-v if neg else v)
        raise ValueError(f'const tag {t!r}')

    def lifetime_opt(self):
        if self.eat('L'):
            self.base62()

    def binder_opt(self):
        if self.eat('G'):
            self.base62()

    def type(self):
        c = self.peek()
        if c in BASIC:
            self.i += 1
            return BASIC[c]
        self.i += 1
        if c == 'A':
            t = self.type()
            return f'[{t}; {self.const()}]'
        if c == 'S':
            return f'[{self.type()}]'
        if c == 'T':
            ts = []
            while not self.eat('E'):
                ts.append(self.type())
            return f'({ts[0]},)' if len(ts) == 1 else f'({", ".join(ts)})'
        if c == 'R':
            self.lifetime_opt()
            return f'&{self.type()}'
        if c == 'Q':
            self.lifetime_opt()
            return f'&mut {self.type()}'
        if c == 'P':
            return f'*const {self.type()}'
        if c == 'O':
            return f'*mut {self.type()}'
        if c == 'F':
            self.binder_opt()
            unsafe = 'unsafe ' if self.eat('U') else ''
            abi = ''
            if self.eat('K'):
                abi = 'extern "C" ' if self.eat('C') else f'extern "{self.uident()}" '
            ps = []
            while not self.eat('E'):
                ps.append(self.type())
            r = self.type()
            return f'{unsafe}{abi}fn({", ".join(ps)})' + ('' if r == '()' else f' -> {r}')
        if c == 'D':
            self.binder_opt()
            traits = []
            while not self.eat('E'):
                p = self.path()
                binds = []
                while self.eat('p'):
                    n = self.uident()
                    binds.append(f'{n} = {self.type()}')
                if binds:
                    p = (p[:-1] + ', ' if p.endswith('>') else p + '<') + ', '.join(binds) + '>'
                traits.append(p)
            self.lifetime_opt()
            return 'dyn ' + ' + '.join(traits)
        if c == 'B':
            return self.backref(self.type)
        self.i -= 1
        return self.path()


def demangle(sym):
    """Demangle a Mach-O symbol name (with its extra leading `_`)."""
    s = sym[1:] if sym.startswith('_') else sym
    base, _, suffix = s.partition('.')
    try:
        if base.startswith('_R'):
            d = V0(base[2:])
            while d.peek().isdigit():
                d.i += 1
            return d.path() + (f' [.{suffix}]' if suffix else '')
        if base.startswith('_ZN'):
            i, parts = 3, []
            while base[i] != 'E':
                j = i
                while base[i].isdigit():
                    i += 1
                n = int(base[j:i])
                parts.append(base[i:i + n])
                i += n
            if re.fullmatch(r'h[0-9a-f]{16}', parts[-1]):
                parts.pop()
            name = '::'.join(parts)
            for a, b in (('$LT$', '<'), ('$GT$', '>'), ('$u20$', ' '), ('$RF$', '&'),
                         ('$C$', ','), ('$u7b$', '{'), ('$u7d$', '}'), ('..', '::')):
                name = name.replace(a, b)
            return name
    except (ValueError, IndexError):
        pass
    return sym


SEG = r'(?:[A-Za-z_][A-Za-z0-9_]*|\{[^{}]*\})'
PATH_RE = re.compile(rf'{SEG}(?:::{SEG})*')


def shorten(name, limit=150):
    """Drop module prefixes (lowercase path segments) from a demangled name,
    keeping one module segment in front of a free function, and truncate."""
    out, depth, i = [], 0, 0
    for m in PATH_RE.finditer(name):
        pre = name[i:m.start()]
        depth += pre.count('<') - pre.count('>')
        out.append(pre)
        segs = m.group(0).split('::')
        k = 0
        while not pre.endswith('::') and k < len(segs) - 1 and re.fullmatch(r'[a-z_][a-z0-9_]*', segs[k]):
            k += 1
        if k == len(segs) - 1 and re.fullmatch(r'[a-z_][a-z0-9_]*', segs[-1]) and k > 0:
            k -= 1  # free function: keep its module
        out.append('::'.join(segs[k:]))
        i = m.end()
    out.append(name[i:])
    s = ''.join(out)
    if len(s) <= limit:
        return s
    tail = max(limit // 3, len(re.search(r'(::[^:]*)?$', s).group(0)) + 1)
    tail = min(tail, limit - 20)
    return s[:limit - tail - 1] + '…' + s[-tail:]


# --------------------------------------------------------------------------
# Classification of call targets
# --------------------------------------------------------------------------

SINK_RULES = [
    (r'^core::panicking::', None),
    (r'^core::option::(unwrap_failed|expect_failed)$', None),
    (r'^core::result::unwrap_failed$', None),
    (r'^core::slice::index::(slice_index_fail|slice_start_index_len_fail|slice_end_index_len_fail'
     r'|slice_index_order_fail|panic_bounds_check)', None),
    (r'^alloc::alloc::handle_alloc_error', None),
    (r'^alloc::raw_vec::(capacity_overflow|handle_error)', None),
    (r'^core::slice::sort::shared::smallsort::panic_on_ord_violation', None),
    (r'^std::panicking::', None),
    (r'^core::cell::panic_already_(mutably_)?borrowed', None),
    (r'^core::str::slice_error_fail', None),
    (r'panic_cold|panic_display', None),
    (r'panic|unwrap_failed|expect_failed', None),
]
EXTERNAL_NAME = re.compile(r'(^|::)_{0,3}(rust_[a-z_0-9]*|__rust_[a-z_0-9]*|__rdl_[a-z_0-9]*|__rg_[a-z_0-9]*)$')
EXTERNAL_RAW = re.compile(r'^_{1,3}(rust_|rdl_|rg_)|^_(malloc|free|calloc|realloc|posix_memalign|mem\w+|bcmp|bzero)$')


def base_name(dm):
    """Demangled name without generic arguments and LLVM suffix."""
    dm = re.sub(r' \[\..*\]$', '', dm)
    out, depth = [], 0
    for ch in dm:
        if ch == '<':
            depth += 1
        elif ch == '>':
            depth -= 1
        elif depth == 0:
            out.append(ch)
    s = ''.join(out)
    return s


def sink_kind(dm):
    """Sink label (last two path segments, generics dropped), or None."""
    b = base_name(dm)
    if b.startswith('::'):
        # `<T as Trait>::method` / `<T>::method`: classify on the whole name
        b = dm
    for rx, _ in SINK_RULES:
        if re.search(rx, b) or (rx.startswith('panic|') and re.search(rx, dm)):
            segs = [s for s in base_name(dm).split('::') if s]
            return '::'.join(segs[-2:]) if segs else dm
    return None


def is_external(raw, dm):
    return bool(EXTERNAL_RAW.search(raw) or EXTERNAL_NAME.search(base_name(dm)))


# --------------------------------------------------------------------------
# Binary
# --------------------------------------------------------------------------

def load(dylib):
    lc = sh('llvm-otool-18', '-l', dylib)
    sects = []
    for m in re.finditer(r'sectname (\S+)\n\s*segname (\S+)\n\s*addr 0x([0-9a-f]+)\n\s*size 0x([0-9a-f]+)\n'
                         r'\s*offset (\d+)', lc):
        sects.append(dict(sect=m.group(1), seg=m.group(2), addr=int(m.group(3), 16),
                          size=int(m.group(4), 16), off=int(m.group(5))))
    text = next(s for s in sects if s['sect'] == '__text')
    stubs = next((s for s in sects if s['sect'] == '__stubs'), None)

    by_addr = collections.defaultdict(list)
    for line in sh('llvm-nm-18', '-n', dylib).splitlines():
        p = line.split()
        if len(p) == 3 and p[1] in 'Tt':
            by_addr[int(p[0], 16)].append(p[2])
    starts = sorted(a for a in by_addr if text['addr'] <= a < text['addr'] + text['size'])

    stub_names = {}
    for line in sh('llvm-otool-18', '-Iv', dylib).splitlines():
        m = re.match(r'\s*0x([0-9a-f]+)\s+\d+\s+(\S+)', line)
        if m and stubs and stubs['addr'] <= int(m.group(1), 16) < stubs['addr'] + stubs['size']:
            stub_names[int(m.group(1), 16)] = m.group(2)

    insns = {}
    for line in sh('llvm-objdump-18', '-d', '--no-show-raw-insn', '--mattr=+v8.5a,+lse,+rcpc,+rcpc-immo',
                   f'--start-address={text["addr"]}', f'--stop-address={text["addr"] + text["size"]}',
                   dylib).splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$', line)
        if m:
            ops = re.sub(r'\s+', ' ', m.group(3)).strip()
            insns[int(m.group(1), 16)] = (m.group(2), ops)
    blob = open(dylib, 'rb').read()
    return dict(sects=sects, text=text, stubs=stubs, by_addr=by_addr, starts=starts,
                stub_names=stub_names, insns=insns, blob=blob)


def read_bytes(B, addr, n):
    for s in B['sects']:
        if s['seg'] == '__TEXT' and s['addr'] <= addr and addr + n <= s['addr'] + s['size']:
            o = s['off'] + addr - s['addr']
            return B['blob'][o:o + n]
    return None


TARGET_RE = re.compile(r'^0x([0-9a-f]+)')
COND = re.compile(r'^(b\.\w+|cbz|cbnz|tbz|tbnz)$')


def branch_target(mn, ops):
    if mn in ('b', 'bl') or COND.match(mn):
        m = re.search(r'(?:^|, )0x([0-9a-f]+)(?: <|$)', ops)
        if m:
            return int(m.group(1), 16)
    return None


def short_insn(mn, ops):
    ops = re.sub(r' <[^>]*>', '', ops)
    return f'{mn} {ops}'.strip()


# --------------------------------------------------------------------------
# Analysis
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dylib', default=f'{HERE}/target/aarch64-apple-darwin/release/libcedar_check.dylib')
    ap.add_argument('--out-dir', default=f'{REPO}/Examples/Cedar/NoPanic')
    ap.add_argument('--root', default=r'(^|[<:])Evaluator>?::interpret$',
                    help='regex on the demangled name (LLVM suffix dropped) of the root')
    ap.add_argument('--max-md-lines', type=int, default=3000)
    args = ap.parse_args()

    B = load(args.dylib)
    text, stubs, insns, by_addr, starts = B['text'], B['stubs'], B['insns'], B['by_addr'], B['starts']
    text_end = text['addr'] + text['size']
    end_of = {a: (starts[i + 1] if i + 1 < len(starts) else text_end) for i, a in enumerate(starts)}
    start_set = set(starts)
    dm_cache = {}

    def names(a):
        return by_addr[a]

    def dm(raw):
        if raw not in dm_cache:
            dm_cache[raw] = demangle(raw)
        return dm_cache[raw]

    def primary(a):
        ns = names(a)
        return min(ns, key=lambda n: (n.startswith('_OUTLINED'), len(n)))

    # 1. the root
    root_re = re.compile(args.root)
    roots = sorted({a for a in starts for n in names(a)
                    if root_re.search(re.sub(r' \[\..*\]$', '', dm(n)))})
    if len(roots) != 1:
        sys.exit(f'root regex {args.root!r} matched {len(roots)} functions: '
                 + ', '.join(f'0x{a:x} {dm(primary(a))}' for a in roots))
    root = roots[0]
    print(f'root: 0x{root:x} {dm(primary(root))}  ({primary(root)})')

    def classify(a):
        """('internal'|'sink'|'external'|'mid', label) for a code address."""
        if stubs and stubs['addr'] <= a < stubs['addr'] + stubs['size']:
            return 'external', B['stub_names'].get(a, f'__stubs+0x{a - stubs["addr"]:x}')
        if not (text['addr'] <= a < text_end):
            return 'external', f'0x{a:x}'
        if a not in start_set:
            return 'mid', None
        for n in names(a):
            k = sink_kind(dm(n))
            if k:
                return 'sink', k
        for n in names(a):
            if is_external(n, dm(n)):
                return 'external', shorten(base_name(dm(n)))
        return 'internal', None

    # 2-5. walk
    funcs = {}
    work = [root]
    seen = {root}
    sinks = {}      # addr -> {name, kind, sites}
    externals = {}  # label -> {addr, sites}
    func_of = lambda a: starts[bisect_right(starts, a) - 1]


    while work:
        f = work.pop()
        lo, hi = f, end_of[f]
        body = [(a, *insns[a]) for a in range(lo, hi, 4) if a in insns]
        F = dict(addr=f, end=hi, ninsn=len(body), raw=primary(f), aliases=names(f),
                 name=dm(primary(f)), callees=[], calls=[], panic_sites=[], traps=[],
                 indirect=[], ext_calls=[], addr_taken=[], anomalies=[])
        funcs[f] = F
        regs = {}  # last adrp/adr value per register, for adrp+add / jump tables
        for idx, (a, mn, ops) in enumerate(body):
            t = branch_target(mn, ops)
            if mn in ('adrp', 'adr'):
                m = re.match(r'(x\d+), 0x([0-9a-f]+)', ops)
                if m:
                    regs[m.group(1)] = int(m.group(2), 16)
                    if mn == 'adr' and int(m.group(2), 16) in start_set and not lo <= int(m.group(2), 16) < hi:
                        F['addr_taken'].append(dict(site=a, target=int(m.group(2), 16)))
            elif mn == 'add':
                m = re.match(r'(x\d+), (x\d+), #0x([0-9a-f]+)$', ops)
                if m and m.group(2) in regs:
                    v = regs[m.group(2)] + int(m.group(3), 16)
                    if v in start_set and not lo <= v < hi:
                        F['addr_taken'].append(dict(site=a, target=v))
            if mn in ('brk', 'udf', 'hlt'):
                F['traps'].append(dict(site=a, insn=short_insn(mn, ops)))
            elif mn in ('blr', 'br', 'blraa', 'blraaz', 'braa', 'braaz', 'blrab', 'brab'):
                kind = 'call' if mn.startswith('bl') else 'tail'
                if kind == 'tail':
                    win = body[max(0, idx - 6):idx]
                    if any(w[1] == 'adr' for w in win) and any(w[1] in ('ldrb', 'ldrh', 'ldrsw', 'ldr') and '[' in w[2]
                                                               for w in win):
                        kind = 'switch'
                F['indirect'].append(dict(site=a, insn=short_insn(mn, ops), kind=kind))
            if t is None:
                continue
            if lo <= t < hi and mn != 'bl' and not (mn == 'b' and t == lo):
                continue  # intra-procedural branch
            if mn == 'bl' and lo < t < hi:
                F['anomalies'].append(dict(site=a, insn=short_insn(mn, ops), what='bl into own body'))
                continue
            how = 'call' if mn == 'bl' else ('tail' if mn == 'b' else 'cond-tail')
            cls, label = classify(t)
            if cls == 'mid':
                F['anomalies'].append(dict(site=a, insn=short_insn(mn, ops),
                                           what=f'{how} into middle of 0x{func_of(t):x}+0x{t - func_of(t):x} '
                                                f'{shorten(dm(primary(func_of(t))), 80)}'))
                continue
            if how == 'cond-tail':
                F['anomalies'].append(dict(site=a, insn=short_insn(mn, ops), what='conditional tail branch'))
            if cls == 'internal':
                F['calls'].append(dict(site=a, target=t, how=how))
                if t not in F['callees']:
                    F['callees'].append(t)
                if t not in seen:
                    seen.add(t)
                    work.append(t)
            elif cls == 'sink':
                s = sinks.setdefault(t, dict(addr=t, raw=primary(t), name=dm(primary(t)), kind=label, sites=0))
                s['sites'] += 1
                F['panic_sites'].append(dict(site=a, sink=t, kind=label, how=how))
            else:
                e = externals.setdefault(label, dict(name=label, addr=t, sites=0))
                e['sites'] += 1
                F['ext_calls'].append(dict(site=a, target=t, name=label, how=how))

    # guards and context for panic sites and traps
    def analyse_site(F, site):
        lo, hi = F['addr'], F['end']
        # straight-line block containing `site`
        b = site
        while b - 4 >= lo:
            mn, ops = insns.get(b - 4, ('?', ''))
            if mn in ('b', 'ret', 'br', 'braa', 'braaz', 'brk', 'udf') or COND.match(mn) \
                    or (mn == 'bl' and classify(branch_target(mn, ops) or 0)[0] == 'sink'):
                break
            b -= 4
        guards = []
        for a in range(lo, hi, 4):
            if a not in insns:
                continue
            mn, ops = insns[a]
            t = branch_target(mn, ops)
            if t is not None and b <= t <= site and mn != 'bl':
                guards.append(dict(site=a, insn=short_insn(mn, ops), target=t, how='jump'))
        if b - 4 >= lo:
            mn, ops = insns.get(b - 4, ('?', ''))
            if COND.match(mn):
                guards.append(dict(site=b - 4, insn=short_insn(mn, ops), target=branch_target(mn, ops),
                                   how='fallthrough'))
        ctx = [dict(site=a, insn=short_insn(*insns[a])) for a in range(max(lo, site - 12), site, 4) if a in insns]
        # message: x0 = adrp+add, x1 = mov #len within the block
        x0 = x1 = None
        for a in range(b, site, 4):
            mn, ops = insns.get(a, ('', ''))
            m = re.match(r'x0, 0x([0-9a-f]+)', ops)
            if mn == 'adrp' and m:
                x0 = int(m.group(1), 16)
            m = re.match(r'x0, x0, #0x([0-9a-f]+)$', ops)
            if mn == 'add' and m and x0 is not None:
                x0 += int(m.group(1), 16)
            m = re.match(r'[wx]1, #0x([0-9a-f]+)', ops) or re.match(r'[wx]1, #(\d+)', ops)
            if mn == 'mov' and m:
                x1 = int(m.group(1), 16) if '0x' in ops else int(m.group(1))
        msg = None
        if x0 is not None and x1 is not None and 0 < x1 < 400:
            bs = read_bytes(B, x0, x1)
            if bs is not None:
                try:
                    s = bs.decode()
                    if s.isprintable():
                        msg = s
                except UnicodeDecodeError:
                    pass
        return dict(block=b, guards=guards, context=ctx, msg=msg)

    for F in funcs.values():
        for s in F['panic_sites']:
            s.update(analyse_site(F, s['site']))
        for s in F['traps']:
            s.update(analyse_site(F, s['site']))

    # 6. SCCs (iterative Tarjan): emitted callees-first, i.e. bottom-up
    index, low, onstack, stack, sccs, counter = {}, {}, set(), [], [], [0]
    for v0 in sorted(funcs):
        if v0 in index:
            continue
        it = [(v0, iter(funcs[v0]['callees']))]
        index[v0] = low[v0] = counter[0]; counter[0] += 1
        stack.append(v0); onstack.add(v0)
        while it:
            v, children = it[-1]
            w = next(children, None)
            if w is not None:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); onstack.add(w)
                    it.append((w, iter(funcs[w]['callees'])))
                elif w in onstack:
                    low[v] = min(low[v], index[w])
                continue
            it.pop()
            if it:
                low[it[-1][0]] = min(low[it[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop(); onstack.discard(w); comp.append(w)
                    if w == v:
                        break
                sccs.append(sorted(comp))
    order = []
    scc_info = []
    for i, comp in enumerate(sccs):
        rec = len(comp) > 1 or comp[0] in funcs[comp[0]]['callees']
        scc_info.append(dict(id=i, members=comp, recursive=rec))
        for f in comp:
            funcs[f]['scc'] = i
            funcs[f]['scc_recursive'] = rec
            funcs[f]['order'] = len(order)
            order.append(f)

    emit(args, B, root, funcs, order, scc_info, sinks, externals, insns)


def hx(a):
    return f'0x{a:x}'


def emit(args, B, root, funcs, order, sccs, sinks, externals, insns):
    os.makedirs(args.out_dir, exist_ok=True)
    kinds = sorted({s['kind'] for s in sinks.values()})
    kind_sites = collections.Counter(p['kind'] for F in funcs.values() for p in F['panic_sites'])
    abbrev = {}
    for k in kinds:
        last = k.split('::')[-1]
        a = re.sub(r'^panic_const_', '', last)
        a = {'unwrap_failed': k.split('::')[0] + '.unwrap', 'expect_failed': k.split('::')[0] + '.expect'}.get(a, a)
        abbrev[k] = a
    ninsn = sum(F['ninsn'] for F in funcs.values())
    ntraps = sum(len(F['traps']) for F in funcs.values())
    ind = collections.Counter(i['kind'] for F in funcs.values() for i in F['indirect'])
    rec = [s for s in sccs if s['recursive']]
    largest = max(sccs, key=lambda s: len(s['members']))
    with_sites = [F for F in funcs.values() if F['panic_sites'] or F['traps']]
    anomalies = [(F, x) for F in funcs.values() for x in F['anomalies']]
    taken = collections.Counter(t['target'] for F in funcs.values() for t in F['addr_taken'])

    L = []
    w = L.append
    w('# No-panic inventory: `Evaluator::interpret`')
    w('')
    w('Generated by `targets/cedar-check/panic-inventory.py` from the M1 build of')
    w('targets/cedar-check (`libcedar_check.dylib`). DO NOT EDIT: regenerate instead.')
    w('Machine-readable version: `inventory.json` (same directory).')
    w('')
    w(f'Root: `{funcs[root]["name"]}` at `{hx(root)}` (`{funcs[root]["raw"]}`).')
    w('')
    w('Reachability follows direct calls (`bl`) and tail calls (`b` to another symbol\'s start). '
      'Panic sinks and externals are not descended into. Indirect branches (`blr`, non-switch `br`) '
      'are recorded but **not followed**: their targets are not in this inventory.')
    w('')
    w('## Summary')
    w('')
    w(f'| | |\n|---|---|')
    w(f'| reachable functions | {len(funcs)} |')
    w(f'| instructions | {ninsn} |')
    w(f'| SCCs | {len(sccs)} ({len(rec)} recursive; largest has {len(largest["members"])} functions) |')
    w(f'| direct internal call edges | {sum(len(F["callees"]) for F in funcs.values())} |')
    w(f'| panic call sites | {sum(kind_sites.values())} in {sum(1 for F in funcs.values() if F["panic_sites"])} functions |')
    w(f'| inline traps (`brk`/`udf`) | {ntraps} in {sum(1 for F in funcs.values() if F["traps"])} functions |')
    w(f'| indirect calls (`blr`) | {ind["call"]} |')
    w(f'| indirect jumps (`br`): switch tables / indirect tail calls | {ind["switch"]} / {ind["tail"]} |')
    w(f'| distinct externals called | {len(externals)} ({sum(e["sites"] for e in externals.values())} sites) |')
    w(f'| functions with no callees, no panic sites, no traps, no indirect branches | '
      f'{sum(1 for F in funcs.values() if not (F["callees"] or F["panic_sites"] or F["traps"] or F["indirect"] or F["ext_calls"]))} |')
    w(f'| anomalies (calls into function bodies, conditional tail branches) | {len(anomalies)} |')
    w('')
    w('## Panic sinks matched')
    w('')
    w('| sink | abbrev | address | call sites |\n|---|---|---|---|')
    for s in sorted(sinks.values(), key=lambda s: -s['sites']):
        w(f'| `{shorten(s["name"], 200)}` | {abbrev[s["kind"]]} | `{hx(s["addr"])}` | {s["sites"]} |')
    w('')
    w('Call sites per sink kind: ' + ', '.join(f'{abbrev[k]} {n}' for k, n in kind_sites.most_common()) + '.')
    w('')
    w('## Externals called')
    w('')
    w('| external | address | call sites |\n|---|---|---|')
    for e in sorted(externals.values(), key=lambda e: -e['sites']):
        w(f'| `{e["name"]}` | `{hx(e["addr"])}` | {e["sites"]} |')
    w('')
    if anomalies:
        w('## Anomalies')
        w('')
        for F, x in anomalies:
            w(f'- `{hx(x["site"])}` in `{shorten(F["name"], 80)}`: `{x["insn"]}`: {x["what"]}')
        w('')
    if rec:
        w('## Recursive SCCs')
        w('')
        for s in rec:
            w(f'- SCC {s["id"]} ({len(s["members"])} functions): ' +
              ', '.join(f'`{hx(m)}` {shorten(funcs[m]["name"], 70)}' for m in s['members'][:12]) +
              (' …' if len(s['members']) > 12 else ''))
        w('')
    if taken:
        w('## Code addresses taken (`adr`/`adrp+add`; candidate indirect-call targets, not followed)')
        w('')
        for t, n in sorted(taken.items()):
            nm = B['by_addr'][t][0]
            w(f'- `{hx(t)}` ({n}×) {shorten(demangle(nm), 140)}')
        w('')
    w('## Functions, bottom-up')
    w('')
    w('Callees come before callers; members of one SCC are adjacent. `scc*` = recursive SCC. '
      'Panic sites are given per sink kind (abbreviations above). `ind` = indirect calls/jumps '
      '(`c`=`blr` indirect call, `t`=`br` indirect tail call, `s`=switch-table `br`).')
    w('')
    w('| # | addr | insns | function | scc | callees | panic sites | traps | ind |\n|---|---|---|---|---|---|---|---|---|')
    for f in order:
        F = funcs[f]
        ps = collections.Counter(abbrev[p['kind']] for p in F['panic_sites'])
        ic = collections.Counter(i['kind'] for i in F['indirect'])
        indt = ' '.join(f'{k[0]}{ic[k]}' for k in ('call', 'tail', 'switch') if ic[k])
        name = shorten(F['name'], 110).replace('|', '\\|')
        w(f'| {F["order"]} | `{hx(f)}` | {F["ninsn"]} | `{name}` | {F["scc"]}{"*" if F["scc_recursive"] else ""} '
          f'| {len(F["callees"])} | {" ".join(f"{k}:{n}" for k, n in sorted(ps.items()))} '
          f'| {len(F["traps"]) or ""} | {indt} |')
    w('')

    S = []
    s = S.append
    s('## Panic sites and traps, per function')
    s('')
    s('For each site: the sink called (or trap), the guarding branches (conditional branches whose '
      'target lies in the straight-line block ending at the site — `jump` — or the conditional branch '
      'the block falls through from — `fallthrough`), the panic message when it is a literal, and the '
      'three instructions before the site.')
    s('')
    for f in order:
        F = funcs[f]
        if not (F['panic_sites'] or F['traps']):
            continue
        s(f'### #{F["order"]} `{hx(f)}` {shorten(F["name"], 160)}')
        s('')
        for p in sorted(F['panic_sites'] + F['traps'], key=lambda p: p['site']):
            what = (f'{abbrev[p["kind"]]} (`{hx(p["sink"])}`{", tail" if p["how"] != "call" else ""})'
                    if 'sink' in p else f'trap `{p["insn"]}`')
            g = '; '.join(f'`{hx(x["site"])}: {x["insn"]}` ({x["how"]})' for x in p['guards'][:6])
            if len(p['guards']) > 6:
                g += f'; … {len(p["guards"]) - 6} more'
            s(f'- `{hx(p["site"])}` {what}' + (f' msg {json.dumps(p["msg"])}' if p.get('msg') else ''))
            s(f'  - guards: {g or "none found (unconditional on this path)"}')
            s('  - context: ' + ' ; '.join(f'`{c["insn"]}`' for c in p['context']))
        s('')

    md = os.path.join(args.out_dir, 'INVENTORY.md')
    if len(L) + len(S) > args.max_md_lines:
        L.append(f'Per-site detail ({sum(len(F["panic_sites"]) + len(F["traps"]) for F in with_sites)} sites): '
                 'see [INVENTORY-sites.md](INVENTORY-sites.md).')
        open(os.path.join(args.out_dir, 'INVENTORY-sites.md'), 'w').write(
            '# No-panic inventory: per-site detail\n\nGenerated by `targets/cedar-check/panic-inventory.py`. '
            'DO NOT EDIT.\n\n' + '\n'.join(S) + '\n')
        open(md, 'w').write('\n'.join(L) + '\n')
    else:
        open(md, 'w').write('\n'.join(L + S) + '\n')
        p = os.path.join(args.out_dir, 'INVENTORY-sites.md')
        if os.path.exists(p):
            os.remove(p)

    def site_json(p):
        q = dict(p)
        for k in ('site', 'sink', 'target', 'block'):
            if k in q and q[k] is not None:
                q[k] = hx(q[k])
        if 'guards' in q:
            q['guards'] = [dict(g, site=hx(g['site']), target=hx(g['target']) if g['target'] is not None else None)
                           for g in q['guards']]
        if 'context' in q:
            q['context'] = [dict(c, site=hx(c['site'])) for c in q['context']]
        return q

    J = dict(
        root=hx(root), root_name=funcs[root]['name'], dylib=os.path.relpath(args.dylib, REPO),
        summary=dict(functions=len(funcs), instructions=sum(F['ninsn'] for F in funcs.values()),
                     sccs=len(sccs), recursive_sccs=len(rec), largest_scc=len(largest['members']),
                     panic_sites=dict(kind_sites), traps=ntraps, indirect=dict(ind), externals=len(externals)),
        functions={hx(f): dict(
            addr=hx(f), end=hx(F['end']), ninsn=F['ninsn'], name=F['name'], short=shorten(F['name']),
            mangled=F['raw'], aliases=F['aliases'], scc=F['scc'], recursive=F['scc_recursive'],
            order=F['order'], callees=[hx(c) for c in F['callees']],
            calls=[site_json(c) for c in F['calls']], panic_sites=[site_json(p) for p in F['panic_sites']],
            traps=[site_json(t) for t in F['traps']], indirect=[site_json(i) for i in F['indirect']],
            ext_calls=[site_json(e) for e in F['ext_calls']], addr_taken=[site_json(t) for t in F['addr_taken']],
            anomalies=[site_json(x) for x in F['anomalies']]) for f, F in funcs.items()},
        edges=[[hx(f), hx(c['target']), hx(c['site']), c['how']] for f in order for c in funcs[f]['calls']],
        sccs=[dict(id=s['id'], recursive=s['recursive'], members=[hx(m) for m in s['members']]) for s in sccs],
        order=[hx(f) for f in order],
        sinks={hx(a): dict(name=x['name'], mangled=x['raw'], kind=x['kind'], abbrev=abbrev[x['kind']],
                           sites=x['sites']) for a, x in sorted(sinks.items())},
        externals={k: dict(addr=hx(e['addr']), sites=e['sites']) for k, e in sorted(externals.items())},
    )
    with open(os.path.join(args.out_dir, 'inventory.json'), 'w') as fh:
        json.dump(J, fh, indent=1)
    # The forbidden PCs, as a Lean definition.
    lean = ['/-', '  Generated by targets/cedar-check/panic-inventory.py. DO NOT EDIT: regenerate instead.', '-/',
            'import M1', '', 'namespace Examples.Cedar.NoPanic', 'open M1', '',
            '/-- The entry points of the panic machinery reachable from `Evaluator::interpret`',
            '(the sinks of `INVENTORY.md`): a state whose PC is one of these is panicking. -/',
            '@[m1_sym] def Panic (a : BitVec 64) : Prop :=']
    ss = sorted(sinks.items())
    for i, (a, x) in enumerate(ss):
        sep = ' ∨' if i + 1 < len(ss) else ''
        lean.append(f'  a = 0x{a:x}#64{sep} -- {x["name"]}')
    lean += ['', 'end Examples.Cedar.NoPanic', '']
    with open(os.path.join(args.out_dir, 'Sinks.lean'), 'w') as fh:
        fh.write('\n'.join(lean))
    print(f'{len(funcs)} functions, {J["summary"]["instructions"]} instructions, {len(sccs)} SCCs '
          f'({len(rec)} recursive, largest {len(largest["members"])}), panic sites {dict(kind_sites)}, '
          f'{ntraps} traps, indirect {dict(ind)}, {len(externals)} externals; wrote {md}')


if __name__ == '__main__':
    main()
