use std::str::FromStr;

use cedar_check::{check, Outcome};
use cedar_policy::{eval_expression, EvaluationError, Expression};

fn code(src: &str) -> i32 {
    check(src).code()
}

/// What evaluation does with no typecheck first (to show the gate matters).
fn raw_eval_is_type_error(src: &str) -> bool {
    // Rebuild the same environment through the public constructors.
    let (schema, _) = cedar_policy::Schema::from_cedarschema_str(cedar_check::SCHEMA).unwrap();
    let entities = cedar_policy::Entities::from_json_str(cedar_check::ENTITIES, Some(&schema)).unwrap();
    let uid = |s: &str| cedar_policy::EntityUid::from_str(s).unwrap();
    let action = uid(cedar_check::ACTION);
    let ctx = cedar_policy::Context::from_json_str(cedar_check::CONTEXT, Some((&schema, &action))).unwrap();
    let req = cedar_policy::Request::new(uid(cedar_check::PRINCIPAL), action, uid(cedar_check::RESOURCE), ctx, Some(&schema)).unwrap();
    matches!(
        eval_expression(&req, &entities, &Expression::from_str(src).unwrap()),
        Err(EvaluationError::TypeError(_))
    )
}

#[test]
fn parse_errors() {
    for s in ["", "1 +", "permit(principal, action, resource);", "true }; permit(principal, action, resource) when { true"] {
        assert_eq!(code(s), 0, "{s:?}");
    }
    assert_eq!(unsafe { cedar_check::cedar_check([0xff, 0xfe].as_ptr(), 2) }, 0);
}

#[test]
fn well_typed_values() {
    for s in [
        "1 + 2",
        "\"abc\" like \"a*\"",
        "principal.name",
        "principal.age >= 18 && context.n < 10",
        "resource.owner == principal",
        "resource.tags.contains(\"a\")",
        "principal in Group::\"admins\"",
        "principal has name",
        "if resource.public then 1 else 2",
        "{ a: 1, b: [true, false] }",
        "context.ip.isInRange(ip(\"10.0.0.0/8\"))",
        "decimal(\"1.5\").lessThan(decimal(\"2.0\"))",
        "action == Action::\"read\"",
        // The typechecker types `true` as a singleton and skips the dead branch.
        "if true then 1 else \"a\"",
        // `==` across unrelated types is typed as `False`, not rejected.
        "1 == \"a\"",
    ] {
        assert!(matches!(check(s), Outcome::Value(_)), "{s:?}: {:?}", check(s));
    }
}

#[test]
fn well_typed_runtime_errors_are_not_type_errors() {
    // The typechecker does not rule these out; they are not type errors.
    for s in ["9223372036854775807 + 1", "User::\"bob\".age", "-9223372036854775807 - 2"] {
        assert!(matches!(check(s), Outcome::EvalError(_)), "{s:?}: {:?}", check(s));
    }
}

#[test]
fn ill_typed_rejected_before_evaluation() {
    // Each of these would raise a type error if evaluated: the typecheck is
    // what keeps `check` away from the unreachable path.
    for s in [
        "1 + \"a\"",
        "(if context.n == 2 then 1 else \"a\") + 1",
        "principal.age && true",
        "!principal.name",
        "resource.tags.contains(\"a\") && 1",
        "context.ip.isInRange(1)",
        "\"a\" < 1",
    ] {
        assert_eq!(code(s), 1, "{s:?}");
        assert!(raw_eval_is_type_error(s), "{s:?} should be a runtime type error");
    }
    // Ill-typed but no runtime type error: still rejected.
    for s in ["principal.nope", "[]", "principal.age.name"] {
        assert_eq!(code(s), 1, "{s:?}");
    }
}

/// Random expressions over the schema's vocabulary; `check` panics (via the
/// unreachable assertion) if any well-typed one raises a type error.
#[test]
fn random_expressions_never_reach_the_assertion() {
    let atoms = [
        "1", "0", "-3", "9223372036854775807", "true", "false", "\"a\"", "\"\"",
        "principal", "resource", "action", "context", "principal.name", "principal.age",
        "resource.owner", "resource.tags", "resource.public", "context.n", "context.ip",
        "User::\"alice\"", "User::\"bob\"", "Group::\"admins\"", "[1, 2]", "[\"a\"]",
        "{ x: 1 }", "ip(\"10.0.0.1\")", "decimal(\"1.0\")",
    ];
    let mut seed: u64 = 0x9e3779b97f4a7c15;
    let mut rnd = move |n: usize| {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        (seed % n as u64) as usize
    };
    fn gen(d: u32, atoms: &[&str], r: &mut dyn FnMut(usize) -> usize) -> String {
        if d == 0 { return atoms[r(atoms.len())].to_string(); }
        let a = gen(d - 1, atoms, r);
        let b = gen(d - 1, atoms, r);
        match r(20) {
            0 => format!("({a} + {b})"), 1 => format!("({a} - {b})"), 2 => format!("({a} * {b})"),
            3 => format!("({a} == {b})"), 4 => format!("({a} < {b})"), 5 => format!("({a} && {b})"),
            6 => format!("({a} || {b})"), 7 => format!("(!{a})"), 8 => format!("(-{a})"),
            9 => format!("({a} in {b})"), 10 => format!("({a}.contains({b}))"),
            11 => format!("(if {a} then {b} else {})", gen(d - 1, atoms, r)),
            12 => format!("({a} has name)"), 13 => format!("({a}.age)"), 14 => format!("[{a}, {b}]"),
            15 => format!("({a} like \"a*\")"), 16 => format!("({a}.isInRange({b}))"),
            17 => format!("({a}.lessThan({b}))"), 18 => format!("({a}.containsAll({b}))"),
            _ => format!("{{ f: {a} }}.f"),
        }
    }
    let mut counts = [0usize; 4];
    for _ in 0..20_000 {
        let d = rnd(4) as u32;
        let s = gen(d, &atoms, &mut rnd);
        counts[code(&s) as usize] += 1;
    }
    eprintln!("parse error / ill-typed / value / eval error: {counts:?}");
    assert!(counts[2] > 1000 && counts[1] > 1000, "generator should hit both sides: {counts:?}");
}
