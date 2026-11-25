#!/usr/bin/env bash
# Cross-compile this crate from Linux to an arm64 macOS (M1) dylib.
#
#   targets/cedar-check/build-m1.sh
#   -> target/aarch64-apple-darwin/release/libcedar_check.dylib
#
# Needs rustup, clang and ld64.lld (LLVM). No macOS SDK: the only libraries a
# Rust dylib links against are libSystem (and libiconv), so we generate
# text stubs (.tbd) for them that list exactly the symbols the image
# imports. The result binds to the real /usr/lib/libSystem.B.dylib at load
# time, like any other macOS binary.
set -euo pipefail
cd "$(dirname "$0")"

TARGET=aarch64-apple-darwin
SDK=$PWD/target/m1-sdk
OUT=target/$TARGET/release/libcedar_check.dylib
NM=$(command -v llvm-nm || command -v llvm-nm-18)

rustup target list --installed | grep -qx $TARGET || rustup target add $TARGET
mkdir -p "$SDK/usr/lib" "$SDK/bin"

# C compiler and linker for the target: clang + ld64.lld against the stub SDK.
cat > "$SDK/bin/cc" <<CC
#!/bin/sh
exec clang --target=arm64-apple-macos11.0 -fuse-ld=lld -isysroot "$SDK" -mlinker-version=711 \$M1_LINK_EXTRA "\$@"
CC
chmod +x "$SDK/bin/cc"
export SDKROOT="$SDK" CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER="$SDK/bin/cc" CC_aarch64_apple_darwin="$SDK/bin/cc"

# tbd FILE INSTALL-NAME [SYMBOL...]
tbd() {
  local file=$1 name=$2; shift 2
  {
    echo '--- !tapi-tbd'; echo 'tbd-version: 4'; echo 'targets: [ arm64-macos ]'
    echo "install-name: '$name'"; echo 'current-version: 1319'
    if [ $# -gt 0 ]; then
      echo 'exports:'; echo '  - targets: [ arm64-macos ]'; echo '    symbols: ['
      printf "      '%s',\n" "$@" | sed '$ s/,$//'; echo '    ]'
    fi
    echo '...'
  } > "$file"
}
tbd "$SDK/usr/lib/libSystem.tbd" /usr/lib/libSystem.B.dylib
tbd "$SDK/usr/lib/libiconv.tbd" /usr/lib/libiconv.2.dylib
ln -sf libSystem.tbd "$SDK/usr/lib/libc.tbd"; ln -sf libSystem.tbd "$SDK/usr/lib/libm.tbd"

# Pass 1: link with undefined symbols allowed, to learn what the image imports.
M1_LINK_EXTRA="-Wl,-undefined,dynamic_lookup" cargo build --release --target $TARGET
mapfile -t IMPORTS < <("$NM" -u "$OUT" | sort -u)
tbd "$SDK/usr/lib/libSystem.tbd" /usr/lib/libSystem.B.dylib dyld_stub_binder "${IMPORTS[@]}"

# Pass 2: relink with every import resolved against the libSystem stub.
touch src/lib.rs
cargo build --release --target $TARGET
echo "built $OUT (${#IMPORTS[@]} libSystem imports)"
