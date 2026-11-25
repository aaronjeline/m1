fn main() {
    // Relocatable install name for the macOS dylib (otherwise ld records the
    // absolute path of the build directory).
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!("cargo:rustc-cdylib-link-arg=-Wl,-install_name,@rpath/libcedar_check.dylib");
    }
}
