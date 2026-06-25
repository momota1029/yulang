use std::env;
use std::fs;
use std::path::PathBuf;

const PLAYGROUND_STD_ARTIFACT_ENTRY: &str = "<embedded-playground-std-root>";

fn main() {
    track_inputs();
    if let Err(error) = write_embedded_playground_std_artifact() {
        panic!("failed to build embedded playground std artifact: {error}");
    }
}

fn track_inputs() {
    println!("cargo:rerun-if-changed=../yulang/src/playground_std.rs");
    println!("cargo:rerun-if-changed=../yulang/src/source/std_sources.rs");
    println!("cargo:rerun-if-changed=../yulang/src/cache.rs");
    for file in yulang::stdlib::embedded_std_files() {
        println!("cargo:rerun-if-changed=../../lib/{}", file.relative_path);
    }
}

fn write_embedded_playground_std_artifact() -> Result<(), String> {
    let files = yulang::collect_source_text_with_embedded_playground_std(
        PLAYGROUND_STD_ARTIFACT_ENTRY,
        String::new(),
    )
    .map_err(|error| error.to_string())?;
    let loaded = yulang::load_source_text_with_embedded_playground_std(
        PLAYGROUND_STD_ARTIFACT_ENTRY,
        String::new(),
    )
    .map_err(|error| error.to_string())?;
    let key = yulang::cache::source_cache_key(&files);
    let artifact =
        yulang::cache::compiled_unit_artifact_from_loaded_files_with_key(&files, &loaded, key)
            .map_err(|error| error.to_string())?;
    if !artifact.errors.is_empty() {
        return Err(format!(
            "embedded playground std artifact has lowering errors: {:?}",
            artifact.errors
        ));
    }

    let bytes = yulang::cache::encode_compiled_unit_artifact_bytes(&artifact)
        .map_err(|error| error.to_string())?;
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").ok_or("OUT_DIR is not set")?);
    fs::write(out_dir.join("embedded_playground_std.yuunit"), bytes)
        .map_err(|error| error.to_string())
}
