use std::fs;
use std::path::PathBuf;

fn main() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("assets")
        .join("typed_act_templates.bin");
    let bytes = yulang::typed_act_bundle::generate_typed_act_template_bundle_bytes()
        .unwrap_or_else(|error| panic!("failed to generate typed act template bundle: {error}"));
    if std::env::args().any(|argument| argument == "--check") {
        let checked = fs::read(&path).unwrap_or_default();
        assert_eq!(bytes, checked, "{} is stale", path.display());
        return;
    }
    fs::create_dir_all(path.parent().expect("asset parent")).expect("create asset directory");
    fs::write(&path, bytes).expect("write typed act template bundle");
}
