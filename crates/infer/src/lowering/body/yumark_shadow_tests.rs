use super::*;

#[test]
fn yumark_nil_text_shadow_role_scans_stop_at_flat_format_selection() {
    let loaded = minimal_shadow_loaded(concat!(
        "use std::text::yumark::html_tag\n",
        "use std::text::yumark_algebra_shadow::*\n",
        "my empty = '[]\n",
        "my plain = '[hello world]\n",
        "html_tag (render_html_doc empty)\n",
        "render_markdown_doc empty\n",
        "html_tag (render_html_doc plain)\n",
        "render_markdown_doc plain\n",
    ));
    let output = crate::lowering::with_yumark_algebra_shadow_lowering(|| {
        lower_loaded_files(&loaded).expect("lower shadow source")
    });
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    // This source universe contains exactly one role, the two-candidate flat
    // YumarkAlgebraShadowFormat mapping. Any prerequisite scan would therefore
    // be recursive format evidence rather than unrelated stdlib traffic.
    let stats = output.timing.analysis;
    eprintln!(
        "Yumark nil/text shadow role scans: demands={} scans={} matches={} prerequisite_demands={} prerequisite_scans={} prerequisite_matches={}",
        stats.role_resolve_demands,
        stats.role_resolve_candidate_scans,
        stats.role_resolve_candidate_matches,
        stats.role_resolve_prerequisite_demands,
        stats.role_resolve_prerequisite_candidate_scans,
        stats.role_resolve_prerequisite_candidate_matches,
    );
    assert_eq!(stats.role_resolve_demands, 8);
    assert_eq!(stats.role_resolve_candidate_scans, 16);
    assert_eq!(stats.role_resolve_candidate_matches, 6);
    assert_eq!(stats.role_resolve_prerequisite_demands, 0);
    assert_eq!(stats.role_resolve_prerequisite_candidate_scans, 0);
    assert_eq!(stats.role_resolve_prerequisite_candidate_matches, 0);
}

fn minimal_shadow_loaded(root: &str) -> Vec<LoadedFile> {
    sources::load(vec![
        source_file(&[], root),
        source_file(&["std"], "pub mod text;\n"),
        source_file(
            &["std", "text"],
            concat!(
                "pub mod str;\n",
                "pub mod yumark;\n",
                "mod yumark_algebra_shadow;\n",
            ),
        ),
        source_file(
            &["std", "text", "str"],
            concat!(
                "pub type str\n",
                "pub concat(left: str, right: str): str = left\n",
            ),
        ),
        source_file(
            &["std", "text", "yumark"],
            concat!(
                "use std::text::str::str\n",
                "pub struct html_format { marker: str }\n",
                "pub struct markdown_format { marker: str }\n",
                "pub struct html_node { tag: str, body: str }\n",
                "pub html_format_value(): html_format = html_format { marker: \"html\" }\n",
                "pub markdown_format_value(): markdown_format = markdown_format { marker: \"markdown\" }\n",
                "pub html_tag(node: html_node): str = node.body\n",
            ),
        ),
        source_file(
            &["std", "text", "yumark_algebra_shadow"],
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../lib/std/text/yumark_algebra_shadow.yu"
            )),
        ),
    ])
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path {
            segments: path
                .iter()
                .map(|segment| sources::Name((*segment).to_string()))
                .collect(),
        },
        source: source.to_string(),
    }
}
