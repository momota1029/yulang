use super::*;

#[test]
fn yumark_full_static_role_scans_stop_at_flat_format_selection() {
    let plain = minimal_yumark_loaded(concat!(
        "use std::text::yumark::*\n",
        "my plain = '[hello world]\n",
        "html_tag (render_html_doc plain)\n",
        "render_markdown_doc plain\n",
    ));
    let plain = lower_loaded_files(&plain).expect("lower plain Yumark source");
    assert!(plain.errors.is_empty(), "{:?}", plain.errors);

    let rich = minimal_yumark_loaded(concat!(
        "use std::text::yumark::*\n",
        "my rich = '{## Static vocabulary\n",
        "Paragraph with *emphasis* and **strong**.\n",
        "\n",
        "#.\n",
        "- bullet *item*\n",
        "1. numbered **item**\n",
        "```text\n",
        "line one\n",
        "line two\n",
        "```\n",
        "> quoted\n",
        "}\n",
        "html_tag (render_html_doc rich)\n",
        "render_markdown_doc rich\n",
    ));
    let rich = lower_loaded_files(&rich).expect("lower rich Yumark source");
    assert!(rich.errors.is_empty(), "{:?}", rich.errors);

    // This source universe contains exactly one role, the two-candidate flat
    // YumarkFormat mapping. Any prerequisite scan would therefore
    // be recursive format evidence rather than unrelated stdlib traffic.
    let plain_stats = plain.timing.analysis;
    let rich_stats = rich.timing.analysis;
    eprintln!(
        "Yumark role scans: plain demands/scans/matches={}/{}/{} prerequisite={}/{}/{}; rich demands/scans/matches={}/{}/{} prerequisite={}/{}/{}",
        plain_stats.role_resolve_demands,
        plain_stats.role_resolve_candidate_scans,
        plain_stats.role_resolve_candidate_matches,
        plain_stats.role_resolve_prerequisite_demands,
        plain_stats.role_resolve_prerequisite_candidate_scans,
        plain_stats.role_resolve_prerequisite_candidate_matches,
        rich_stats.role_resolve_demands,
        rich_stats.role_resolve_candidate_scans,
        rich_stats.role_resolve_candidate_matches,
        rich_stats.role_resolve_prerequisite_demands,
        rich_stats.role_resolve_prerequisite_candidate_scans,
        rich_stats.role_resolve_prerequisite_candidate_matches,
    );
    assert_eq!(
        rich_stats.role_resolve_demands,
        plain_stats.role_resolve_demands
    );
    assert_eq!(
        rich_stats.role_resolve_candidate_scans,
        plain_stats.role_resolve_candidate_scans
    );
    assert_eq!(
        rich_stats.role_resolve_candidate_matches,
        plain_stats.role_resolve_candidate_matches
    );
    assert_eq!(plain_stats.role_resolve_prerequisite_demands, 0);
    assert_eq!(plain_stats.role_resolve_prerequisite_candidate_scans, 0);
    assert_eq!(plain_stats.role_resolve_prerequisite_candidate_matches, 0);
    assert_eq!(rich_stats.role_resolve_prerequisite_demands, 0);
    assert_eq!(rich_stats.role_resolve_prerequisite_candidate_scans, 0);
    assert_eq!(rich_stats.role_resolve_prerequisite_candidate_matches, 0);
}

fn minimal_yumark_loaded(root: &str) -> Vec<LoadedFile> {
    sources::load(vec![
        source_file(&[], root),
        source_file(
            &["std"],
            "pub mod core;\npub mod text;\npub mod int;\npub mod control;\n",
        ),
        source_file(&["std", "core"], "pub mod cmp;\npub mod ops;\n"),
        source_file(
            &["std", "core", "cmp"],
            concat!(
                "use std::text::str::str\n",
                "pub role Eq 'a:\n",
                "  pub a.eq: 'a -> bool\n",
                "impl str: Eq:\n",
                "  our x.eq y = std::text::str::eq x y\n",
            ),
        ),
        source_file(
            &["std", "core", "ops"],
            concat!(
                "use std::core::cmp::*\n",
                "pub infix (==) 3.0.0 3.0.1 = \\x -> \\y -> x.eq y\n",
            ),
        ),
        source_file(
            &["std", "int"],
            concat!(
                "use std::text::str::str\n",
                "pub to_string(value: int): str = \"\"\n",
            ),
        ),
        source_file(&["std", "control"], "pub mod junction;\n"),
        source_file(&["std", "control", "junction"], "pub mod junction;\n"),
        source_file(
            &["std", "control", "junction", "junction"],
            "pub junction value = value\n",
        ),
        source_file(
            &["std", "text"],
            concat!("pub mod str;\n", "pub mod yumark;\n",),
        ),
        source_file(
            &["std", "text", "str"],
            concat!(
                "pub type str\n",
                "pub concat(left: str, right: str): str = left\n",
                "pub eq(left: str, right: str): bool = true\n",
            ),
        ),
        source_file(
            &["std", "text", "yumark"],
            &format!(
                "use std::core::ops::*\n{}",
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../../lib/std/text/yumark.yu"
                ))
            ),
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
