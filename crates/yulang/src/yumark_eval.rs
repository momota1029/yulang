//! Headless evaluation of isolated ordinary Yumark literals.

use std::fmt;

/// Render each owned doc-comment unit independently, then concatenate bytes.
///
/// Units without a sound ordinary-literal mapping carry their existing static
/// rendering as a per-unit fallback. Other units use the warm evaluator below.
pub fn evaluate_doc_comment_render_input_markdown_with_embedded_std(
    input: &infer::doc_comment_render_input::DocCommentRenderInput,
) -> Result<String, YumarkLiteralEvaluationError> {
    let mut rendered = String::new();
    for unit in input.units() {
        match unit.to_synthetic_yumark_literal() {
            Ok(literal) => {
                let unit_rendered = evaluate_yumark_literal_markdown_with_embedded_std(&literal)?;
                let suffix = unit
                    .rendered_markdown_suffix_to_trim()
                    .expect("constructed literals have a rendered-boundary mapping");
                let normalized = unit_rendered.strip_suffix(suffix).ok_or_else(|| {
                    YumarkLiteralEvaluationError::UnexpectedRenderedBoundary {
                        expected_suffix: suffix,
                        actual: unit_rendered.clone(),
                    }
                })?;
                rendered.push_str(normalized);
            }
            Err(_) => rendered.push_str(
                unit.static_fallback_markdown()
                    .expect("mapping failures carry their static per-unit fallback"),
            ),
        }
    }
    Ok(rendered)
}

/// Render one ordinary Yumark literal through the bundled standard library.
///
/// The embedded-std source route keeps its compiled prefix warm per thread;
/// only the synthetic root containing `literal` is lowered for each call.
/// Native host operations stay disabled because doc rendering is pure.
pub fn evaluate_yumark_literal_markdown_with_embedded_std(
    literal: &str,
) -> Result<String, YumarkLiteralEvaluationError> {
    let build = compile_yumark_literal_markdown_with_embedded_std(literal)?;
    run_compiled_yumark_literal(build)
}

fn compile_yumark_literal_markdown_with_embedded_std(
    literal: &str,
) -> Result<crate::source::BuildControlOutput, YumarkLiteralEvaluationError> {
    let source = format!("std::text::yumark::render_markdown_doc ({literal})\n");
    let mut poly =
        crate::source::build_poly_from_source_text_with_embedded_std("<lazy-yumark-eval>", source)
            .map_err(YumarkLiteralEvaluationError::Compilation)?;
    // The warm prefix carries whole-program computed roots. Keep its arena as
    // the dependency environment, but specialize only the fresh expression
    // root so evaluation cannot eagerly run unrelated std initialization.
    poly.arena
        .runtime_roots
        .retain(|root| matches!(root, poly::expr::RuntimeRoot::Expr(_)));
    let root_count = poly.arena.runtime_roots.len();
    if root_count != 1 {
        return Err(YumarkLiteralEvaluationError::UnexpectedRootCount { actual: root_count });
    }
    crate::source::build_control_from_poly_output(&poly)
        .map_err(YumarkLiteralEvaluationError::Compilation)
}

fn run_compiled_yumark_literal(
    build: crate::source::BuildControlOutput,
) -> Result<String, YumarkLiteralEvaluationError> {
    let root_count = build.program.roots.len();
    if root_count != 1 {
        return Err(YumarkLiteralEvaluationError::UnexpectedRootCount { actual: root_count });
    }

    let plan = evidence_vm::build_plan(&build.program, &build.runtime_evidence);
    let output =
        evidence_vm::run_program_with_plan_without_native_host_operations(&build.program, &plan)
            .map_err(YumarkLiteralEvaluationError::Runtime)?;
    output
        .single_string_value()
        .map(str::to_owned)
        .map_err(YumarkLiteralEvaluationError::Output)
}

#[derive(Debug)]
pub enum YumarkLiteralEvaluationError {
    Compilation(crate::source::RouteError),
    UnexpectedRootCount {
        actual: usize,
    },
    Runtime(evidence_vm::RuntimeEvidenceRunError),
    Output(evidence_vm::RuntimeEvidenceSingleStringError),
    UnexpectedRenderedBoundary {
        expected_suffix: &'static str,
        actual: String,
    },
}

impl fmt::Display for YumarkLiteralEvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compilation(error) => write!(f, "failed to compile Yumark literal: {error}"),
            Self::UnexpectedRootCount { actual } => {
                write!(f, "expected one Yumark evaluation root, got {actual}")
            }
            Self::Runtime(error) => write!(f, "failed to evaluate Yumark literal: {error}"),
            Self::Output(error) => write!(f, "failed to extract Yumark output: {error}"),
            Self::UnexpectedRenderedBoundary {
                expected_suffix,
                actual,
            } => write!(
                f,
                "expected rendered Yumark boundary {expected_suffix:?}, got {actual:?}"
            ),
        }
    }
}

impl std::error::Error for YumarkLiteralEvaluationError {}

#[cfg(test)]
mod tests {
    use super::*;

    use infer::doc_comment_render_input::{DocCommentRenderInput, DocUnitLiteralMappingError};

    #[test]
    fn warm_embedded_std_evaluator_runs_one_ordinary_yumark_literal() {
        let rendered = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let build =
                    compile_yumark_literal_markdown_with_embedded_std("'{Hello *Yumark*.\n}")
                        .expect("compile one Yumark literal");
                assert_eq!(
                    build.program.roots.len(),
                    1,
                    "compiled roots: {:#?}",
                    build.program.roots
                );
                run_compiled_yumark_literal(build).expect("run one Yumark literal")
            })
            .expect("spawn Yumark evaluator test thread")
            .join()
            .expect("Yumark evaluator test thread");

        assert_eq!(rendered, "Hello *Yumark*.\n\n");
    }

    #[test]
    fn characterizes_current_visible_ordinary_blank_line_operation() {
        let (continued, separated) = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let continued =
                    evaluate_yumark_literal_markdown_with_embedded_std("'{first\nsecond\n}")
                        .expect("evaluate continued paragraph");
                let separated =
                    evaluate_yumark_literal_markdown_with_embedded_std("'{first\n\nsecond\n}")
                        .expect("evaluate blank-line-separated paragraphs");
                (continued, separated)
            })
            .expect("spawn Yumark evaluator test thread")
            .join()
            .expect("Yumark evaluator test thread");

        assert_eq!(continued, "first\nsecond\n\n");
        assert_eq!(separated, "first\n\n\n\n\nsecond\n\n");
    }

    #[test]
    fn per_unit_lazy_doc_render_matches_static_renderer_bytes() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let cases = [
                    ("paragraph", "-- paragraph\nmy x = 1\n"),
                    ("stacked units", "-- first\n-- second\nmy x = 1\n"),
                    ("multi-line paragraph", "---\nalpha\nbeta\n---\nmy x = 1\n"),
                    ("heading", "---\n## Heading\n---\nmy x = 1\n"),
                    ("list", "---\n- first\n- second\n---\nmy x = 1\n"),
                    ("fence", "---\n```text\nalpha\nbeta\n```\n---\nmy x = 1\n"),
                    ("quote", "---\n> quoted\n---\nmy x = 1\n"),
                    ("CRLF", "---\r\nalpha\r\nbeta\r\n---\r\nmy x = 1\r\n"),
                    (
                        "boundary whitespace",
                        "--  leading and trailing  \nmy x = 1\n",
                    ),
                    ("empty unit", "--\nmy x = 1\n"),
                    ("terminal blank line", "---\nalpha\n\n---\nmy x = 1\n"),
                    ("mixed fallback", "--\n-- paragraph\nmy x = 1\n"),
                ];

                for (name, source) in cases {
                    let (input, expected) = doc_render_case(source);
                    let actual =
                        evaluate_doc_comment_render_input_markdown_with_embedded_std(&input)
                            .unwrap_or_else(|error| panic!("{name}: {error}"));
                    assert_eq!(actual, expected, "{name}");
                }

                let (mixed, _) = doc_render_case("--\n-- paragraph\nmy x = 1\n");
                assert_eq!(
                    mixed.units()[0].to_synthetic_yumark_literal(),
                    Err(DocUnitLiteralMappingError::EmptyOrBoundaryOnlyUnit)
                );
                assert_eq!(mixed.units()[0].static_fallback_markdown(), Some("--"));
                assert!(mixed.units()[1].to_synthetic_yumark_literal().is_ok());
                assert!(mixed.units()[1].static_fallback_markdown().is_none());
            })
            .expect("spawn per-unit doc renderer test thread")
            .join()
            .expect("per-unit doc renderer test thread");
    }

    fn doc_render_case(source: &str) -> (DocCommentRenderInput, String) {
        let loaded = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let lower = infer::lowering::lower_loaded_files(&loaded).expect("lower doc fixture");
        let root = lower.modules.root_id();
        let def = lower.modules.value_decls(root, &sources::Name("x".into()))[0].def;
        let doc = lower
            .modules
            .def_doc_comment(def)
            .expect("doc comment should attach to x");
        assert!(infer::doc_comment_render::doc_comment_is_safe_for_yumark_literal_reparse(doc));
        let expected = infer::doc_comment_render::render_doc_comment_markdown(doc);
        let input = DocCommentRenderInput::from_safe_doc_comment(doc);
        (input, expected)
    }
}
