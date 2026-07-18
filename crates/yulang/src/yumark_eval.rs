//! Headless evaluation of isolated ordinary Yumark literals.

use std::fmt;

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
    UnexpectedRootCount { actual: usize },
    Runtime(evidence_vm::RuntimeEvidenceRunError),
    Output(evidence_vm::RuntimeEvidenceSingleStringError),
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
        }
    }
}

impl std::error::Error for YumarkLiteralEvaluationError {}

#[cfg(test)]
mod tests {
    use super::*;

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
}
