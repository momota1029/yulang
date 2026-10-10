#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn solve(text: &str) -> Result<CandidateInference, CandidateError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty(), "{text}");
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("formal-effect-polarity", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap());
    CandidateInference::solve(hir)
}

const EFFECTS: &str = "act io:\n    our tick: int -> ()\nact other:\n    our tick: int -> ()\n\n";

#[test]
fn double_argument_flip_admits_concrete_formal_rows() {
    for row in ["[io]", "[io, 'e]", "[]"] {
        let source = format!("{EFFECTS}my bridge (consume:(int -> {row} ()) -> ()) = consume; my first = bridge; my second = bridge");
        let candidate = solve(&source).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{row}");
    }
}

#[test]
fn closed_covariant_callback_accepts_its_operation_and_rejects_other_effects() {
    for (operation, accepted) in [("io", true), ("other", false)] {
        let source = format!("{EFFECTS}my bridge (consume:(int -> [io] ()) -> ()) = consume {operation}::tick; my provider callback = callback 1; my answer = bridge provider");
        let candidate = solve(&source).unwrap();
        assert_eq!(candidate.candidate_conflicts().is_empty(), accepted, "{operation}");
        if !accepted {
            assert!(candidate.candidate_conflicts().iter().any(|error| candidate.effect_conflict(error.kind()).is_ok()), "foreign concrete lower must retain an effect conflict");
        }
    }
}

#[test]
fn mixed_covariant_tail_accepts_unmatched_operation_lowers_after_fresh_uses() {
    let source = format!("{EFFECTS}my answer = {{ my bridge (consume:(int -> [io, 'e] ()) -> ()) = consume other::tick; my first = bridge; my second = bridge; my provider callback = callback 1; my ignored = first provider; second provider }}");
    let candidate = solve(&source).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
}

#[test]
fn omitted_and_symbolic_formal_effect_ports_keep_their_existing_behavior() {
    for row in ["", "['e]"] {
        let source = format!("{EFFECTS}my bridge (consume:(int -> {row} ()) -> ()) = consume other::tick; my provider callback = callback 1; my answer = bridge provider");
        assert!(solve(&source).unwrap().candidate_conflicts().is_empty(), "{row}");
    }
}

#[test]
fn positive_argument_effect_port_admits_a_concrete_row() {
    let source = format!("{EFFECTS}my bridge (consume:([io] int) -> ()) = consume");
    assert!(solve(&source).unwrap().candidate_conflicts().is_empty());
}

#[test]
fn negative_concrete_and_empty_formal_rows_still_reject_before_solving() {
    for ty in ["int -> [io] ()", "int -> [] ()", "(int -> ()) -> [io] ()", "[io] int", "((int -> [io] ()) -> ()) -> ()"] {
        let source = format!("{EFFECTS}my bridge (callback:{ty}) = callback");
        assert!(matches!(solve(&source), Err(CandidateError::Unsupported)), "{ty}");
    }
}
