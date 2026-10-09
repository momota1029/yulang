# Symbolic effect tails on formal Function annotations

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `e62a4a07f`
Status: bounded private implementation verified; independent compiler-referee delta review clean
Authority: selected annotation-variable flow policy and paired Function formal construction gate
Scope: singleton variable-only effect tails on formal Function annotations
Measurement: zero timing samples and benchmark processes

## Behavior

Formal Function annotations can now use a singleton symbolic effect tail such as
`int -> ['e] int`. It is an ordinary effect row, shared by name across formal
ports and the whole-binding annotation in the same definition scope. Local
binding scopes remain separate, and each use freshens local effect rows as
before. Existing paired positive/negative Function ports consume the shared
row; omitted ports keep their independent rows.

This applies the selected rule that an annotation variable is not a concrete
annotation atom without severing its row connection. Later concrete lowers
still reach the shared effect fiber and are checked by existing propagation.
Formal concrete rows and closed `[]` rows remain explicitly unsupported. No
attachment identity, contextual PUSH/POP, subtraction filter, or new row-global
permission is introduced by this slice.

## Ownership and review

The source formal preflight admits only singleton variable-only tails. The
candidate constructor maps effect names separately from value names, keyed by
the actual definition/local annotation scope. Whole-definition annotation
tails consult the same definition-scoped map; operation-signature variables
retain their operation-local map. New keys and owned names participate in
route rollback, retained/undo accounting, and peak sampling.

The initial independent compiler-referee review found that formal and
whole-definition annotation tails were held in separate maps. The repair shares
the definition-scoped map and adds a source case whose body returns an unrelated
pure callback, then verifies a late concrete lower reaches the returned
Function's captured effect fiber. A second regression verifies a failed
whole-annotation route restores the preexisting formal tail. The independent
delta review closed the major finding and found no new blocking or major issue.

## Verification

All Cargo commands ran serially, offline, with two build jobs and one test
thread; `RUSTC_WRAPPER=` bypassed the configured sccache permission failure.

- `RUSTC_WRAPPER= timeout 120s cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib formal_and_whole_annotation -j 2 --offline -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= timeout 120s cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib formal -j 2 --offline -- --test-threads=1` — 9 passed.
- `RUSTC_WRAPPER= timeout 120s cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_annotated_function_formals -j 2 --offline -- --test-threads=1` — 10 passed.
- `git diff --check -- crates/yu-solver/src/candidate_effect.rs crates/yu-solver/src/candidate_source.rs crates/yu-solver/tests/candidate_annotated_function_formals.rs` — passed.

The independent review covered the scoped map, definition/local separation,
operation-map preservation, late concrete flow, capture, and rollback. Default
feature builds, broader suites, concrete formal annotation hygiene, the user's
`[io]` callback target, complete Call, public owned schemes, default migration,
and F5 replacement remain open. This is a source-inference slice, not completion
of contravariant concrete subtraction.
