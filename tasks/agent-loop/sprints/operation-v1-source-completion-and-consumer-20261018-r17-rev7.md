# r17 revision 7 — source-linked FieldBound continuation argument

This revision preserves the r5 static Phase-S outcome and adds the exact source argument linkage required by the independent r5 spec review. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0 with unchanged quantifiers, source domain and semantics. The frozen r5 design and rev6 resource amendment remain immutable.

Frozen design: `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md` (SHA-256 recorded in current state after freeze). r5 review finding: a same-family callback with matching type/body could be selected without proving it was the argument supplied to the matched handler continuation.

## Exact outcome and constructor correction

For the fixed source specimen, construct `HandlerContinuationArgumentV1` from one exact retained local-source path: `u_ping` is in the scrutinee subtree of `u_catch`; the selected operation arm resolves to the same `decl`; its continuation binder has identity `k`; the retained `k response` Apply's callee resolves as `CatchBinder(k)`; the Apply's actual argument occurrence resolves to the exact `response_definition`; and that definition's body owns `u_outer`. `h_arg` is retained by `m0`, q and `FieldBoundV1`. No spelling/type/family equality substitutes for any edge. Changing the actual argument to `other_response` must change the linked definition or reject the record.

This is source-correspondence evidence for the static research constructor. It does not assert runtime request selection, does not enlarge/restrict the original parent theorem domain, and does not claim parent closure. Existing negative preflight, typed q-Allowance edge, ordinary drain, rollback, and no-cast requirements remain as frozen in r5/r6 design. Runtime Phase R remains out of scope.

## Budget and gates

The unchanged total cap is 4560s. Previously charged/reserved 3420s; 1140s remain, no reset, Astra 0. Allocate: source-linkage correction 120s (charged by this revision), independent focused delta review 180s, conditional solver code 420s, fresh independent compiler review 180s, one focused solver run plus integration/state 240s. Code remains unleased until CLEAN delta review. Failed review consumes no code allocation. No automatic renewal.

After CLEAN review, Luna/high may implement only the exact source-linked constructor/consumer in `crates/yu-solver/src/candidate_source.rs`, `candidate_effect.rs`, optional `shadow_apply.rs` only if the ordinary recipe is required, and additive `crates/yu-solver/tests/candidate_operation_catch.rs`. Other paths remain read-only absent a new exact lease. Then a fresh compiler referee reviews the frozen code/test diff before one focused solver test. A green test does not close the parent theorem or Phase R.

## Review contract

Read-only reviewer checks that every `h_arg` edge is grounded in the same retained source root and exact source/HIR identities; matching is by resolved operation declaration and lexical continuation binder ID; the Apply argument is the actual child at that application; unrelated same-family definitions cannot enter `m0` or FieldBound; the exact `h_arg` reaches q and the FieldBound consumer; all previous r5 constraints remain satisfied; and absence/ambiguity refuses the provisional constructor without changing legacy behavior. Falsifier: replace only `response` by `other_response`; if the old definition still populates the same record, BLOCKING. No tests, edits or Git by the reviewer.

## Parent and stop condition

The r5 review result closes no original condition (0 → 0). Parent remains OPEN / closure 0. Next seam after a CLEAN delta review and static implementation is whether the source-linked record is emitted by the actual collector and survives typed propagation/drain. Do not promote a design, conditional constructor, or passing test to theorem or production status.
