# R186 Option B sequence-slice implementation contract

Status: design frozen for prospective review; code lease is not yet active.

Sprint: `source-emission-and-option-b-stage1-20261021-r186`
Contract SHA-256: `41d2241083e3443918b730cd457428d5128b5abe73896e0ed23aae17390664d3`
Baseline: `ef15618375343b5bfef0ba4aa3a7fbfbe5606d74`
Design source ceiling: the exact 50 committed blob/mode pins in the sprint contract.

## User-visible slice

Implement the ordinary non-record braced expression sequence in a braced `if` arm. Each item runs once, in source order. Intermediate values are discarded and the last item supplies the arm value. Its type is the last expression's value type; its computation effect includes the effects of every item, in order. Preserve sequencing state while a selected expression suspends and resumes. A braced `if` without `else` still evaluates its selected body and has Unit result. Preserve the existing colon/indented/inline arm behavior and existing Web fixture bytes and expected `countdown_result -> 8`.

This slice does not define record-shaped `{}`, `{field: value}`, or `{...spread}` meanings, duplicate field policy, spread precedence, missing-field lookup, record rendering, or mixed record/non-record spread. Those forms remain explicitly unsupported/deferred according to the provisionally adopted R147 packet; do not reinterpret them as sequences. Malformed syntax remains recoverable and must not produce a partially executable sequence.

## Source-to-runtime contract

1. **Parser ownership.** `if_nud_normalized` / `if_arm_normalized` in `yu-syntax/expression/if_expr.rs` own arm boundaries and keyword/colon compatibility. `inline_body_normalized` and `with_body` own inline/braced body admission. `DelimitedOwner` and `SequenceOwner::If` in `expression/delimited.rs` / `sequence.rs` distinguish the conditional body from ordinary record literals. The sequence parser must retain each expression node in lexical order, delimit the closing brace and `elsif`/`else` correctly, and leave existing expression-list recovery and expected token ownership intact. No AST-level filtering may drop an item.
2. **Retained HIR.** `yu-hir/module/local_source.rs::conditional` currently lowers each `IfArm` to one condition index and one body index and accepts only `OperatorChain` or `IndentedStatementBlock`. Extend the retained local-source form so the braced sequence has a stable owner occurrence and ordered direct child indices. Every child has its own source key and occurrence; the parent is not conflated with any child. Preserve existing single-expression and indented-body forms and the no-else `None` representation. A malformed/record-shaped body returns the existing unsupported/availability path without publishing partial source identities. Update `yu-hir` exports/source identity only as needed for the new form.
3. **Inference.** `candidate_value_graph.rs` must connect the sequence result to its final child and preserve the source-qualified child graph. `candidate_source.rs` schedules each direct child exactly once in source order. Each child receives normal value checking and contributes its computation effect; the sequence's value endpoint is the final child's value endpoint. A conditional with `else` joins arm result values as before. Without `else`, branch bodies are still checked and their effects retained, while the conditional value remains Unit. Keep condition checks and existing per-occurrence value/effect slots distinct; no parent/child occurrence aliasing. Preserve SCC/use routing and rollback guarantees.
4. **Evaluator.** `runtime/program.rs` lowers the retained sequence into ordered child code and an explicit final-result rule. `runtime/machine.rs` runs children left to right, discards intermediate values, returns only the last child's received value, and selects exactly one arm after the condition. The sequence continuation frame must survive operation handling/resumption through the existing continuation/receiving protocol (`continuation.rs`, `receiving.rs`); it must not re-run a completed child or skip the remaining suffix. No-else evaluation executes the body then returns Unit. Preserve the pinned `primitive.rs` universal closed/ground certificate: certification is permitted only when every retained definition, every arm (including arms not selected by this execution), every dependency, and every child of each sequence is covered. If any retained object is outside coverage, the primitive path must decline the optimization. Never narrow this condition to the selected runtime path.
5. **Web integration.** The unchanged ordinary-islands fixture goes through the existing Web compile/evaluate path in `web/playground/src/main.ts`; preserve output rendering and existing smoke expectations. Do not edit the fixture. Add a CLI integration test that exercises ordered side effects, last-value return, a suspending/resuming child with a remaining suffix, `elsif` selection, and no-else Unit. Web smoke coverage must continue to assert the unchanged countdown result.

## Exact conditional code and test paths

Only these paths are candidates for the code lease, and only the subset justified by the implementation may be activated:

- `crates/yu-syntax/src/expression/if_expr.rs`
- `crates/yu-syntax/src/expression/mod.rs`
- `crates/yu-syntax/src/expression/delimited.rs`
- `crates/yu-syntax/src/syntax_kind.rs`
- `crates/yu-syntax/src/sequence.rs`
- `crates/yu-syntax/src/expression/tails/with_body.rs`
- `crates/yu-syntax/src/tests/if_expr.rs`
- `crates/yu-syntax/src/tests/delimited_recovery.rs`
- `crates/yu-syntax/src/tests/expression_recovery.rs`
- `crates/yu-syntax/src/tests/braced_statement_recovery.rs`
- `crates/yu-syntax/src/tests/rule_expression_list_recovery.rs`
- `crates/yu-hir/src/lib.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/source_identity.rs`
- `crates/yu-hir/tests/conditional_local_source.rs`
- `crates/yu-solver/src/candidate_value_graph.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/tests/ordinary_expression_source.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/primitive.rs`
- `tools/inference-playground/src/runtime/continuation.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/tests/cli_ordinary_islands.rs` (new)
- `web/playground/src/main.ts`
- `web/playground/smoke-test.mjs`

The fixture and `tools/inference-playground/src/lib.rs` are not write paths. The dirty solver files `candidate_context.rs`, `candidate_scheme.rs`, `lib.rs`, and `shadow_apply.rs` are excluded byte-for-byte. If implementation requires any excluded path or another source owner, stop before editing and request a sequential exact-path contract revision and fresh review. Do not read dirty working-tree versions; use the pinned committed baseline.

## Focused evidence after code activation

Run only the focused parser/HIR/solver/CLI/Web checks listed by the sprint contract. Required evidence: valid sequence child order and unique occurrences; malformed/recovery parity; final-value and cumulative-effect constraints including no-else Unit; exact-once execution with suspend/resume and continuation suffix preservation; unchanged fixture SHA and `countdown_result -> 8`; all pre-existing targeted expectations. Do not change expected outputs to obtain a pass. No check, build, sample execution, or test is authorized before code activation.

## Review finding and activation status

The first prospective contract review (about 110/120 seconds charged) found that the initial wording “every selected child” could weaken the pinned primitive certificate, which covers all constructed definitions, arms, and dependencies including unused code. This revision states the universal retained-object condition explicitly. It has not received a fresh review under the R186 review budget; therefore this revision grants no code authority and requires a separately budgeted independent prospective review before activation.

## Open boundaries

This is a staged, reviewable implementation increment, not closure of `R183-FRONTIER-COVERAGE-1`, the original A/B/source-native theorem, or production approval. The R186 proof lane remains independent. A proof result cannot self-review. Record representation questions stay open. Any source path/consumer missing from the 50-pin map blocks activation until the exact manifest and contract are revised and independently reviewed.
