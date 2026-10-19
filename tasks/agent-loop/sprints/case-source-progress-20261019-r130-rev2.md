# R130 rev2 — case source progress and correspondence

Revision 2 preserves rev1 SHA-256
`c0c17c1a5e6c7c21e14b0b0f336b92d927baf94c2b2ec069546bd099e1516d6d`.
Rev1 pre-spec review found two major findings: an unleased optional browser
output and conflicting implementation/final-verification sequencing. This
revision removes browser edits and assigns all verification to the final gate.

Status: CANDIDATE rev2; read-only delta pre-spec review only. No proof or implementation
lease exists until a CLEAN review and Luna's explicit grant. This packet is a
finite, provisional source-slice repair; it does not change production compiler
semantics or close any theorem/adoption gate.

Branch `research/simple-sub-intrusion`; baseline `1f44d6087d696a2bf436c18cbb6c7446af9fa6f1`.

## Fixed outcome

Establish whether the experimental integer/binder/wildcard `case` path has two
source-accounting defects, repair each confirmed defect, and carry a minimal
ordinary case through source construction, candidate inference and the public
CLI evaluator. Existing WebAssembly case examples remain unchanged; this packet
does not edit browser files. Keep all changes inside the experimental
candidate/playground path.

The exact probe source is:

```yu
my main = case 7: unused -> 11
```

Expected result under the existing experimental evaluator is `11`. The binder
is intentionally unused. A second witness nests a case body and checks that
each retained LocalSource expression is processed once by the candidate
worklist; this is a source/worklist invariant, not a new language rule.

## Decisive premises and falsifiers

1. `LocalSourceForm::Case` visitation currently schedules every arm body in
   `Work::Visit`, then `Work::CaseArms` schedules the same bodies again. Confirm
   actual LIFO order, including nested cases and integer patterns, before
   changing it. Falsifier: a complete worklist trace shows each body is
   scheduled only once or one route is unreachable.
2. `case_positions` is populated only from resolved `CaseBinder` Name
   occurrences, while `Work::CaseArms` currently requires an entry for every
   binder. Confirm with the pinned constructors and consumer. Falsifier: an
   unused binder receives a valid position elsewhere or the branch is not
   reached for the exact witness.
3. Preserve arm-local binding to the scrutinee endpoint, per-arm value/effect
   constraints, source-order runtime selection, and wildcard behavior. No
   shared mutable visitor state or recursive traversal is introduced.

## Proof lane — 480 seconds, Sol/high

Construct a finite source/worklist argument for the exact case carrier and its
nested case extension: follow `LocalSourceBuilder::case` and `Work::CaseArm`,
the retained `LocalSourceForm::Case` indexes and binder IDs, then the candidate
worklist's `Work::Visit` / `Work::CaseArms` scheduling, endpoint lookup and
`Finish` constraint generation. Establish the actual old defect(s), the
repaired one-visit schedule, the unused-binder case, and preservation of every
arm body's value/effect constraints. Trace selected-arm evaluation to the
original scrutinee value in the provisional machine. Apply only to the
experimental source/evaluator correspondence; explicitly leave Simple-sub and
evaluator A/B, R85 adoption, all six effect-hygiene parents, and broad case
completeness OPEN.

Outputs: `notes/theory/2026-10-19-r130-case-source-progress.md` and
`tasks/agent-loop/inbox/20261019-r130-proof.md`. No production edits, semantic
decisions, test expectation changes, or independent certification.

## Implementation lane — Luna/high, 360 seconds

After proof of the two local source facts (or Luna adjudication if only one is
confirmed), repair only `crates/yu-solver/src/candidate_source.rs` and add one
focused public CLI regression in
`tools/inference-playground/tests/cli_case_source_progress.rs`. Cover the exact
unused-binder witness and one nested case whose selected body returns the
original value. Preserve existing case examples and outputs. The implementation
lane performs no test/build/formatter/CLI checks; verification belongs only to
the final gate after both lanes stop and all three independent reviews are
CLEAN.

No edits to stable syntax, production inference, evaluator policy, fixtures,
expected outputs, design authority, or Yulang2. If the proposed fix requires a
new typing/semantic rule, stop and return the exact choice to Luna.

## Pinned inputs at baseline `1f44d6087d696a2bf436c18cbb6c7446af9fa6f1`

| Input | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `1c758cf1bff9eb2b304107f1511bcac442e9b09a165d57ba142888b50ca0365f` |
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `tools/inference-playground/tests/cli_resumed_receiver_permission.rs` | `9a5fd48d1f89ae064960554d8ece36d6b9b437ae6cc91504a1e7c035aec9257a` |
| `web/playground/smoke-test.mjs` | `67d498313fdab02cb1689d4a9a5bde44ce46cae1d8938f133a7d25f65cfe602e` |
| `notes/progress/2026-10-19-case-pattern-playground.md` | `ef7096cb074fd4ad23cacf110fab1e3daddf34c8ad643b29a564d617936275cd` |
| `notes/progress/2026-10-19-r129-resumed-receiver-cli.md` | `283a5a27d3794588c08996f7b9f30fa822daca3e216e80fafd679546a4a7ea47` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |

## Review, resources and gates

The pre-spec reviewer has read-only access to this rev2 contract and pinned
inputs; max 60 seconds. No producer, test, formatter, build or CLI run starts
before CLEAN review and Luna's lane grant. Sprint cap: 1,560 seconds; 180
inventory, 240 pre-spec, 480 proof, 360 implementation, 180 final review, 60
verification, 60 closeout. One heavy process at a time; no Astra assignment.
Preserve all inherited UNKNOWN identities, reservations and quarantined paths.
After both lanes stop, freeze outputs for fresh independent compiler/source,
spec/authority and regression review. Only after all three are CLEAN, Luna runs
exactly `cargo test -p yu-playground --test cli_case_source_progress -- --exact
case_binder_may_be_unused_and_nested_case_body_is_processed_once`. This is the
single verification command; it compiles the owning package. No separate
package check or browser smoke is authorized. Luna alone integrates, reviews
the full outbound range, commits and pushes non-forcibly.

The candidate result can establish at most a finite experimental
source/inference/evaluator correspondence. It cannot prove arbitrary cases,
Simple-sub soundness/principality, evaluator A/B, semantic adoption or
production admission.
