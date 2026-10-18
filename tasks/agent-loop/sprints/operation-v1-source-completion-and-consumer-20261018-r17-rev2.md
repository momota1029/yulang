# r17 revision 2 — licensed callback response through live resumption

Status: Luna-issued same-goal continuation; supersedes r17 revision 1 for new work without rewriting its evidence. Branch baseline last observed `2a3f2a47d5013761f0e0717b0c6073c54c62d36` (local `.git` read-only; origin confirmation unavailable). Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0.

## Why revision 2

Revision 1 design SHA-256 `47025832b8ebec78953649890b50e41972e6b210bb5753a2b941e3d82b442c9e` was reviewed BLOCKING: it used interface sketches instead of rules, selected a specimen without the exact `s1,j` field, and under-specified pending/divergent observations. Its source audit is frozen at `notes/theory/2026-10-18-operation-v1-source-completion-correspondence.md` SHA-256 `4147ee01443f8e89187d7fcd99d83865a1ee4458bc8146525989f6c48a01c524`, handoff `tasks/agent-loop/inbox/20261018-operation-v1-source-completion.md` SHA-256 `4ec480644768ec3dae0212543dd9f5c2aa42b0bcbd595c2ee24843f15b753196`. These are exact source/native-obstruction evidence, not a proof of a new rule. r16 rule SHA-256 `1004426d4afa990453d0addc8008f88327166862b63d311be8445eeb4218503d` remains the named v1 basis, subject to independent review of the revised producer/consumer.

The one vertical outcome is now: **a source-written callback at the exact positive nested result field is returned through a captured operation continuation, called after resumption, and its `outer::next()` request is consumed by the still-live outer handler; the same source evidence reaches a versioned v1 constraint consumer.**

Candidate exact source (not yet accepted or executed):

```yulang
act outer:
    our next: () -> int
act signal:
    our ping: () -> (int -> [outer] int)

my response (x:int): [outer] int = outer::next()
my result = catch (catch (signal::ping())(1) {
    signal::ping(), k -> k response,
    v -> v
}) {
    outer::next(), _ -> 42,
    v -> v
}
```

The exact `ping` row at `Operation.Function.ResultValue.Function.ResultEffect`, operand 0 is the v1 licensed field candidate. Existing code currently rejects its used negative callback port in both HIR preflight and candidate signature construction, then separately rejects Function responses before runtime continuation capture and at resume-type validation. Revision 2 must derive each repair, not delete these guards blindly. If this source is malformed or the field path differs, the proof lane must state the exact HIR/source correction before any semantic approval or code lease.

## Required design and proof

Luna owns `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r2.md`. It must state introduction/elimination rules (premises and conclusions), fixed source occurrence/field/license/development identity, negative concrete effect-row treatment, exact v1 consumer constraint, callback closure/carrier validation, actual source evaluation, and compatibility effects. It must prove no lower contribution is manufactured from an Allowance/Permission. It must state that Pending preserves event/history/live state and the ordered unprocessed `k >>= A_decl` suffix. A finite step-budget prefix is `Running`/`ResourceExhausted`, not semantic Diverged; no eventual return is inferred. Divergent histories remain as the original finite prefixes.

After Luna freezes design r2, Sol owns `notes/theory/2026-10-18-operation-v1-source-completion-correspondence-r2.md` and `tasks/agent-loop/inbox/20261018-operation-v1-source-completion-r2.md`. Prove the exact source -> typed field/license -> operation request -> captured continuation -> exact function response -> resumed saved suffix -> actual outer handler request -> v1 constraint consumer chain for the candidate source, or freeze the earliest exact failed premise. Preserve c and field identity across the chain. A concrete example closes no original universal condition; all W/Z, futures, G, F1/FK1, general Call, whole-use transport and soundness/principality remain explicit.

## Review gates and conditional implementation authority

Fresh independent semantic/spec review of the frozen design r2 and proof seam is required before code. After CLEAN/PASS, Luna may issue the following exact bounded code lease; this contract does not itself authorize writes:

- Solver: `crates/yu-solver/src/candidate_source.rs` (`preflight_catch_signature` path), `crates/yu-solver/src/candidate_effect.rs` (`candidate_catch_operation`, `candidate_signature_effect` exact negative concrete field path).
- Runtime: `tools/inference-playground/src/runtime/machine.rs` (`propagate_request`, `Frame::ResumeArgument`, typed response check), `tools/inference-playground/src/runtime/continuation.rs` (only if exact owner audit confirms a required change).
- Focused tests: existing `crates/yu-solver/tests/candidate_operation_catch.rs` and `tools/inference-playground/tests/runtime_resume.rs`; additions only, preserve existing expectations.
- `tools/inference-playground/src/lib.rs` and runtime `program.rs` are read-only during first lease. If wiring changes are required, freeze the reason and exact functions, then get a Luna follow-up lease before editing.

Feature-gate any new v1 behavior so default/old behavior remains separately observable. The complete test must pass through source parse/lowering, the ordinary candidate solve entry, runtime request, callback closure capture/response, resume, outer request handling and completed integer `42`; no test injects a response value, map, proof object or constraint. Add a negative control using a distinct same-family closure so execution must retain the actual response closure and its environment. Do not alter stable-core expected-output files without a separate `rules/testing.md` expected-output protection review. Independent compiler review checks HIR/source identity, variance/allowance, saved context, active-handler lifetime and v1 consumer before one focused runtime run.

Falsifiers: exact positive `s1,j` differs; actual response closure is replaced by another same-family closure; map/action is inferred from family or coordinates; handler response is not the callback passed by this source; saved suffix changes; outer request reaches a removed or wrong handler; or consumer uses an old Contrib/Inc/Cover/Permission cast.

## Budget and stop

Total r17 envelope remains 3,600 seconds; revision 1 proof reservation 1,200 seconds is charged and does not reset. Revision 1 spec review reserves/charges 360 seconds conservatively; actual elapsed for both is UNKNOWN. Remaining 2,040 seconds: Luna rule/source design 300, additional Sol correspondence 300, implementation 960, compiler review 360, focused runtime 60, integration/state 60. Astra 0. Do not start the code lease until review; keep counters honest. If implementation cannot fit, freeze the exact implementation and request an explicit additional envelope without claiming the vertical outcome.

Success is a real source-driven callback/resume/outer-handler execution and exact v1 consumer evidence. Runtime passage without the v1 proof consumer is an implementation partial only. Original parent closure stays 0 unless the unchanged full theorem is genuinely discharged for every original case/domain/quantifier. On closeout report original conditions actually closed, new implementation/test behavior, and the next single missing item.
