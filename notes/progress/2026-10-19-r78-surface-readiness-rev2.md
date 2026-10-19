# R78 method/role surface readiness — revision 2

Status: decision-ready draft pending fresh independent delta reviews; no implementation or semantic approval  
Contract: `tasks/agent-loop/sprints/effect-hygiene-executable-method-role-20261019-r78-rev2.md`, SHA-256 `5a5cca3b708b0d79b56fc0d0b48c37f4226365d53f7159eb31c1b667881323b6`  
Design: `notes/design/2026-10-19-r78-executable-method-role-pilot-rev2.md`

## What is now concrete

The design gives exact source and expected proposed outcome for unique resolution, missing target, ambiguity across roles, callable-field collision, effectful receiver and argument, computation-annotated formal retention, outward method-body request, malformed syntax, unsupported-but-valid syntax and an unvalidated implementation. It separates three outcomes: language diagnostics for malformed/ambiguous/missing/type-invalid source; valid draft execution behavior; and provisional playground admission refusal for valid syntax the runtime cannot yet execute.

The Value/Computation entry account follows charter §21. The method receiver is the first ordinary formal. Value receiver/argument computations are constructed inertly, then each is forced/rebound once at its receiving activation; an explicit Computation formal retains its carrier. Lookup never eagerly executes a method body. Effect requests must continue through the ordinary selected-handler path, and an unhandled method request remains outward. The proof certificate is supporting conditional evidence only; static `K,D`, residual type, continuation resumption, foreign continuation and universal hygiene are OPEN.

The path names each absent owner: declaration/member identity and admission; role signature and impl body validation; member source root/environment; unique source-qualified selection; ordinary Apply elaboration/provenance; candidate preflight in `candidate_source.rs`; and validated declaration metadata in `RuntimeProgram`. The current exception for effect-declaration placeholders is explicitly not treated as role/impl admission.

## Readiness gates

| Gate | State | Evidence / next obligation |
|---|---|---|
| Surface syntax nodes | Existing but semantically inert | `FieldTail`, role and impl parser-node correspondence exists; no dispatch law follows. |
| Role/impl declaration semantics | Draft only | User decision required for role meaning, `ImplDescription`, member identity, validation and diagnostics. |
| Ordinary call typing | OPEN | Preserve original ordinary Call source formation and proof obligations; generated Apply is not a typing rule. |
| Candidate admission | Missing owner path | Define all-or-nothing validated declaration metadata at `candidate_source.rs`; provisional refusal stays distinct from a language error. |
| Runtime materialization | Missing owner path | Carry validated members, roots and declaration-qualified callee identity into `RuntimeProgram`; ensure ordinary handlers retain outward requests. |
| Method source/native correspondence | OPEN | Join original FieldTail and generated application through both directions with source provenance. |
| Effect hygiene | Conditional partial evidence | R78 certificate remains OPEN at source projection and does not close native or universal obligations. |
| Runnable surface | Next contract after decision | First useful vertical slice: `1.second(2)` → `2`, followed by order, retention, ambiguity and outward-request gates. No execution authorized in this revision. |

## Proposed outcome and stop conditions

This revision is suitable for an independent compiler/source and spec/design delta review because the examples, owner path, categories and first runnable milestone are explicit. Acceptance requires no blocking/major review finding and exact artifact/source hashes. Any major omission leaves the milestone OPEN; no contract auto-expands.

Successful document review closes only “decision-ready method/role pilot design.” It does not choose the semantics. The next selector consultation should frame the strongest bounded outcome as a user decision packet followed, if approved, by one integrated runnable method/role pilot. Keep the effect-hygiene path at receiving/selection and outward-boundary owners, applying any new proof to the original obligation. Do not refill the lane with automatic storage/fiber exploration.
