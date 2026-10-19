# R79 readiness — first role-qualified executable call

Status: Draft; independent review pending; no semantic adoption or implementation  
Contract: `tasks/agent-loop/sprints/effect-hygiene-role-call-20261019-r79.md`, SHA-256 `0ad36f8f9efb6e9fab326cd7df35e553c6baa9b1dd721e277a8ac184c774e479`  
Design: `notes/design/2026-10-19-r79-first-executable-role-call.md`

## Product direction

The first proposed runnable surface is a role-qualified call `SecondInt::second 1 2` that returns `2`. This gives a concrete role-backed path without claiming that general dot syntax has settled field/method precedence. `1.second(2)` remains a competing, more method-like surface proposal; its general collision semantics stay OPEN. This R79 decision package explicitly replaces no previous approved rule and adopts no new one.

The design includes full declarations for unique resolution, missing member, missing implementation, duplicate implementation, same-spelled members in distinct roles, effectful Value receiver/argument, explicit Computation retention, outward method request, and malformed/unsupported/type-invalid distinctions. It maps declaration identity, signature/body validation, executable root/environment, exact member selection, Apply provenance, `CandidateInference` admission and `RuntimeProgram` metadata. Its proposed first implementation milestone is the unique result `2`; later execution cases belong in that separate contract.

## Readiness gates

| Gate | State | Evidence or remaining work |
|---|---|---|
| Role/impl parsing | Existing syntax owners; meanings unadopted | Exact role/impl nodes and identities are pinned. Syntax parse does not define call semantics. |
| Qualified call semantics | Decision draft | User chooses qualification, receiver stage, duplicate policy and diagnostic sites. |
| Member validation/materialization | Missing implementation path | Must tie source declaration/member IDs to signature validation, body root and lexical environment. |
| Call typing/source provenance | OPEN | Ordinary Call formation and both-direction generated Apply provenance remain proof obligations. |
| Candidate admission | Missing | `candidate_source.rs` preflight currently does not admit validated role/impl executable metadata. |
| Runtime execution | Missing | `RuntimeProgram` needs validated member metadata and source-qualified selected identity; first goal is result `2`. |
| Dot-field collision | OPEN/deferred | No real field/method source collision is claimed. Decide in a later bounded design only when the receiver domain is evidenced. |
| Effect receiving/source bridge | In progress, bounded | R79-SOURCE-HIR-1 traces exact U/O/S source constructors; stops at 900s or first missing rule. An obstruction leaves the obligation OPEN. |
| Full effect hygiene | OPEN | R78 runtime certificate is conditional; native K/D, residual typing and universal continuation obligations remain. |

## After review

Fresh independent compiler/source and spec/design reviews must find no blocking/major design-readiness issue. Proof review/application remains independent. A clean review closes only the design packet, not its semantic choices. The user then decides the concrete proposals. Only an approved choice unlocks a new, exact implementation contract with source, test, expected-output and verification-command leases.
