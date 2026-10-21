# R263 — locate an in-repository Y2 parser and registration path

Status: ACTIVE primary-only source audit; read-only.
Branch / baseline: `research/simple-sub-intrusion` / `3fe3d8cfd`.
Authority: unchanged Types/Console user goal; R149, R261 and R262. This audit
does not alter the language semantics or close R168, parent proof, or
production gates.

## Original outcome and success evidence

Run the unchanged Yulang2 playground Types/Console samples in ordinary tests
with proof-backed source-to-runtime correspondence. R260-R262 establish that
the imported initializer census is conditional and the current Y3 CST cannot
serve as a Y2 root witness. This sprint searches only the current repository
for an authentic Y2 parser, module registration implementation, or retained
Y2 parser artifact/API.

Success: identify exact in-repository source owners and interfaces that can
parse/register the pinned 40-source closure, with hashes and a clear
Y2-authenticity premise; or record a bounded `NO_IN_REPOSITORY_Y2_PARSER`
result with the searched source roots, exact Y3-only candidates, and the next
in-repository implementation/evidence seam. A text-only search result is not
proof that no code exists: inspect candidate owner modules and executable
entrypoints.

## Scope, resources and stop conditions

Primary-only, read-only audit of repository files under `crates/`, `tools/`,
`apps/`, and relevant tracked Y2 evidence under `notes/` and
`tasks/agent-loop/`. Search source/interface ownership and executable routes;
do not inspect or modify external checkouts or temporary directories. No code,
test, build, or sample execution in this packet. Cap 420 seconds, no carryover.

The audit ends if no repository-owned Y2 parser/registration implementation
is found after source and manifest inspection. Record exact owners that were
rejected and why. Independent review is unavailable, so any negative result
remains primary-only and does not authorize implementation. Preserve the
unchanged sample inputs, R149 contract, all proof quantifiers and the R168
implementation boundary.

## Still-open obligations

R149 imported ModuleMap identity/publication, accepted Types, root
specialization, Request reachability, output, Simple-sub/evaluator A/B,
R70/R71, source/native correspondence, soundness, principality and production
remain OPEN. If the audit finds no authentic parser, the next sprint must
identify a source-preserving bridge in this repository before any dependent
runtime implementation.
