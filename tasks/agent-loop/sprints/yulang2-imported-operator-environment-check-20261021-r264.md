# R264 — distinguish parser-environment failures from Y2 syntax gaps

Status: ACTIVE primary-only read-only investigation.
Branch / baseline: `research/simple-sub-intrusion` / `512404178`.
Authority: unchanged Types/Console goal; R149, R261-R263. R262's empty
`SyntaxEnvironment` probe may confound missing operator capabilities with
source incompatibility. Recheck before treating its diagnostics as a Y2/Y3
grammar falsifier.

## Outcome and scope

Use the pinned 40-source bundle and current public `yu_syntax` interface to
check whether authentic imported operator headers materially reduce the
diagnostics observed after the bounded line-comment projection. Construct one
probe environment from scanned headers only as a diagnostic control; it is
not assumed to model each module's actual dependency set or authenticate Y2
semantics.

Temporary test code may be used and must be removed. No compiler, test,
fixture, expected-output or semantic edits may remain. Inspect exact diagnostics
counts and representative structural recovery paths. If all-source header
construction conflicts or parser diagnostics remain, preserve that exact
obstruction. Do not use this broad environment as a module registration
witness.

## Evidence, limits, resources

Primary-only, 420-second cap, no carryover. Source reads are limited to the
pinned standard-library bundle, the current `yu-syntax` header/environment/
parser APIs, and R262/R263 evidence. One focused Cargo test process at a time.
Stop after the environment control identifies whether R262's empty-environment
diagnostics were materially confounded. No independent reviewer is assigned;
the result remains provisional.

Even a zero-diagnostic parse would not prove exact Y2 syntax or ModuleMap
registration. R149 imports, source/root correspondence, accepted Types,
specialization, Request reachability, output, parent proofs and production
remain OPEN.
