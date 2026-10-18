# Implementation handoff — Replay positive provenance

Sprint-ID / contract revision and SHA-256:
`npair-provenance-complete-replay-and-operation-rules-20261018`, revision 1,
`248f7949bb7b69875afd44c0965f878405b4563b14c68eb58a58aa28ae318455`.

Assignment-ID / handoff revision:
`replay-positive-provenance-20261018`, revision 2. Revision 1 received a
blocking independent review because its census was wired only to the
CandidateInference observer, not the contracted InferenceSession helper.

Parent gate / original theorem and scope locator:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN; original
quantifiers, source domain, accepted semantics and fixed `c` unchanged. This
handoff is source-native observational evidence only and closes no parent gate.

Baseline / direct dependency hashes:

- `candidate_scheme.rs`: `d3e49fd2a737e271fdf579807732516ee8c3b40050449b82c34813f65f8f326c`
- `candidate_context.rs`: `f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569`
- `shadow_apply.rs`: `6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3`
- source constructor owner `candidate_source.rs`: `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`
- call owner `candidate_call.rs`: `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`
- governing contract: `248f7949bb7b69875afd44c0965f878405b4563b14c68eb58a58aa28ae318455`

Role / actual worker / current session / launch receipt:
`implementer` / `/root/provenance_impl_20261018` / `current-session` /
Luna's exact-path authorization received after ACK. No descendants.

Requested model and effort / observed model and effort:
Luna / high; observed model UNKNOWN / observed effort UNKNOWN.

Exact leased paths / authors:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tasks/agent-loop/inbox/20261018-replay-positive-provenance.md`

Only the assigned worker authored this packet. The code paths were already
dirty at intake relative to HEAD, with their present bytes matching the pinned
baseline. Those existing edits were preserved; no unrelated work was reverted.

Outcome class:
`source-native-evidence`, provisional and test-only.

Parent application / behavior achieved:
The diagnostic observer records each retained positive Function node's
route owner/index, node index, four child indices, retained child/root terms,
and exact match to the selected lower root. For each Replay lower input it
records every matching lower-bound relation with its typed pair, scoped flow,
bound admission and associated physical emissions. It also records the native
source demand root and its four ports alongside the copied FreshUse root,
use-instance and four copied ports. Existing per-run route authentication
stages remain available for matching routes and first rejection. The observer
is compiled only under `cfg(test)` and gated by the existing observer env var.
Revision 2 also wires the same census directly into the contracted
`InferenceSession::execute()` focused test helper immediately before its
existing authentication `expect`. That helper emits lower-root matches, lower
relation pair/flow/admission/emission provenance, source and copied roots and
ports, and whether authentication returned evidence. The existing assertion
and mutation controls are unchanged.

Source constructors -> generated constraints -> propagation -> consumer/native
path:
The instrumentation reads retained FreshUse route graphs/maps and the actual
Replay dependencies after inference. It reads lower fibers, relation pairs and
flows, producer admissions/emissions, and native/copied function terms. It does
not generate constraints, alter propagation or select a different consumer;
existing authentication and assertions remain intact. This packet therefore
adds run-local source/consumer correspondence evidence, not an end-to-end
production behavior change.

Artifact locators / byte hashes:

- `crates/yu-solver/src/candidate_scheme.rs` —
  `0c55d3d47bc88166a68eb5f5797043b136a2d2bc0ace55de832e8e27ca20a07f`
- `crates/yu-solver/src/candidate_context.rs` —
  `f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569`
- `crates/yu-solver/src/shadow_apply.rs` —
  `6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3`
- frozen review target is these three exact code paths plus this handoff;
  no tests/runtime were run and no test output artifact exists.

Checks, coverage, omitted cases and resource budget:
`git diff --check` passed for the three code paths after repair. No Cargo, compiler, test or
runtime command was run. The diagnostic and its source constructors have not
yet been observed executing; route multiplicity, lower-root matches and producer
provenance remain unreported until the authorized diagnostic attempt. No helper,
graph or source-example coverage was run. The 600-second author grant was
charged at launch; actual active seconds are UNKNOWN to this worker. Runtime
remains locked pending fresh independent review and Luna's one-command grant.

Next related step inside the existing envelope:
Fresh independent review of this frozen revision. If CLEAN, Luna may
authorize the single frozen diagnostic command. Do not infer a semantic or
ownership change from the census; route/authentication changes return to Luna.

Mutual TODOs:
`TODO-REPLAY-PROVENANCE-DIAGNOSTIC-01`; parent `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017`; first missing evidence: actual census output
for all exact current-lower-root matches, lower relation pair/flow and producer
records, plus source/FreshUse ports; owner: Luna for runtime authorization and
runtime logs; required input: CLEAN review of this frozen target and the exact
contracted command; proposed output: Luna-owned diagnostic stdout/stderr/meta
logs; falsifier: zero or multiple exact matches inconsistent with the rejection,
caller-owned function evidence missing from callee capture, or provenance that
does not identify the selected lower relation in that run.

Worker state / writes-stopped receipt / unresolved descendants:
All assigned writes stopped at freeze. No descendants. Runtime was not started.

Commit-ready milestone or pending review/integration:
Revision 1 received a blocking independent review because the census was not
wired into the contracted `InferenceSession::execute()` path. Revision 2
contains the minimum requested helper wiring and is frozen pending a new
independent review. Not commit-ready or integrated.
