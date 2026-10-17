Sprint-ID / contract revision and SHA-256:
  npair-actual-argument-ingress-20261018 / rev1 /
  c0754dc6de94c15e923ce24cc58b8208d0934dcf7bc92abcae34589185ec9d32
Assignment-ID / handoff revision:
  npair-actual-argument-source-path / rev1
Parent gate / original theorem and scope locator:
  CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017; original theorem,
  quantifiers, receive route, source domain, C1/C2, F1/FK1 unchanged.
Baseline / direct dependency hashes:
  Baseline b3a9b1739b59d8c7991b5f798e98f71f96904b19.
  Contract c0754dc6de94c15e923ce24cc58b8208d0934dcf7bc92abcae34589185ec9d32.
  Pinned source/example inputs matched contract hashes:
    candidate_source.rs 4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce
    candidate_call.rs 2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359
    candidate_scheme.rs abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494
    candidate_effect.rs 9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212
    candidate_context.rs 72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6
    candidate_extrusion.rs 2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b
    research_source_registration.rs 10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c
Role / actual worker ID / session / launch or resume receipt:
  Luna implementation/source lane; /root/npair_actual_argument_source_path;
  current-session. Assignment arrived as an active task under the primary's
  current-state receipt; no separate runtime metadata is exposed here.
Requested model and effort / observed model and effort:
  Luna / high; UNKNOWN / UNKNOWN.
Exact leased paths / authors:
  notes/progress/2026-10-18-npair-actual-argument-source-path.md
  tasks/agent-loop/inbox/20261018-npair-actual-argument-source-path.md
  tasks/agent-loop/fixtures/20261017-receive-choose.yu
  Author: /root/npair_actual_argument_source_path; no descendants.
Outcome class:
  source-native-evidence (bounded refusal probe; not implementation).
Parent application / remaining premise and owner:
  Parser reports no structural recovery, but HIR marks added `received`
  expression UnsupportedExpression at range 372..382. It is absent from
  LocalSource, so no candidate collector coverage exists for the binding.
  The partial HIR retains receive's existing f() -> local g -> g() body and
  resolves f0's choose use to its declaration. No outer Apply, actual call,
  Call/Function comparison, s1-to-D edge, or ordered Replay inputs are
  established. Parent remains OPEN.
Source constructors -> constraints -> propagation -> consumer/native path:
  candidate_source.rs captures lowered Apply nodes as generic Apply relations
  and ApplySourceInput records. candidate_call.rs validates source endpoints
  only after NativeInterface exists and exposes Gen-Call-0 suppliers as
  pending requirements. candidate_context.rs has generic Function-port
  admission and ordered Replay from lower_input/upper_input; no inspected
  path joins those inputs to this missing binding or proves s1-to-D.
Artifact locators / byte hashes / frozen review snapshot:
  notes/progress/2026-10-18-npair-actual-argument-source-path.md
    SHA-256 a856822836623c031e1fe545da2821ebab725298ce79f8208fd2c5442d1180ef
  Fixture restored byte-for-byte:
    tasks/agent-loop/fixtures/20261017-receive-choose.yu
    SHA-256 969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0
  No separate review snapshot; artifact is frozen for primary intake.
Checks, coverage, omitted cases, resource budget:
  Ran exactly once:
    timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
  Exit 0. Printed parse.structural_recoveries=[], HIR UnsupportedItem at
  80..130, UnsupportedExpression at 147..162, 328..356 and 372..382,
  candidate.observes_hir=true, candidate.conflicts=[], and f0-only export.
  No tests or other build/check ran. One heavy process; under 120s. Assignment
  cap 720s; no other resource use. Green exit is not source acceptance. This
  is only refusal evidence for this added source line, not negative evidence
  against the theorem or the proposed s1-to-D edge.
Next related step / exact boundary:
  Need Luna to identify and sequentially pin the HIR lowering owner that emits
  UnsupportedExpression for the new module binding (range 372..382) before
  any further source experiment. Exact file path is unknown; no owner outside
  the six assigned read pins was inspected. After HIR exposes the Apply, a
  separately authorized trace must show collector coverage, actual argument
  to formal, same R1, Function field comparison to D and both ordered Replay
  inputs. Do not infer hidden s1->D, At/N-Subtract, H0/L2, or parent closure.
Mutual TODOs:
  HIR-UNSUPPORTED-20261018-1 — Luna: identify/pin the HIR lowering source
  owner responsible for `UnsupportedExpression` on range 372..382; first
  missing evidence is the accepted outer Apply in LocalSource. Falsifier:
  pinned lowering evidence shows the syntax is intentionally unsupported, in
  which case stop this source route without narrowing the theorem's domain.
Worker state / writes stopped receipt / unresolved leases:
  STOPPED; fixture restored to baseline hash after receipt; no active writes,
  descendants, generated outputs, or scratch files remain.
Commit/review/integration:
  Not commit-ready. Primary review/integration required; no gate promotion.
