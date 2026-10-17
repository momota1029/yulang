# Operation source contract and Local route sprint closeout

Sprint `npair-operation-source-contract-and-replay-reachability-20261018`,
contract rev3 SHA-256 `1fa25ac715f9bd583c7dc56e11b1fe027f71e953faac0fc6130b2e2b009ed94d`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN;
original-condition closure **0 -> 0**.

## Proof result

The source-owner lane derived the concrete Operation request-carrier,
consumer/suffix, actual `A_decl` completion and complete-output `phi` action.
It still cannot identify the parent's original fixed `c` with that `phi`, or
prove universal active-consumer reflection. The two-observation disjoint-fiber
quantifier construction remains conditional: no source-qualified admitted
counterexample was found.

Independent proof/spec review was CLEAN only for preserving the exact
conditional candidate and its stated boundaries. It identified two BLOCKING
adoption conditions: original-c identity at the same formation/reference/theta;
and universal compatibility/reflection for every original R/W/Z case with
full Sigma/Lambda/G/licenses/domain and the active consumer. No rule is adopted
by this receipt; no original theorem condition closes.

Frozen proof artifacts:
- proposal `notes/design/2026-10-18-operation-contribution-formation-proposal.md`:
  `7d966d665fc4a87806c4ba989bb11c8ec1fbde34a39432a31e190cf207ec1236`
- parent application `notes/theory/2026-10-18-operation-contribution-parent-application.md`:
  `e1124c001d6529d326ce82b5d58294b263f6a8eb707f00f0ddfa67089262cf7d`
- proof handoff `tasks/agent-loop/inbox/20261018-operation-contribution-contract.md`:
  `6989d97551d2151e4351b8db32eca345c3a486229e49f1f84339eacda8d94b0e`
- independent falsifier `notes/theory/2026-10-18-operation-contribution-contract-falsification.md`:
  `1176df49cae3afb91d8bf35b47eb52f112523b443b9ce071c69b9aeedae0c405`
- falsifier handoff `tasks/agent-loop/inbox/20261018-operation-contribution-contract-falsification.md`:
  `dca9f8c0a1c458dc99b0dc88bf02c7e15d29a5abdaa7ce26c48773d366c6b2d2`

## Implementation result

The implementation author connected scoped Local-source discovery, Apply
source-input retention and LocalUse/FreshUse publication. A fresh compiler
review found two MAJOR defects in the frozen candidate:

1. Apply checked `local_routes.last()`, although source evaluation processes
   the callee before the argument. A later LocalUse in the argument could
   replace the callee's route and cause a false `IdentityExhausted`.
2. New `SCOPED_RECORD_LIMIT` checks also applied to unscoped candidate
   inference, introducing a new failure boundary in ordinary inference.

No Cargo/test/fixture command ran. I restored all four source files to the
pinned source baseline because the candidate was not safe to integrate. Exact
restored hashes:
- `candidate_source.rs`: `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b`
- `candidate_call.rs`: `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359`
- `candidate_scheme.rs`: `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494`
- `shadow_apply.rs`: `d29d5f6488b5824eef5dc7902b70351b5bfae1ae3d7d014ec3629267443dbc83`

The observer from the prior reviewed checkpoint remains present, but its
runtime and demand-bearing Replay rows are still unverified.

## Review and next proof/implementation seam

The source proposal/application and falsifier were independently reviewed as
conditional research only. The implementation candidate was NOT CLEAN and was
restored. Parent and production gates remain OPEN.

Next target: pair an original formation-based fixed-c compatibility proof (or
an explicit concrete decision packet) with an exact local-route association
that is invariant under later argument LocalUses; keep scoped caps scoped.
Add focused regressions for a local callee plus a local argument and for
unscoped-limit noninterference. Then run the exact receive fixture only after
CLEAN review. No source-domain, expected-output or quantifier change is implied.
