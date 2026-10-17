# Sprint `npair-fixed-c-source-selection-scoped-collection-20261018`

Status: ACTIVE, revision 1. Branch `research/simple-sub-intrusion`;
baseline `d9e6949a4cdc2d1899f55d5e7a75a014d4630606`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN, closure 0.
Original theorem, quantifiers, source domain, receive route, C1/C2 and F1/FK1
are unchanged. Previous sprint closeout:
`notes/progress/2026-10-18-npair-written-conservative-lift-closeout.md`
SHA-256 `d27386f25325dbbbf229817bbdfe84ad9bb0d85aa7619605abf09f54e1abd97c`.

## Fixed outcomes

1. Trace the original fixed contribution `c` from its actual source constructor
   through Operation response selection and its designated consumer to the
   actual returned provider's Written `r.s1`. Derive its original field proof
   and complete dependencies, or identify the exact missing source rule and
   draft a reversible interpretation with explicit compatibility/falsifier.
   Do not infer `c` from root Support, member index, `r:B`, family membership,
   `CallMem`, or an unadmitted R/W/Z inhabitant. No candidate interpretation is
   adopted as theorem proof until its original domain, erasure/reflection and
   consumer behavior are independently reviewed.
2. Diagnose the exact owner and branch that makes the scoped candidate
   collection exit `Collection(ComponentIdentityExhausted)`. Preserve source
   identity and existing Install/Capture/FreshUse suppliers. Apply a minimal
   correction only when it retains those original identities and constraints.
   The target observation is the authenticated `received` Apply/source_call
   linked to its scoped relation/scope; the two ordered Replay BoundKeys remain
   separately required and may remain UNOBSERVED if no typed API owns them.

Do not route around the experiment through ordinary `solve()`, remove a
provenance/identity guard, alter expected output, weaken the theorem, or turn a
candidate conflict/count into source rejection or proof. If the observed source
case is outside an existing owner’s authority, stop that code path and return
the exact missing rule/owner before changing semantics.

## Frozen dependencies

The previous sprint contract SHA-256
`704a20cf457ed02ff07b52a399f6440c2fb145d02d6f840db10896f8d892c856` is the
transitive frozen manifest for the original theorem/source/call/effect
contracts and 24 direct dependencies. The following added result and owner
pins were checked at this sprint baseline:

| Path | SHA-256 | Use |
|---|---|---|
| `notes/progress/2026-10-18-npair-written-conservative-lift-closeout.md` | `d27386f25325dbbbf229817bbdfe84ad9bb0d85aa7619605abf09f54e1abd97c` | Prior reviewed result and exact next premise |
| `notes/theory/2026-10-18-npair-written-conservative-lift.md` | `3482f86bb48869507f0ac89e304d01ad52f378f17456664cf751ad4e97e8e8a6` | Conditional source/Call calculation; fixed-c gap |
| `notes/theory/2026-10-18-npair-written-lift-adversarial.md` | `c447f90dba0018b139485c9b5cbdc4eeef08e345214d8bf3de245fa9d8b143ed` | Reviewed admission audit; no admitted counterexample |
| `notes/progress/2026-10-18-npair-call-scoped-replay-evidence.md` | `25fd000de4f3c9b7bf358b511a29ef28d23171e9b8feae44bfb0f35c53d6492b` | Exact failed scoped run; no CandidateInference returned |
| `notes/theory/2026-10-16-operation-primitive-image-contract-construction.md` | `4fe70b18cad9ded249869b21b84bbf26e2a5f95320f79632a29a5071ddb1c4e9` | Actual R response action; incomplete W/Z owner inputs |
| `notes/theory/2026-10-16-choose-installed-support-source-substitution.md` | `f795e62aa1c148f1707419a7eefaf51c4e0500620a186713f6d0bd76013c9096` | Original installation/substitution owner |
| `notes/theory/2026-10-16-first-call-fresh-use-semantic-application.md` | `9d5ec6a410c2b358187c1fcf105ba9efe5b2f5f9f4ede37ea2bb5364801ff46b` | Original call/fresh-use consumer |
| `notes/theory/2026-10-16-receiving-local-install-freshuse-correspondence.md` | `7537cb02f2d01532ad97ecddf4ddd4f75abccd791b028785d714f3d55ec0bc70` | Install/Capture/FreshUse correspondence |
| `notes/theory/2026-10-17-choose-operation-source-instantiation.md` | `6075d45f38787bd5a981a2da177504450239a05e6dbec6f19ccf526ca0d4a110` | Selected choose source, conditional constructor/application |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` | Original R/W/Z hard envelope |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` | Adopted CallMem/result clauses |
| `notes/theory/2026-10-07-owned-call-contribution-construction.md` | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` | Whole-evidence Call identity under premises |

Read-only code owners pinned at baseline:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/examples/research_source_registration.rs` | `25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca` |
| `crates/yu-solver/tests/candidate_operation_source.rs` | `ee95a08bcb7da80c17bdba60034377c4d230d3469f261838205cb8af3f39d8bc` |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` |

Every lane verifies direct pins before use. Any source/theory owner change
requires primary revision before dependent work proceeds.

## Lanes and exact leases

1. **Constructive source proof, configured Sol/prover/high, cap600s.** Trace
   the original fixed `c` constructor and field selection through the actual R
   response and designated consumer. Apply the full theta, provider, world,
   assignment, scope, guards, licenses and lineage. Then compose authentic
   CallMem. If no original rule introduces the field proof at `r.s1`, draft a
   separately labeled reversible rule interpretation and state observable
   consequences, compatibility obligations and falsifier; do not report the
   parent closed. Write only:
   - `notes/theory/2026-10-18-npair-fixed-c-source-selection.md`
   - `tasks/agent-loop/inbox/20261018-npair-fixed-c-source-selection.md`
2. **Independent source-case falsification, Sol/researcher/high, cap300s.**
   Check actual fixed-c identity, complete response admission and original
   consumer output. Keep W/Z independent and require their actual admission
   premises. No counterexample from missing bytes. Write only:
   - `notes/theory/2026-10-18-npair-fixed-c-source-selection-adversarial.md`
   - `tasks/agent-loop/inbox/20261018-npair-fixed-c-source-selection-adversarial.md`
3. **Implementation, Luna/high, cap900s.** Exact diagnostic, correction and
   vertical validation packet. Exact code leases:
   - `crates/yu-solver/src/candidate_source.rs`
   - `crates/yu-solver/src/shadow_apply.rs`
   - `crates/yu-solver/src/candidate_call.rs`
   - `crates/yu-solver/src/candidate_scheme.rs`
   - `crates/yu-solver/src/candidate_context.rs`
   - `crates/yu-solver/src/lib.rs`
   - `crates/yu-solver/examples/research_source_registration.rs`
   - `crates/yu-solver/tests/candidate_scoped_collection.rs` (create only if a
     behavior correction has a source-level regression to encode)
   - temporary fixture `tasks/agent-loop/fixtures/20261017-receive-choose.yu`
   - `notes/progress/2026-10-18-npair-scoped-collection-repair.md`
   - `tasks/agent-loop/inbox/20261018-npair-scoped-collection-repair.md`

   First determine the exact branch using a minimal source/occurrence-aware
   diagnostic; do not collapse distinct provenance, allocation and limit
   failures. A diagnostic-only patch must receive a fresh exact-byte compiler
   review before its first command. Apply only a semantics-preserving repair
   that retains source ownership, identity, Install/Capture/FreshUse routes and
   all scope/input remaps. Freeze final code and the regression before a second
   exact-byte review. At most three focused Cargo commands, each timeout <=120s:
   (1) identify the branch on the original fixture; (2) observe the repaired
   exact received-call route; (3) execute the focused regression or sibling
   preservation discriminator. Measure lane budget immediately before each;
   no command if less than120s remains. Stop on a needed rule/meaning change or
   unbounded remediation. Restore the fixture exactly. Do not bypass by using
   ordinary solve or deleting a validity guard.
4. **Independent reviews:** Fresh proof/spec reviewer cap180s on both frozen
   mathematical artifacts. Fresh compiler reviewer cap120s on diagnostic
   bytes before command1 and cap120s on the final source/test delta before
   commands2–3. Reviewers verify exact hashes and remain read-only. Primary
   adjudicates repairs and integration.

New envelope **2700 seconds**, fully reserved: constructive600 + falsification300
+ implementation900 + proof review180 + compiler reviews240 + primary120 +
reserve360. Astra0, descendants0, no prior-cap rollover. One heavy process at a
time. No background services.

## Closeout and parent application

A sprint success must reduce the original fixed-c premise or produce a
reviewed, premise-checked source counterexample. The source interpretation is a
candidate until compatibility is independently accepted; proposed rules alone
are not parent progress. Implementation success requires observed exact-call
identity and a working scoped path with regression evidence when corrected.
Record the original condition count, test/command results, hashes, review and
restoration. Keep Replay BoundKey identity separate if still unavailable.
The goal remains active after this sprint; do not mark the parent, soundness,
principality, termination or compiler complete from this packet.
