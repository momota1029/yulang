# Sprint ordinary-mixed-capture-20261019-r53 — ordinary source-to-native mixed capture

Status: ACTIVE, primary-approved; constructive proof plus read-only source construction
Branch / baseline: `research/simple-sub-intrusion` / `158f319398a8e0b2e5b9d575446f5ebfa5022298`.
Primary: `/root`, session `current-conversation-2026-10-19-r53`.
Authority: top-level inference principles §§1–5; forwarding-preservation §§6–7; approved local self-recursion rule; R52 reviewed candidate and both message-only review receipts integrated at baseline. R50 active-Link scoped protocol remains NOT ADOPTED.
Contract revision / SHA / approval: revision 3; Luna primary-approved before proof output writes. Revision 1 manifest columns were transposed and revision 2 source wording called the enclosing top-level function a local binding; neither draft produced proof writes. Revision 3 corrects the source shape and preserves the verified manifest.

## Fixed outcome

Trace the R52 recursive source candidate through the existing ordinary `CandidateInference::solve` entry and its scalar lowering, then determine the same-provider port coverage through its actual source-qualified extrusion group and any subsequent capture. Either prove coverage for this concrete ordinary-route history; produce an authentic same-lineage mixed cut; or identify the first exact ordinary-route source/native obstruction. Do not infer universal post-merge preservation from this one candidate. Preserve the original forwarding-preservation quantifiers, source domain, accepted semantics, expected outputs and OPEN parent.

The selected source is an approved single parameterized local self-recursive binding with nested local `forward (t:[io] int)=t` and `used=loop forward`, inside the body block of the top-level parameterized `outer q` function, which realizes the level-2 recursive root and level-3 provider/use. The exact source is restated in the proof artifact. No mutual recursion, polymorphic recursion or new source restriction is authorized.

## Mandatory mode distinction

R52 established only that `authenticate_scoped_apply` blocks this active-Link use when `scoped_experiment` is enabled. R53 must trace `CandidateInference::solve`, which calls `solve_mode(hir,false,false)`, and show exactly which source actions, Apply lowering, qualified parent work, settlement and capture execute in that ordinary mode. Do not carry the scoped obstruction over to the ordinary path. Do not call `solve_scoped_experiment`, turn off any validation, or infer solve success from candidate-source reachability alone.

## Lanes and exact outputs

Sol/high proof: reconstruct the ordinary route from HIR LocalSource through active recursive Link, installed `forward` use/FreshUse, `Action::Candidate`, native interface and typed scalar dispatch. Track original provider formal/body/argument occurrence, every signed Function port, physical BoundKeys, source event set, extrusion parent/co-parent group, representative level/nongeneric changes, settlement and actual reconstruction maps. Conclude concrete port coverage or first ordinary-route obstruction. Keep source-SCC qualification, native dispatch reachability, solver completion and later capture as distinct claims. Outputs: `notes/theory/2026-10-19-r53-ordinary-mixed-capture.md`; `tasks/agent-loop/inbox/20261019-r53-proof.md`.

Luna/high read-only source audit: independently trace the same source through ordinary `CandidateInference::solve` and establish whether the candidate reaches the required scalar dispatch and settlement from the static producer/consumer path. Map exact owner and sign transitions and any actual capture consumer. No source edits, tests, builds, runtime, probes or measurements. Outputs: `notes/progress/2026-10-19-r53-ordinary-source-native.md`; `tasks/agent-loop/inbox/20261019-r53-implementation.md`.

Fresh compiler referee and spec auditor review the exact frozen packet, explicitly checking ordinary/scoped mode, source route, signed co-parents, same-lineage reconstruction, and unchanged parent quantifiers/authority. Message-only receipts integrated by Luna.

## Stop and authority boundaries

No code edits, tests, builds, runtime executions, test-only observations, probes, benchmarks or measurements. No implementation handoff beyond a static exact obstruction. R50 adoption, active-Link semantics, capture/freshening changes, parent closure and production promotion are outside this sprint. If the route requires new source authority, changed dependencies, new artifacts, code/test execution or a different model of source admission, stop dependent work and return to Luna for a revised exact contract. Unknown writers retain quarantined leases. Primary alone owns Git.

## Resources

Fresh cap: 2400 seconds. Sol proof 900; Luna static source audit 600; independent compiler/spec reviews 300 each; Luna integration 300. At launch charge 1500 seconds; reserve 900. Astra 0. No carryover. Requested/effective runtime settings and CPU/RSS are not evidence unless explicitly reported by the worker.

## Frozen handoff and dependencies

R52 closed at the reviewed bounded result. R52 compiler and spec reviews were CLEAN and message-only; their receipts and primary adjudication are in the baseline `current.json`. R52 did not prove a general post-merge invariant. R52 proof and Luna source artifacts below are content pins, not transferable conclusions beyond their stated scope.

Exact consumed-file SHA-256 manifest (all bytes revalidated before launch):

```text
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
477ada20e61ce5355601af138b37016ba1a8036e65f4f39627beda2abe062adf  notes/theory/2026-10-15-computation-signed-copy-source-bridge.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
baeebe5872dcf313cffa402667494a9ea9d5395bbe18025e1c14f0c1d7526397  notes/progress/2026-10-15-computation-source-plans.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134  notes/design/2026-10-15-callback-identity-forwarding.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
f133c402f47b90f37bca92d2470cd7007fd320c580efba9ae0919a7f38a027b8  notes/theory/2026-10-19-computation-formal-copy-bridge.md
8180aa417995c6d069a5a1b24a0ab405ad0b10bb056ac42c74d402a0ca0874ce  tasks/agent-loop/inbox/20261019-computation-formal-copy-proof.md
b58e19d3a921dcf9ba99627c8584f24f8d7ab779a336f21e21f0dcd63d7a0807  tasks/agent-loop/sprints/computation-formal-copy-bridge-20261019-r51.md
a37cd471c26c9936118282afe2eec295380a02b5197159d787f7d3ef75a50b47  notes/theory/2026-10-16-first-call-local-result-view-generalization.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
feb92f2ff3f2dc65059e07723adc5bef8ebf2ca9f83c979120ac484214c8e69d  tasks/agent-loop/sprints/computation-mixed-capture-20261019-r52.md
16850d4f83a65d1c4a124c520da0b1546a97c62869b0a23a3722f3f93afe6220  notes/theory/2026-10-19-r52-mixed-capture-coverage.md
3ad115cf65969c1b39b074fcc2e22631c0ab04f91eb810a4d666087a78cce2c1  tasks/agent-loop/inbox/20261019-r52-proof.md
276b692d820aa6cec3e29a2428b4e75ff34e20e546b76fc07209eed8e1ab6299  notes/progress/2026-10-19-r52-mixed-capture-source.md
f667508891d9990036c5bd33150d96f428bae0030af007cd174d28915e00773a  tasks/agent-loop/inbox/20261019-r52-implementation.md
```

Leases (no other output or scratch path):
- `tasks/agent-loop/sprints/ordinary-mixed-capture-20261019-r53.md` — Luna primary
- `notes/theory/2026-10-19-r53-ordinary-mixed-capture.md` — Sol proof
- `tasks/agent-loop/inbox/20261019-r53-proof.md` — Sol proof
- `notes/progress/2026-10-19-r53-ordinary-source-native.md` — Luna source audit
- `tasks/agent-loop/inbox/20261019-r53-implementation.md` — Luna source audit

Baseline: `158f319398a8e0b2e5b9d575446f5ebfa5022298`; no pending Git changes at sprint entry. Review and end-boundary dispatcher consultation occur after both lanes freeze. Parent remains OPEN 0→0 throughout.
