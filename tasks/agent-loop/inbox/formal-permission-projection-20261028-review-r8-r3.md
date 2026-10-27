# Independent review: formal permission projection r8-r3

Disposition: MAJOR conditional-proof gap; accept the authenticated inventory and owner STOP only. No preservation theorem or r7 premise removal is established.

## Identity, scope and authentication

Actual independent reviewer/session: `/root/formal_permission_projection_r8_r3_review`, delivered by NEW_TASK. No authorship of the submission or prior r8 evidence. Startup ACK and active-work receipt sent before inspection. Requested model/effort inherited without override; effective model/effort and separate session UUID UNKNOWN. No descendants.

Target SHA-256 independently matched `aafd543e2dc727d8999342ff0d76b8419730befd48cbf9a2d8cd6116a0771148`. Original r8 contract, addenda 01/02, all ten admitted source/policy pins, frozen r8 outcome, and r8-r2 source/review hashes independently matched the target's table. Baseline `3cc8a897fe08980576b1582952a95acab55f09d2` remains a primary pin, not an independently resolved revision. Hashes authenticate current bytes, not producer execution history or semantic claims.

Read governing r8 contracts, root/base instructions, design authority, relevant annotation policy and inference principles, admitted merge/helper/journal/resource bodies and r8-r2 conditional lemma. Source bodies supply evidence independently of producer narration. No candidate_context.rs body was opened. No tests/builds/probes, Cargo/Lean/Lake, Git or network ran. No compiler change is submitted, so executable tests would not discharge this logical issue.

## Finding

### MAJOR — selected-root stability does not preserve the whole forest

Location: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r3.md:177–185`, particularly the conclusion at :182–183. Dependency: r8-r2 conditional link lemma, item 3, requires a closed finite forest at the link step.

The listed premises assume closure at selection, preservation of the two selected root entries and vector lifetimes during intervening calls, checkpoint/log association, and inverse ordering. They do not require preservation of closure for the rest of the forest. Thus they cannot justify that the final link preserves the forest by the cited lemma.

Concrete logical countermodel: at selection take F=[0,1,2,3], r=0, s=1. An intervening helper writes F[2]=3 and then F[3]=2, recording the old parents in the proper checkpoint and temporal order. It preserves r, s, all vector lifetimes, and the checkpoint/log association. No inverse entry needs an out-of-order position. All stated assumptions hold, but the forest has a 2↔3 cycle before and after F[0]=1. Correct inverse logging does not establish forward forest well-formedness. This is a countermodel to the conditional implication, not an allegation that admitted source reaches this state.

Violated contract: original r8 fixed outcome/stage 2 requires a preservation induction over the forest invariant, and amendment 02 requires composition with the actual premises of the reviewed local lemmas. Root stability is necessary for the selected link but is insufficient for global closure.

Minimum closure: explicitly require the entire addressed forest to remain closed immediately before the final link, or establish that every intervening effective forest mutation preserves closure. Keep that premise OPEN at its actual transitive source owner. Rephrase the present conclusion as preserving only the selected link's local safety under a separately stated whole-forest invariant. No new source execution or source-reachable counterexample is required to repair this conditional statement.

## Other checks and limits

The effect inventory agrees with inspected direct statements: the merge journals its prospective inverse before bound copies; the newly admitted count/read helpers perform no direct forest write; insertion mutates bound storage/evidence and skips capture registration with capture=false; origin transfer calls an unrestricted session method at candidate_effect.rs:697; splice journals bucket/link metadata before direct writes; journal/capacity helpers update bookkeeping and can sample resources. Direct write absence is consistently distinguished from complete transitive effects.

The STOP at unadmitted `crates/yu-solver/src/candidate_context.rs` is justified by the concrete transport call and evidence helper calls. The report correctly says :697 is not necessarily the first dynamic unknown call and retains earlier journal/resource transitive gaps. The root/checkpoint equation at :64–67 correctly includes in-range self-roots immediately before the write and same-checkpoint inverse ordering. The defect is its later claimed conditional composition, not the equation or owner resolution.

No runtime-independent evidence confirms the producer's command list, model, elapsed runtime, or lack of unrecorded accesses; those remain attributed receipts. Current bytes match all authentication claims. No evidence supports a reachable source falsifier, successful wrong-image export, or removal of any r7 premise. B, D, reachable forest/lifetime preservation, r1 Lean verification, original A/B, source/native, full inference/executor and production remain OPEN. No additional BLOCKING or minor finding is established within this bounded review.

## Resources and handoff

Cap: 120 seconds, one CPU, 1 GiB. A recorded clock during review was 2026-10-27 22:48:38 UTC; exact launch-to-stop duration, CPU and peak RSS UNKNOWN. Only short sequential static reads and hashes ran. Charge the full 120-second grant and preserve previous charges. Some broad output was truncated; no exhaustive transitive effect certificate is claimed.

Sole write: this review artifact. No source or shared state changed. Primary owns finding adjudication, any producer repair, owner admission and worker-state synchronization. Reviewer STOP on submission; no descendants or unresolved descendant leases.
