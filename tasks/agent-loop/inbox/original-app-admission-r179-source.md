# R179 source correspondence — App Logical field owners

Assignment: `/root/original_app_admission_r179_source`; revision 1, FROZEN.
Sprint: `ORIGINAL-APP-ADMISSION/20261102-R179`.
Contract SHA-256: `30bd50b1886d9b390ab290051b9d2926552b7dc45aa5a17ff47c35cde25e42aa`.
Primary-pinned baseline: `yulang3` at `9ee28f082c157fda11d7c5c948decd3798472bbb`.
Role requested: researcher; effective model/effort metadata: UNKNOWN.
Sole author: this worker; no descendants or joint authors.
Outcome: **BLOCKED — first App descriptor field recipe unauthenticated**.
Claim class: bounded static source correspondence / source-native-evidence;
no theorem, source counterexample, new admission policy or implementation result.

Objective and method: map the five existing `Logical` fields to the original
App and source-Generalize clauses, distinguishing data readers and constraints
from constructors. The parent is Yulang inference success implying the original
type/effect judgment, with all original forms and one same-solution `sameScoped`
witness. Runtime/Rust-program correctness is outside scope.

## Dependency receipt

Before direct-input content reads, separately counted 17 path rows, parsed
exactly 17 rows, required full 64-hex digests and recomputed all 17 successfully.
The same validation passed immediately before this sole output write. ACK was
sent to the primary after the initial pass. No dependency was changed.

| # | Direct input | Verified SHA-256 |
| --- | --- | --- |
| 1 | `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| 2 | `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| 3 | `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| 4 | `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| 5 | `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| 6 | `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| 7 | `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| 8 | `notes/theory/lean/YulangClosure/OriginalAppConstructionR160.lean` | `a7a766ef1d733719bfc4145bdcc9051e2e9e64521feb3fa400877a60bf9cb793` |
| 9 | `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean` | `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408` |
| 10 | `notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR104.lean` | `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39` |
| 11 | `notes/theory/lean/YulangClosure/OriginalSourceValueEntryAdmission.lean` | `3dc218f9d6623192d7d85c6f5be14f0fddbe833b19ede467c75647a5833205dd` |
| 12 | `notes/theory/lean/YulangClosure/OriginalProofProgress.lean` | `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39` |
| 13 | `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| 14 | `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| 15 | `tasks/agent-loop/history/app-demand-original-checking-r178-outcome.md` | `eb5dab4d2905db070d20e70c54a90b39a686285c8297d74e134bd68505cc5b47` |
| 16 | `tasks/agent-loop/inbox/app-demand-original-checking-r178-proof.md` | `86b17a3e1a943f53699eb19583d1ed89e2d32fc3974075064c758cfc6b63c2f3` |
| 17 | `tasks/agent-loop/inbox/app-demand-original-checking-r178-source.md` | `f79255103002e94c782259e60594b6280963feeebc2319fc939d6216601474fa` |

## Exact field map

Lean paths below are relative to `notes/theory/lean/YulangClosure/`.
SG means the pinned `2026-10-08-source-generalize-definition-and-proof.md`.

| Field | Original source owner and available equation | Missing App construction |
| --- | --- | --- |
| `descriptors` | `OriginalSourceEnvironment.lean:249–254` stores a list of endpoint/descriptor writes. `Decoded.logical:346–352` applies them with `put`. App `OriginalSourceGeneration.lean:111–123` introduces `descriptorFormation` and `wholeArgumentCompatibility`, plus the returned-callee value check. SG §3.1 Call retains original returned callee, inert whole argument, receiver/entry/consumer; §3.3 retains original declaration and dependency owners. | No pinned constructor computes the App descriptor entries from those child derivations and the same solution. `Kernel.atom:670–671` only supplies the local relation's type. This is the first missing field recipe. |
| `interfaces` | `Logical.interfaces` and `Decoded.logical` store/apply interface writes. App retains both `sourceRules context callee` and `sourceRules context argument`, and checks `⟨site,.callableImage⟩` against `⟨site,.synthesis⟩`. The builder comment `OriginalSourceGeneration.lean:79–82` explicitly identifies the argument as the inert whole code interface, not a printed Comp summary. SG §3.1 retains the complete actual Call tuple; §3.2 retains permissions, effects and finite checks. | No equation constructs this list from both child judgments while preserving complete argument interface, returned callee, inflow, residual and separate invocation/result ports. `OriginalSourceChecking.environmentReading:1010–1015` reads a supplied decoded state and supplied `PortReadout`; it does not produce these writes. |
| `viewMeaning` | `OriginalSourceEnvironment.Root:239–245` and `Decoded:303–314` carry `View → s.Interface`; `Decoded.logical:346–352` replaces it with the packet's supplied function. SG §2 selects one source joint view; §§3.3,5.2 retain one ViewLogic binder in its original incoming frame/telescope. | No pinned App equation identifies this packet field with the interpretation of that source-owned presentation under solution `a`. Copying a state's function is a possible candidate assignment, without the required App ownership/admission proof. |
| `eta` | `OriginalSourceInterpretation.Event:62–74` distinguishes fixed `eta0` from current `eta`. `Decoded.logical` installs the supplied `data.eta`. SG §3.4 (lines 353–359), §5.2 and §6 require the original scoped strategy at preceding dependencies. | No pinned map takes solution `a` at the exact App telescope to this field, or proves that the decoded prior telescope is the interpretation of that same `a`. Copying `state.assignment.event.eta` alone does not establish that correspondence. |
| `witness` | `Event.witness` and `Logical.witness` carry the original joint witness. `Decoded.logical` installs `data.witness`; it does not derive its origin. SG §3.4 requires one strategy on the entire joint tree; §5.2 preserves Shared/event identities and ViewLogic frame identity; §6 retains the same whole witness and binder dependencies. | No App constructor transports `a`'s joint witness through the complete prior telescope and this extension. A freely supplied `s.JointWitness` or separately solved children would leave the premise open. |

The actual source child judgments in the App continuation are both at the
**same extended environment**, rather than two independently selected worlds
(`SourceAppAdmissionR159.lean:126–154`). Its theorem is inspected only to locate
these existing premises. It is not used as a newly proved construction.
`SourceLogicalOccurrencesR104.app_exact:321–344` authenticates the App binder,
full body and annotation route, including both annotation alternatives. It
constructs no semantic packet.

The existing typed telescope owner is
`OriginalParameterSemantics.Telescope:18–24`; `.frames`, `.values` and
`replayTelescope:25–35` retain actual frames and fold `decodeFrame` over them.
`telescope_keeps_binders:37–42` and `telescope_keeps_payloads:44–48` preserve
binder/payload data, but do not prove admission or equality with an inferred
solution. `OriginalParameterWorld.FormalAssignment:57–59` is specifically a
Parameter/route/prior-scope contract assignment. It is not a general App
solution interpretation. The original parent `sameScoped` requirement is
retained by this contract; no declaration defining its App readback is among
the inspected matching declarations. No unpinned parent module was opened.

## Existing producers checked without substituting their scope

`OriginalFormalAdmission.declarationFor:40–45` genuinely constructs descriptor
or interface writes for a supplied formal contract and copies the prior view,
eta and witness. `Introduction.description:51–53` obtains that contract from
the Lambda/formal selection, whose original typed telescope is an explicit
input. This is a formal declaration producer, not App descriptor formation.

`ViewPacket:57–65` takes `viewMeaning`, `eta` and `witness` as independent fields
and encodes empty descriptor/interface lists. `localAdmissions:122–132` selects
the formal description/view binder and otherwise delegates to `base.logical`.
`produced_view_admitted:164–170` is relative to that local formal interpretation.
`view_rejects_descriptor_overwrite:414–422` and
`view_rejects_interface_overwrite:424–432` additionally rule out nonempty writes
at that formal view binder. Reusing this API would neither construct App writes
nor discharge the unchanged App admission; coincident raw Site identifiers
would not authenticate the source occurrence.

R159's `app_admission_iff` and R160's `formation_consumer_iff` /
`logical_admission_consumer_iff` settle no required field. They quantify over
supplied `data : Logical s View`, `admissions`, and `original`; R160 explicitly
leaves the witness-preserving interpretation into the descriptor atom and
Logical packet open. Their consumer-only result and rejecting interface model
were not rerun or repackaged as a new attack.

`OriginalSourceValueEntryAdmission.lean:23–60` supplies receipt construction,
four presented invocation operands, unchanged independent template fields and
a two-step source receipt prefix. Its decoder theorem `:65–81` uses the
supplied receipt Current. Its opening boundary explicitly leaves the source
readout/LocalAdmissions law open. None constructs any of the five App logical
fields or authenticates their common solution. No imported, unpinned receipt
module was read.

## Precise derivation boundary and stop

Fix the existing semantic sorts, `inputs`, `readout`, `admissions`, original
kernel `k`, environment `rho`, context `Gamma`, App occurrence and both source
children. Assume `decode readout rho = some state`. For the required original
binder `b = ⟨site,.viewLogic,0⟩`, an actual constructor must produce `d` from
that same inferred solution and complete prior telescope, together with

```text
admissions.logical state b .viewLogic d.
```

The admission definition has the following exact unfolding, rather than a
constructor for that final line:

```text
DataAdmitted inputs readout admissions state b (.logical .viewLogic d)
  = ((.viewLogic.binderKind = b.kind) ∧
       admissions.logical state b .viewLogic d).
```

The kind equation is reflexive. `scopeCandidate` preserves `rho.eventPath`;
`decode_extend` and `Decoded.logical` explain the resulting state once `d` is
supplied. None proves the remaining independent proposition.
`LocalAdmissions.logical`, `OriginalSourceEnvironment.lean:599–600`, is the
exact semantic relation owner; App-local atoms are instead owned by
`OriginalSourceGeneration.Kernel.atom:670–671`. A child derivation in an
already chosen extension constrains that extension; it does not itself provide
an independently legal original logical introduction.

The first construction boundary is therefore already
`Logical.descriptors`, before any claimed completion of `interfaces`,
`viewMeaning`, `eta`, `witness` or admission. The source-level formation owner
is SG §3.1's independently selected Call/descriptor formation, whose §2 locator
names `2026-10-08-native-signature-formation-definition.md`. That defining
source is not a frozen direct input here. This lane does not read it, infer its
contents, or assert that no recipe exists anywhere in the repository.

**STOP at this owner.** This is a bounded authentication failure, not a proof
that the original App rule is false or impossible. No candidate assumption,
conditional theorem or established parent result is introduced. R159/R160 and
R178 already left this premise open; another equivalent interface probe would
leave it untouched. The next method needs actual owning-constructor equations.

## Commands, coverage and disposition

Commands: strict `python3` SHA-256 row parsing/recomputation; exact-path
`cat`, `rg -n`, `sed -n`, `wc -l`; this sole Markdown write and SHA-256 receipt.
One initial `python` invocation failed with exit 127 because that alias is
absent; the identical preflight then succeeded with `python3`. Other observed
source/hash commands exited 0. Some combined display outputs were truncated;
all relied-on equations were obtained by bounded subsequent reads. Hash
verification covers all 17 files; semantic inspection covers the cited regions
and exact-file lexical searches, not every imported module or source case.

No executable semantic experiment, random seed/range, mutation or external
oracle was used. The static reference is the independent original source
rule inventory, with its local semantic laws still explicit inputs. Parser/hash
success authenticates bytes only. No checker assumes transitions and then claims
to prove their source meaning. No Rust path is pinned in this contract, so no
new Rust content was inspected; R178's pinned receipt is historical
correspondence evidence only, not implementation correctness.

No tests, Lean/Lake/Cargo/build/runtime command, cache/environment/scratch
creation, compiler edit, Git operation, central record change or delegation.
Resource envelope: 600 seconds, short serial read/hash processes; exact wall,
CPU and peak RAM were not measured. Work stopped within the bounded packet;
no computation remains running. No theorem was constructed, so no fresh Lean
check or axiom audit was run. Independent review is PENDING.

Recommended next action: primary authenticate and pin the actual original App
descriptor-formation constructor and its same-solution/telescope interpretation,
then assign the constructive bridge to that owner. Keep finite App Checking,
complete Call, whole Build satisfaction, concrete SourceProblem and the shared
`sameScoped` parent OPEN.

Worker state: STOPPED; revision 1 frozen; no outstanding descendant leases.
No further writes or source inspection will occur under this submission.

Commit packet:

- Exact leased/changed path: `tasks/agent-loop/inbox/original-app-admission-r179-source.md`.
- Baseline SHA: `9ee28f082c157fda11d7c5c948decd3798472bbb`.
- Dependency hashes changed: none; all 17 verified hashes listed above.
- Review status: unreviewed bounded source correspondence; R179 BLOCKED,
  original inference soundness parent OPEN.
- Checks already run: strict 17-row parse/full-hash validation twice; bounded
  exact-path source inspection; no tests/build/Lean/axiom audit.
- Proposed commit message: `Record R179 App Logical field ownership blocker`.
- Shared-record deltas left to primary/curator: freeze/hash/review intake,
  STOPPED worker observation, first descriptor constructor owner and blocked
  App admission; preserve all other original parent obligations and leases.
