# Sprint R180 — authenticate App descriptor formation

Status: admitted primary continuation of the unchanged Yulang type/effect
inference-soundness goal. Baseline: `yulang3` at `b9d831177bb8a6d7fb95950f263781fbf851d342`.
The parent remains original `SourceProblem.InferenceSoundness`, with its full
quantifiers and one shared same-solution `sameScoped` witness. Rust runtime and
general Rust-program correctness are out of scope.

## Fixed outcome

Authenticate the actual original source owner for App descriptor/profile
formation and determine whether it supplies a constructor equation that can be
interpreted as the App `Logical.descriptors` writes under the same inferred
solution, complete prior telescope and genuine callee/whole-inert-argument
children. Trace that equation to the unchanged
`LocalAdmissions.logical state binder .viewLogic data` premise. Produce either:

1. a source-owned constructor-to-consumer derivation with the exact same-solution
   and telescope equalities needed for an eventual Lean construction; or
2. the first exact missing equation in the defining owner, classified as a
   specification/formalization gap, with the precise authority needed to close
   it.

A stored descriptor readout, renamed atom, free descriptor parameter, circular
admission assumption, per-call witness, new kernel or application of R159/R160
consumer iff lemmas does not meet this outcome. R179 remains CLOSED_INCOMPLETE;
this work neither proves nor refutes the parent theorem.

## Required derivation

Map the source-owned signature constructors and their complete constituent
partitions to:

1. the descriptor writes at the actual App endpoint;
2. the original atom
   `.descriptorFormation site Γ [callee.site, argument.site]`;
3. the unchanged App `LocalAdmissions.logical` premise; and
4. preservation of the complete prior telescope and the same solution's
   assignment and joint witness.

Do not infer the contents of a cited source from its filename or citation. If
the defining document imports an additional owner, stop before reading it and
request one sequential contract revision. Rust implementation owners remain
out of scope; the R178 owner trace is frozen evidence and no additional Rust
inventory is authorized.

## Frozen direct inputs

Before content reads, count these 23 rows separately, require one exact path and
one full 64-hex SHA-256 per row, and verify every digest. Any mismatch or
additional owner stops the lane for sequential primary admission.

- `notes/design/2026-10-08-native-signature-formation-definition.md` —
  `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` —
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` —
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `notes/theory/lean/YulangClosure/OriginalAppConstructionR160.lean` —
  `a7a766ef1d733719bfc4145bdcc9051e2e9e64521feb3fa400877a60bf9cb793`
- `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean` —
  `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- `tasks/agent-loop/sprints/original-app-admission-r179.md` —
  `30bd50b1886d9b390ab290051b9d2926552b7dc45aa5a17ff47c35cde25e42aa`
- `tasks/agent-loop/history/original-app-admission-r179-outcome.md` —
  `97f0ef1fceaf96b73e55b8c08e0f7e2c000bf4593fc090ef3bf348136fede8a3`
- `tasks/agent-loop/inbox/original-app-admission-r179-proof.md` —
  `7180e445a11fa926b52081677d3f917a6f30a5bca40278e533230b6cf95528d7`
- `tasks/agent-loop/inbox/original-app-admission-r179-source.md` —
  `796ef47418f2c72f2fb0824585672bca8b05859c4d61c3575ba7b28b24a692f7`
- `notes/theory/2026-10-08-source-signature-incidence-construction.md` —
  `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`

- `notes/theory/2026-10-08-call-source-interface-construction.md` —
  `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` —
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/theory/2026-10-07-call-input-construction-proof.md` —
  `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6`
- `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` —
  `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe`
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` —
  `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`
- `notes/design/2026-10-02-parametric-component-linking.md` —
  `108fb9ab91c79aedc716ae476a07d567447644892ae1e32671c8fa4bce96efca`
- `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` —
  `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`

## Revision 2 — sequential owner admission

Revision 1 stopped before reading the selected incidence-construction owner.
The pinned native-signature-formation definition explicitly delegates its
actual constructor grammar to this file (§§2–6). Primary verified its exact
path and SHA-256 above before admitting it as the 16th direct input. The
producer digest `e698ad0467a6986029f5f5d21ff3e0bf8a2cc836c9410f1fa0be4b717be915d2`
reported in that definition is a referenced producer artifact identity, not
the filesystem SHA-256 of the admitted document. Both lanes must authenticate
their dependencies again under this revision and send fresh ACKs before
resuming content reads. Further imported owners require another sequential
revision.

## Revision 3 — sequential Call/interface owner admission

Revision 2 authenticated the incidence-construction owner, which explicitly
delegates actual App/Call field injection to the selected Call source-interface
construction and cites the source contracts/common allowance as primitive
source judgments. The source lane independently located both as direct
dependencies of the complete App formation recipe. Primary verified the exact
paths and filesystem SHA-256 values above before admitting them as inputs 17
and 18. Revision-2 handoffs are frozen at proof SHA
`d6be2efc35c84407b9ab3c90c9f7a852464900a35b9d04aad3975918dd017388` and source
SHA `36aeba9d538c93cbcd6f9875c02dd3075cb7735f54640bb33fa326c7cc56b2ed`.
Both lanes must authenticate all 18 inputs again under this revision and send
fresh ACKs before reading the two newly admitted owners. Any further imported
owner requires another sequential revision.

## Revision 4 — sequential original constructor-owner admission

Revision 3 handoffs are frozen at proof SHA
`9a864d4fe99bc22f8672fa404f6f20dce9e65be0652cf120f371e14cb03657f0` and source
SHA `b6e68eb4def92d2332a47e515dd9d8674782b853d7d53dd6dafa5bffe7d0af8d`.
The admitted Call/interface and source-contract documents identify two further
defining owners: Theorem S §§3–4 for actual Application origins, and theorem C
for the source graph. Both lanes stopped before reading either owner. Primary
verified the exact filesystem paths and SHA-256 values above, admitting them
as inputs 19 and 20. Both lanes must authenticate all 20 inputs under this
revision and send fresh ACKs before reading the newly admitted owners. Any
further imported owner requires another sequential revision.

## Revision 5 — sequential computation-semantics owner admission

Revision 4 handoffs are frozen at proof SHA
`b560c2a2720f02766ee31dc30257a7e96971c8e8122e158537fd32ac2bf810dd` and source
SHA `7060df74f7fe5d6e7f266e4e4e9524c6c0a156312241795908d662fa47bb68bc`.
Both identify the typed-computation core as the owner of source translation,
tags and semantic typing used by Theorem S and theorem C. The source handoff
also identifies the joint-hiding law as an owner for theorem C. Both lanes
stopped before reading these files. Primary verified their exact paths and
SHA-256 values above, admitting them as inputs 21 and 22. Both lanes must
authenticate all 22 direct inputs and send fresh ACKs before reading either
new owner. Any further imported owner requires another sequential revision.

## Revision 6 — sequential scope-charter admission

Revision 5 handoffs are frozen at proof SHA
`fc68780b93d64f0772916d90ecc6501502ed3e7f1eb5454108acde0b390c7724` and source
SHA `d4179f61e3dfa46584b8915d3b384e36243e4bb4ead9b951c1315166d2cb0fd8`.
The proof lane cites charter §§19–20 as the owner of rigid/hidden packet scopes
used by the admitted joint-linking law. It stopped before reading that file.
Primary verified its exact path and SHA-256 above, admitting it as input 23.
Both lanes must authenticate all 23 direct inputs and send fresh ACKs before
reading those clauses. Any further imported owner requires another sequential
revision.

## Lanes, outputs and limits

- Proof correspondence: one registered `lean_prover`, 900 seconds, initially
  read-only. Sole output `tasks/agent-loop/inbox/app-descriptor-formation-r180-proof.md`.
  It may write `notes/theory/lean/YulangClosure/AppDescriptorFormationR180.lean`
  only if a theorem is actually constructible from the frozen equations. If no
  theorem is constructed, run no Lean/Lake/version/build/check command.
- Source correspondence: one registered `researcher`, 600 seconds, read-only.
  Sole output `tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`.
  Authenticate the cited owner clauses and map their constructors to the Lean
  consumer. No Rust inspection or compiler edits.
- Fresh independent exact-conformance review: 300 seconds after outputs freeze.
- Existing `.lake` is the only possible Lean environment. No new cache,
  environment, scratch, Cargo, tests, runtime, build, or source implementation
  changes.

Luna owns exact leases, hash acknowledgements, review, adjudication, central
state, exact staging, commit and push. Preserve all UNKNOWN worker rows and
quarantined paths. Keep the parent OPEN.
