# Handoff: module entry provenance data contract

Sprint-ID / contract revision and SHA-256:
`module-reference-materialization-20261017` / rev2 /
`64c89cb6566de76cfaca4cf483ae278d16720962358db1ec6a2d016d9e11aa77`

Assignment-ID / handoff revision: `module-entry-provenance-contract` / 3
Supersedes handoff rev2 SHA-256: `d0792931b02763c4722de532309109422035bf0dbf71986efe6c7d5210e0a5fb`
Primary acknowledgement: rev2 intake accepted; this revision adds the reviewed semantic-image/bookkeeping boundary and updates the frozen contract pin.
Parent gate: `HINTRO-OWNER-u_id` under adopted ModuleEnv-Expose*; source/native
correspondence and original §7.2(2) remain distinct.
Baseline: `2b563076a0ac2c4f0b66a277c1b557dac8134313`.
Role / worker: Luna primary `/root`; actual model/runtime metadata UNKNOWN.
Output lease: `notes/design/2026-10-17-module-entry-provenance-contract.md` (rev2 SHA-256 `44f33397a45f5d17a0302c6b1efbfe1f7bbdf018caed2ece2acc18176a746bd9`) and
this handoff only.

## Result and parent application

The fixed occurrence proof and both fresh application reviews are complete; Luna
adjudicated the local HINTRO owner as supplied under adopted authority. This
artifact identifies actual native source/module-use producers and consumers,
then specifies the minimum source/native records required by the adopted rule. It does not supply
the source `Sig`, environment transport constructor, `Phi_u` or registered
Call root. Therefore original conditions closed: **0**; implementation remains
unleased.

## Exact source-to-native evidence

`candidate_source.rs` retains ModuleDef `parent,target,occurrence` and queues
`Action::Module`; execution routes an active use to `route_candidate_open_use`
and other uses to `route_incoming`. `candidate_call.rs` observes a direct
ModuleDef callee target but leaves
`ModuleNameSourceTypingAndAdmission` and
`ModuleUseReceivingExportCorrespondence` pending. The native FreshUse remap
retention proof remains limited to GraphState lifetime.

Required data and the missing exact owners are tabulated in the frozen design
artifact. The key discriminant is that each entry keeps its real owner:
Published, Family, Mono, Alias or Live. A target ID or route cannot choose it.

## Remaining premises and next step

1. Architecture review found the contract coherent as a readiness contract, not an implementable design; no safe code slice was established. It caught the stale rev2 sprint pin in handoff rev1; rev2 corrects it and clarifies semantic-image correspondence excludes ordinary native bookkeeping.
2. The local fixed-source proof was independently reviewed CLEAN by compiler and spec auditors; it supplies only HINTRO under adopted formation authority.
3. No code until the exact inherited UNKNOWN implementation lease is resolved and a concrete source producer exists. No compiler tests/builds were run or authorized by this packet.

The adoption adds source formation authority; whole-source admission/observation
equivalence remains open. Registered root, complete Call, source/native fields,
N-Transport, F1/FK1, soundness, principality and termination remain open.

Artifact class: bounded source/native data contract, not implementation, proof
or production authority. No descendant, tests, probes, Git or external contact.
Writer: STOPPED after Luna freezes and hashes this handoff.
