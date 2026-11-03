# R330 registration leaf handoff

Baseline: `fcce33422`. Owner: `/root/r330_registration`. Source writes stopped.
No Git, compiler, dependency/configuration, root-import or shared-status edits.
No children. Heavy checker slot returned to the primary after the final audit.

## Result and boundary

**PARTIAL / CONDITIONAL, not full GR1 or R159 closure.** The actual selected
R315 Call now has a source-owned static definition record, its computed original
ViewLogic location, a disjoint generated-key resolver, and a real original
`Decoded.logical` / `decode_extend` consumer construction. Readback is derived,
not assumed. No private interfaces-only `Decoded` adapter is constructed.

The actual source registry is `OriginalSourceViewRegistrationR330.register`:
it retains the complete original source `Program` and stores the definition at
the original owner, keyed by `request.generatedResult.key`. `definedLogical`
constructs an original `Logical` payload with a fresh presentation-token type
`Sum View Unit`. Its old descriptors/interface updates, eta and joint witness
are retained verbatim (interfaces embedded with `Sum.inl`); every old view
token is embedded with `Sum.inl`. The one added token reads the stored complete
constructor expression. `logical_registry_correspondence` proves its readout
equals the registry resolver's readout.

The original decoder consumes that payload at the **computed original binder**
using `scopeCandidate`, so its event parents are the same current environment
path. `actual_decoder_generated_view` derives generated readback after actual
`decode`/`Environment.extend`. This theorem requires an ordinarily decoded
prefix environment explicitly over the enlarged presentation-token type.
**Transport of an arbitrary original environment into that type is not proved.**
This is not described as transport of a complete source environment.

## Governing source / unchanged parent

- Authoritative EI definition: `notes/design/2026-10-24-computed-call-result-constructor.md`
  §§2,4,6,9; SHA-256
  `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`.
- GR1 source construction manuscript: `notes/theory/2026-10-24-generated-computed-result-correspondence.md`
  §§1–5; SHA-256
  `58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b`.
  This is the reviewed source mathematics, not blanket production authority.
- Original ViewLogic rule/location: SG §3.3, `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`;
  actual Lean `OriginalScopedClosure.Occurrence`, `Reference.viewLogic`,
  `OriginalSourceEnvironment.Logical`, `Decoded.logical`, `decode_extend`.
- Actual source: R315 `selectedCall origin externalContext`, R314 `Fixture.root`,
  R297 `sourceInventory`. `original_owner_computed` computes ViewLogic row 12;
  `original_call_computed` computes Call row 13. No assumed location equality.
  `original_description_scope` proves the Call is immediately under that same
  binder and retains the seven preceding scopes, route, origin and frame.
- Unchanged parent: `YulangClosure.SourceAppAdmissionR159.app_admission_iff`.
  Arbitrary original inputs/readout/admissions/kernel, environment, context,
  annotation, callee and argument remain quantified. Original annotations,
  all local premises, admission, both source children and the same candidate
  extension remain required. This selected-occurrence construction does not
  replace the whole-language parent by a fixture theorem.

## Independent inputs and exact omissions

`Definition origin declared` requires precisely:

```lean
arms : List (ComputedCallTypedFormationR310.Arm [])
operands : ComputedCallTypedFormationR310.StaticFormation declared
  (OriginalInterfacePreservationR328.Selected.request origin).operands
armFormation : ∀ arm ∈ arms, declared arm.descriptor.key
```

`declared : Key → Prop` is an independent original declaration relation. No
concrete original instance of these fields is invented. `definition_formed`
applies existing `ComputedCallTypedFormationR310.form` to these fields.
This proves syntactic typed formation under its printed premises; it does not
construct concrete semantic declarations or complete EI membership.

Every supplied original arm is retained, including duplicates and arbitrary
arm-local binders. `branchCode` uses `Sum Unit (Fin arms.length)` and stores
each arm's actual `Ref ([] ++ arm.localBinders) .computation`. The full arm
record, including originalScope and tag, remains in `Definition.arms` and the
result expression. No endpoint-only flattening, empty-arm default, arm
membership, final contribution or checking conclusion is supplied as input.

Original synthesis `⟨1, .synthesis⟩`, check `⟨1, .callableImage⟩`, inert argument
Program, CalRet-local argument reference and incidence reference are retained.
Actual CalRet/receiver result-provider/current-world/future **semantic maps**
are not constructed here. Their reference is preserved, not promoted into a
proof of actual tuple incidence.

## Parent application / first remaining premise

`parent_admission_obligation` applies original `admitted_scoped_iff` to this
specific constructed payload and its computed owner. Given ordinary prefix
decoding, the exact remaining original admission obligation is:

```lean
admissions.logical state (owner origin).binder .viewLogic
  (definedLogical old definition)
```

It is not assumed proved. Owner: primary/source logical-admission construction.
After it, R159 still needs all original locals/checks and both source children
in the SAME extended environment. Complete old-environment token transport
also remains with the source-environment owner.

No R306 child is available, and no semantic catalogue equality is asserted.
R293 `branchCatalogue` reads `state.interfaces endpoint`; the generated static
definition is read through the separate key/view-token space. The exact
obstruction `old_endpoint_cannot_read_generated` proves every R328-transported
old endpoint is `inl`, hence cannot equal the generated `inr` interface.
Applying R306 requires genuine EI phase/arm interpretation, a licensed source
child and a justified separate-address consumer/correspondence. Owners:
phase lane for EI/child; primary/source arm owner for dependent arm schemas
and semantic catalogue correspondence. No desired equality is a premise here.

`old_meaning_retained` applies R328's original greatest-fixed-point theorem
for every old query, under arbitrary explicit `Generated` data. This leaf does
not construct those `Generated` data. Kernel acceptance is not independent
review, source-law instantiation, native correspondence or production authority.

## Files and frozen revisions

Only changed proof path:
`notes/theory/lean/YulangClosure/OriginalSourceViewRegistrationR330.lean`
SHA-256 `fd8ea7bed1bc42f5ed6ff32dbf01b812d8967e6cc33a4536ced74bb5710c375e`.
Handoff: this file. Scratch/cache/logs: `/tmp/yulang-r330-source` (237 MiB).

Frozen dependency SHA-256:

- R315: `7adcf88c1ff98c5c4cf23aa788bf5713ddcb949dd09775fb0bd542fe1e2ac577`.
- R328: `0e3ee88f1ac9c4ad4d31a4b6951b0e4bff70725715a70c96ab80f680b6b60857`.
- R310: `077a114bf3f6f190ce4fc125f6113e411b15ea221f8183c6385e51940595ec38`.
- Pin: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- lakefile: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.
- manifest: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
- Final isolated module olean:
  `ab354e1b9d05332ef73e9d97def7732271b373afce08cf648b4977b218b3a83d`.

## Actual checking and retained failures

Toolchain resolved read-only with `elan which lake` (exit 0; existing-version
fallback warning). Native path:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version`: Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`.
Lean: `4.35.0`, `x86_64-unknown-linux-gnu`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.

All builds use isolated `/tmp/yulang-r330-source/project`; no shared cache writes.

1. Initial copy command used an incorrect relative path: exit 1, missing new
   module (`build-1.log`). Corrected to absolute source path.
2. `lake build +YulangClosure.OriginalSourceViewRegistrationR330`: exit 1,
   `build-2.log`; unchanged R315 exceeds default `-M1024` kernel memory,
   followed by secondary universe/constructor diagnostics. This is not a
   mathematical counterexample. Primary explicitly authorized local `-M2048`.
3. `lake env lean -j1 -M2048 -o .lake/build/lib/lean/YulangClosure/OriginalModuleContextBindingR315.olean YulangClosure/OriginalModuleContextBindingR315.lean`
   and the analogous R328 command produced import artifacts, logs
   `dependency-r315.log`, `dependency-r328.log`. First new-module check failed
   (`step-1.log`) on two unsolved simplifier goals; repaired by explicit rewrite
   and constructor discrimination. `step-2.log`: exit 0.
4. Admission reduction initially needed the `DataAdmitted` conjunction made
   explicit (`step-3.log`, exit 1). Repaired with the two implication terms.
   `step-4.log`: exit 0. Final module compilation `step-5.log`: exit 0, no warnings.
5. Bundled `check_lean.py --project /tmp/yulang-r330-source/project --lake <native-lake> --module YulangClosure.OriginalSourceViewRegistrationR330 --theorem YulangClosure.OriginalSourceViewRegistrationR330.actual_decoder_generated_view --timeout 120`:
   exit 1, `helper.log`; same unchanged R315 default-memory failure.
   It removed the prior R315 olean. Manual authorized R315 rebuild restored it,
   exit 0 (`dependency-r315-restored.log`). The first manual audit import failure
   is retained in `audit.log`; subsequent 22-root audit passed (`audit-2.log`).
6. Final reusable audit `/tmp/yulang-r330-source/YulangProofAudit.lean` was
   generated with the skill checker's unchanged `audit_source` for ALL 23
   authored theorems, including declaration-kind and axiom-whitelist checks.
   `lake env lean -j1 -M2048 --root=/tmp/yulang-r330-source /tmp/yulang-r330-source/YulangProofAudit.lean`:
   exit 0, `audit-final.log`. The unchanged skill `validate_audit` accepted all
   23 ordered full types and complete axiom reports. No default/full integration
   build is claimed. The primary retains integration checking ownership.

Complete fully qualified theorem inventory: `theorems.txt`; complete printed
types and axioms: `audit-final.log`, both under `/tmp/yulang-r330-source`.
All theorem names are under `YulangClosure.OriginalSourceViewRegistrationR330`.

Exact axiom groups:

- `every_old_resolution_retained`, `old_endpoint_cannot_read_generated`: `[]`.
- `old_meaning_retained`: `[propext, Quot.sound]`.
- All other 20 authored theorems: `[propext, Classical.choice, Quot.sound]`.

Changed-source search for `sorry`, `admit`, `axiom`, `skipKernelTC`,
`native_decide`: no matches. Transitive audits contain no `sorryAx`, project
axioms or unchecked native assumptions. Primary-approved per-process cap:
`-j1 -M2048`; total packet bound 1800 s. Peak OS RSS was not measured.
Proof/source review and any promotion remain independent primary-owned gates.

Writes stopped after this handoff. No background Lean processes remain.
