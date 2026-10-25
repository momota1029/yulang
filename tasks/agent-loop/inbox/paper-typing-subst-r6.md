# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r6 — frozen unfinished proof handoff

Assignment: R6 proof lane; revision 1. Contract SHA-256
`7c3fe39c2a3bb9bd77425129751a09e46e80c63c50a72cdbd1215e7726c04bb7`.
Setup supplied by primary: `18ba53220`; no Git commands performed by this leaf.
Worktree: `/tmp/yulang-r6-paper-record-proof` only.
Runtime task identity observed in delivery: `/root/r6_record_proof`.
Requested role: lean_prover; effective model/effort: UNKNOWN (no runtime model metadata).
Author: this leaf only; no children. Outcome: constructed, FAILED_CHECK, not proved.
Independent review: NOT_RUN; source/native correspondence and production authority: OPEN.

## Original claim and authority

Original unchanged parent: `docs/yulang-operational-type-safety-ja.tex:953-977`,
substitution lemma item 2: one arbitrary type substitution acts simultaneously on
declaration instances, environment, plans, all payload/response types and result,
preserving full paper typing. Record rules: :217-231; record code lemma: :724-749.
Opening correction :56-63 states that the manuscript's machine does not establish
source-owner correspondence after the raw-resume correction. This work claims
no machine simulation, source/native bridge, executor safety, inference A/B closure
or authoritativeness of research drafts.

Verified admission hashes:
- paper: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- syntax baseline: `2c2f7efac389488cdebee22fb5c6c666b183f7c200fd3ffec73c9c2fb41ae81d`
- typing baseline: `f29c00981f9abaf29051021570088b77cc031b191d9429f7e15d4210f992a313`
- PaperTypeFormation: `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- PaperTypeSubstitution: `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`
No dependency, root import, configuration, toolchain or compiler edits.

## Rule mapping and coverage

All names below are in `YulangClosure.PaperTypes`.
`RecordShape` traverses a record type, retaining ordered declaration labels and
its required-label subset, with uniqueness; payload types have no extra formation
premise. `RecordField` gives a declared field's label, Presence and payload type
using here/there membership, independent of runtime ordering.
`RecordPayloadsTyped` traverses present runtime entries, requiring RecordField
membership plus actual PaperValueTyped payload evidence. Hence actual domain is
contained in declared domain. `PaperValueTyped.record` additionally requires
actual-label Nodup and every required label in the actual domain. No list-order
equality or condition demanding optional fields was introduced.
`PaperComputationTyped.field` requires RecordField with `.required`;
`.lookup` requires any declared Presence and returns `.union (.base .unit) fieldType`.
`Bad` remains absent from Computation and has no typing constructor.

The raw existing Value.record Presence tag is retained by mapRecordFields but is
not equated with declaration presence: paper :150-153 has runtime entries l=v,
not such tags. Its interpretation is an unresolved syntax correspondence.
RecordFormed.subst was inspected and deliberately not applied: it needs subScope
(formed substitution payloads), absent from the original arbitrary-σ theorem.
RecordShape makes no claim of payload formation at an ambient scope. No stronger
substitution hypothesis was added and no target typing premise was assumed.

Represented inductive coverage after edits: 14 value constructors, 7 computation
constructors, ValuesTyped nil/cons, ValuesAllTyped nil/cons, RecordPayloadsTyped
nil/cons; RecordShape nil/required/optional and RecordField here/there.
The five mutual substitution constructions cover each listed constructor but fail
checking below. Record introduction, field and lookup are not delivered as proved.
Omitted full-paper cases remain variants, nominals, wrap, polymorphism, roll/unroll,
choose/unionCase/absurd, tuple split, primitive/template declarations, patterns,
operations/handlers/mappers, recursive bindings and guarded graphs, continuations,
resume and administrative forms. The record code lemma's generated branch/adapter
program is also not formalized here; no source->constraints->propagation->consumer
or Rust native execution correspondence was established.

## Parent application and exact residual

There is no accepted extended mutual substitution theorem to apply to the parent.
Independent record support terms `RecordShape.subst`, `RecordField.subst`, and
`mapRecordFields_labels` produce clean printed axiom lists in the failed-module
run, and reduce the proposed record case to payload transport plus raw list-map
alignment. They are not a successfully built deliverable module.
First actual residual at PaperValueTyped.subst's record case: the source mapping
uses `fields.attach.map` and the constructor proof uses `fields.map`; the current
`simpa [mapPaperValue, mapRecordFields]` does not identify them. A targeted theorem
for the subtype-erasing map is needed. Separately the kernel reports an application
mismatch at RecordPayloadsTyped.subst (line 94 in checked snapshot), with different
environment/recordType indices in the recursive projection. Do not presume that
it disappears when the earlier elaboration failure is repaired.
Owner: primary proof intake; next bounded task is repair these two actual failures,
build, and audit the five mutual results without sorryAx/project dependencies.
After that, the original parent's first remaining obligation is all omitted paper
rules/shared indices plus full source judgment correspondence, owned by the primary
full-paper proof lane. Fresh independent review remains required.

## Commands, versions, resources and failures

Read-only resolution, project cwd:
`elan which lake` -> `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` (exit 0).
Native path abbreviated below as LAKE; no proxy execution or install.
1. `LAKE --version`: exit 0, Lake 5.0.0-src+eb6cafb (Lean 4.35.0).
2. `LAKE env lean --version`: exit 0, Lean 4.35.0, x86_64-unknown-linux-gnu,
   commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
3. `/usr/bin/time -f 'ELAPSED=%e EXIT=%x' timeout 30s LAKE build +YulangClosure.PaperExecutionTypingSubstitution`:
   exit 1, 19.46s. Dependency and syntax modules built. Unresolved required-label
   implicit and RecordPayloadsTyped.subst kernel mismatch.
4. Same build with timeout 20s: exit 1, 1.33s. A preceding Python repair command
   used the project cwd with a repository-relative path and failed FileNotFoundError,
   leaving bytes unchanged; the build repeated the same failure. No failure hidden.
5. `timeout 20s LAKE --no-cache build +YulangClosure.PaperExecutionTypingSubstitution`
   under the same time command: exit 1, 0.84s. Explicit constructor pattern omitted
   its leading environment index; corrected the pattern before attempt 6.
6. Same --no-cache build: exit 1, 0.84s. Attached-list map mismatch plus kernel
   mismatch remain. Full printed types and axiom lists are preserved below.

6/6 serial Lake invocations including both version probes; checker wall time
22.47s from build time receipts, plus versions (<1s observed tool wall).
Each build's Lean command explicitly used project `-j1 -M1024`; one cache owner,
no concurrent Lean processes. Active cognitive wall time is not machine-measured;
no fabricated CPU/RSS receipt. Finite invocation bound reached; no additional check.
Skill checker CLI full run was not used because its four extra calls would exceed
remaining budget. Its source was inspected; manual #check/#print axioms used instead.
No helper whitelist PASS is claimed. Failed audits explicitly contain sorryAx and
a generated failed declaration dependency, so the mutual results are rejected.

Audit commands were temporary in the checked source to combine build and audit;
they are now preserved in `.lake/R6AuditCommands.lean`, removed from the deliverable.
`.lake/R6FailedModule.lean` preserves the exact last checked source bytes. The final
source differs only in removing audit commands and an accurate unfinished header;
it has not been checked again. No repair after the call bound is presented as checked.
No literal sorry/admit, project axiom or kernel bypass was written.

## Artifact and scratch hashes

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e44ca4b6a4b7afaeaa1232b5bb3d5a4702a75e74ccc58c8924ccf3ed1fe34ffc`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `23fafc22d33f9b9bf7f695e7ba8a53671c7bfd26c286643eea30bfc4dc4e438e`
- `notes/theory/lean/.lake/R6FailedModule.lean`: `4a4c6b1e2f58edf7ab87cd77867b08a52645f9e18368beff5955aaff69c04e16`
- `notes/theory/lean/.lake/R6AuditCommands.lean`: `306e9d51942af0464abea6b8ad66cc11c3625b3d5eacd7f7405eee1c9755c3c4`
- `notes/theory/lean/.lake/r6-build1.log`: `e7bd58f756621ea9b8b0489307fb3ce88ff42c92139ad6ef5dec43aee87adc62`
- `notes/theory/lean/.lake/r6-build2.log`: `2fbc0741dcba87a62dbcaa9f09262ab2e43fee2cc0e6b57d3b844516aad37b89`
- `notes/theory/lean/.lake/r6-build3-audit.log`: `bd640744d9a3dc97857275dd7327353cef9be3a6db355c2f9ab14d052d2a0b7b`
- `notes/theory/lean/.lake/r6-build4-audit.log`: `607ba03d4962709778a5749ee27f2211a46bfa18d9f49816db857c9a237ecb95`

Generated/build manifest: `notes/theory/lean/.lake/r6-generated-files.txt`
(SHA-256 `728b17393f08b4c8ad18dec17f12b9606ee361d41ae00274f1558cfd81b3cd06`), lists owned cache/generated
outputs with hashes. Scratch is restricted to that worktree's `.lake` tree:
four r6-build logs, R6FailedModule.lean, R6AuditCommands.lean, generated build/lib,
build/ir, lakefile cache and this manifest. No main-checkout writes.
Exact leased persistent edits are the two Lean paths above and this handoff file.

## Complete final failure/type/axiom evidence

```text
error: YulangClosure/PaperExecutionTypingSubstitution.lean:138:8: Type mismatch: After simplification, term
  PaperValueTyped.record (RecordShape.subst σ shape) unique' required'' (RecordPayloadsTyped.subst σ payloads)
 has type
  PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
    (mapTypeEnvironment σ environment)
    (Value.record
      (List.map (fun (field : Label × Presence × Value) => (field.fst, field.snd.fst, mapPaperValue σ field.snd.snd))
        fields))
    (subst σ ty)
but is expected to have type
  PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
    (mapTypeEnvironment σ environment)
    (Value.record
      (List.map (fun (x : { x // x ∈ fields }) => (x.val.fst, x.val.snd.fst, mapPaperValue σ x.val.snd.snd))
        fields.attach))
    (subst σ ty)
error: YulangClosure/PaperExecutionTypingSubstitution.lean:94:10: (kernel) application type mismatch
  x✝.1 fields
argument has type
  RecordPayloadsTyped declarations graphTypes environment fields✝² recordType
but function has type
  RecordPayloadsTyped declarations graphTypes environment✝ fields✝² recordType✝ →
    RecordPayloadsTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment✝) (mapRecordFields σ fields✝²) (subst σ recordType✝)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:192:0: YulangClosure.PaperTypes.argsSyntax_subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (types : List YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.argsSyntax (List.map (YulangClosure.PaperTypes.subst σ) types) =
    YulangClosure.PaperTypes.subst σ (YulangClosure.PaperTypes.argsSyntax types)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:193:0: 'YulangClosure.PaperTypes.argsSyntax_subst' depends on axioms: [propext]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:194:0: YulangClosure.PaperTypes.literalType_subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (literal : YulangClosure.PaperTypes.Literal),
  YulangClosure.PaperTypes.subst σ (YulangClosure.PaperTypes.literalType literal) =
    YulangClosure.PaperTypes.literalType literal
info: YulangClosure/PaperExecutionTypingSubstitution.lean:195:0: 'YulangClosure.PaperTypes.literalType_subst' does not depend on any axioms
info: YulangClosure/PaperExecutionTypingSubstitution.lean:196:0: YulangClosure.PaperTypes.lookupTypeEnvironment_subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (environment : YulangClosure.PaperTypes.TypeEnvironment) (index : Nat),
  YulangClosure.PaperTypes.lookupTypeEnvironment (YulangClosure.PaperTypes.mapTypeEnvironment σ environment) index =
    Option.map (YulangClosure.PaperTypes.subst σ) (YulangClosure.PaperTypes.lookupTypeEnvironment environment index)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:197:0: 'YulangClosure.PaperTypes.lookupTypeEnvironment_subst' does not depend on any axioms
info: YulangClosure/PaperExecutionTypingSubstitution.lean:198:0: YulangClosure.PaperTypes.lookupGraphEnvironment_subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (environment : YulangClosure.PaperTypes.GraphEnvironment) (index : Nat),
  YulangClosure.PaperTypes.lookupGraphEnvironment (YulangClosure.PaperTypes.mapGraphEnvironment σ environment) index =
    Option.map (YulangClosure.PaperTypes.subst σ) (YulangClosure.PaperTypes.lookupGraphEnvironment environment index)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:199:0: 'YulangClosure.PaperTypes.lookupGraphEnvironment_subst' depends on axioms: [propext]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:200:0: YulangClosure.PaperTypes.RecordShape.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {recordType : YulangClosure.PaperTypes.Ty} {labels required : List YulangClosure.PaperTypes.Label},
  YulangClosure.PaperTypes.RecordShape recordType labels required →
    YulangClosure.PaperTypes.RecordShape (YulangClosure.PaperTypes.subst σ recordType) labels required
info: YulangClosure/PaperExecutionTypingSubstitution.lean:201:0: 'YulangClosure.PaperTypes.RecordShape.subst' does not depend on any axioms
info: YulangClosure/PaperExecutionTypingSubstitution.lean:202:0: YulangClosure.PaperTypes.RecordField.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {recordType fieldType : YulangClosure.PaperTypes.Ty} {label : YulangClosure.PaperTypes.Label}
  {presence : YulangClosure.PaperTypes.Presence},
  YulangClosure.PaperTypes.RecordField recordType label presence fieldType →
    YulangClosure.PaperTypes.RecordField (YulangClosure.PaperTypes.subst σ recordType) label presence
      (YulangClosure.PaperTypes.subst σ fieldType)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:203:0: 'YulangClosure.PaperTypes.RecordField.subst' does not depend on any axioms
info: YulangClosure/PaperExecutionTypingSubstitution.lean:204:0: YulangClosure.PaperTypes.mapRecordFields_labels : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)),
  List.map Prod.fst (YulangClosure.PaperTypes.mapRecordFields σ fields) = List.map Prod.fst fields
info: YulangClosure/PaperExecutionTypingSubstitution.lean:205:0: 'YulangClosure.PaperTypes.mapRecordFields_labels' depends on axioms: [propext, Quot.sound]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:206:0: YulangClosure.PaperTypes.ValuesTyped.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {values : List YulangClosure.PaperTypes.Value}
  {types : List YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.ValuesTyped declarations graphTypes environment values types →
    YulangClosure.PaperTypes.ValuesTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (List.map (YulangClosure.PaperTypes.mapPaperValue σ) values) (List.map (YulangClosure.PaperTypes.subst σ) types)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:207:0: 'YulangClosure.PaperTypes.ValuesTyped.subst' depends on axioms: [propext, sorryAx, Quot.sound]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:208:0: YulangClosure.PaperTypes.ValuesAllTyped.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {values : List YulangClosure.PaperTypes.Value}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.ValuesAllTyped declarations graphTypes environment values ty →
    YulangClosure.PaperTypes.ValuesAllTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (List.map (YulangClosure.PaperTypes.mapPaperValue σ) values) (YulangClosure.PaperTypes.subst σ ty)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:209:0: 'YulangClosure.PaperTypes.ValuesAllTyped.subst' depends on axioms: [propext, sorryAx, Quot.sound]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:210:0: YulangClosure.PaperTypes.RecordPayloadsTyped.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)}
  {recordType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.RecordPayloadsTyped declarations graphTypes environment fields recordType →
    YulangClosure.PaperTypes.RecordPayloadsTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment) (YulangClosure.PaperTypes.mapRecordFields σ fields)
      (YulangClosure.PaperTypes.subst σ recordType)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:211:0: 'YulangClosure.PaperTypes.RecordPayloadsTyped.subst' depends on axioms: [propext,
 Quot.sound,
 YulangClosure.PaperTypes.RecordPayloadsTyped.subst._f]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:212:0: YulangClosure.PaperTypes.PaperValueTyped.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {value : YulangClosure.PaperTypes.Value}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value ty →
    YulangClosure.PaperTypes.PaperValueTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment) (YulangClosure.PaperTypes.mapPaperValue σ value)
      (YulangClosure.PaperTypes.subst σ ty)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:213:0: 'YulangClosure.PaperTypes.PaperValueTyped.subst' depends on axioms: [propext, sorryAx, Quot.sound]
info: YulangClosure/PaperExecutionTypingSubstitution.lean:214:0: YulangClosure.PaperTypes.PaperComputationTyped.subst : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {computation : YulangClosure.PaperTypes.Computation}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment computation ty →
    YulangClosure.PaperTypes.PaperComputationTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (YulangClosure.PaperTypes.mapPaperComputation σ computation) (YulangClosure.PaperTypes.subst σ ty)
info: YulangClosure/PaperExecutionTypingSubstitution.lean:215:0: 'YulangClosure.PaperTypes.PaperComputationTyped.subst' depends on axioms: [propext, sorryAx, Quot.sound]
Some required targets logged failures:
- YulangClosure.PaperExecutionTypingSubstitution
error: build failed
Command exited with non-zero status 1
ELAPSED=0.84 EXIT=1
```

## Stop receipt

Writes STOPPED after completing this handoff. No active checks, children, Git
operations or background processes remain. No lease transfer/release, promotion,
review appointment, or self-certification. Pending review/integration; failed proof
must be repaired in a new primary-authorized envelope.
