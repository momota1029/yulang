# R305 proof lane — missing source formation inputs

Outcome: **BLOCKED** at source construction. The unchanged R159 parent remains
OPEN, with **no parent-edge reduction or closure claimed**. One narrow constructor
obstruction theorem is kernel checked; it does not formalize or refute EI-All.
Fresh independent review remains the primary's responsibility. No production
semantic authority, compiler changes, Git operations or descendants.

## Parent and authority

Unchanged parent: `YulangClosure.SourceAppAdmissionR159.app_admission_iff`.
Its arbitrary original `context`, `mark` (both annotation alternatives), `callee`
and `argument` are retained. The existential occurrence, Logical data and decoded
state share the SAME ViewLogic extension for every local and both children.
`admissions.logical` remains an independently interpreted input relation.

Frozen baseline supplied by primary: `f961b6d7c`. All four named Lean direct
input hashes R159/R293/R302/R304 match the sprint contract. The generated source
and import-cone manifests are listed below. Relevant original authorities read:

- Source generation G (`2026-10-06-source-call-generation-construction.md`),
  §§3,5–7: existing image→original Comp target checking; profile P and independent
  initial challenge admission A remain separate.
- SG (`2026-10-08-source-generalize-definition-and-proof.md`), §§3.1–3.3,
  §5.2: source operands, original local laws, and actual ViewLogic/event scope.
- Selected IF (`2026-10-08-call-source-interface-definition.md`), §§2–4,
  with the construction manuscript §§2–3 and original Call cases: authentic
  declaration contracts, IF-Insert and IF-Use; static slots grant no licenses.
- Authoritative EI (`2026-10-24-computed-call-result-constructor.md`),
  §§2–5,9: typed EI-Form/EI-Tail-Form, phase clauses, all original arms and
  genuine introduction evidence. The retained Name specialization is not
  generalized to computed callees.
- `2026-10-24-generated-computed-result-correspondence.md`, §§1–5,
  DefineResultView/GR1/GR3/GR5: typed original operands, q_c registration,
  same actual return/future slots, separate fixed target check. Its opening
  historical review wording is qualified by its final independent-review receipt;
  the selected EI definition is the semantic authority, not a research draft.

## Exact source trace and first missing inputs

`OriginalSource.Source.app` has only mark/callee/argument.
`OriginalSourceEnvironment.sourceCallOwners` traverses actual `sourceRules`;
its `CallOwner.application` stores site/context/callee-site/argument-site.
`CallOwner.initialGoal` recovers the original returned-callee→descriptor
**value** check. It stores no declaration/whole-Call-arm family.
`LogicalOccurrencesR104.appRule` has the five original atoms, conditional
singleton-formal origin, original value and computation checks, and both
arbitrary source children. An atom labelled descriptorFormation is a consumer
of original kernel evidence; it is not an EI constructor.

`SourceSignatureConstruction.Node.call` takes `CallNodes`, local introductions
and a result `Catalogue` as INPUTS. `CallNodes.arms` stores Nat graph indices,
not the original complete arm descriptors, their endpoint correspondence or
formation derivations. `SourceSignatureConstruction.build` maps `compileNode`
over an already supplied graph. It constructs neither source→graph nor its
catalogues. A genuine finite declaration graph with typed reference-use and
insertion data is not an input to the current raw `Source`/CallOwner inventory.

The **first missing owner input** to actual EI-All formation is the source-owned
typed complete Call interface/declaration graph required by GR1 §2 (1–4):
callee C_f/Return A_f; checked F_c and independent D_c/I_c/P_c; the inert
argument formation/checking-obligation schema dependent on actual CalRet b;
and every actual whole-Call arm's complete descriptor, scope, tag and output
map. The current raw inventory cannot enumerate these semantic arms. In
particular, substituting source case/catch arm syntax would conflate different
constructors; no such substitution was made.

After those genuine inputs, the missing **constructor/interpretation** is
EI-Form/EI-All-Form with DefineResultView's registered q_c at the actual source
description region and full phase-to-IF result/future correspondence.
`s.Interface` and `s.Observation` are abstract sorts; `RawObservation` stores
only observation/event. `Inputs.traceForm` exposes pureReturn/unfinished, and
`Inputs.observationFields` is an independently supplied callback. No existing
operation recovers actual CalRet/Delay/receipt/receiver/resume/future binders
or builds their required staged EI clause equations from these data. A new
abstract record assuming the desired equations, a free arm list, or relabelling
callableImage as EvalInvoke would leave the same input obligation untouched.

Owner: primary/source-interpretation and source-declaration-construction lane.
A future packet needs concrete typed original declaration inputs and their
translation into the existing environment before a faithful EI instance can
be built. This is not evidence that EI is false or that any supported source
case should be removed.

## Actual construction/application attempts

R293 `sourceContribution`/`armContribution` require (a) the genuine child
catalogue equation, (b) genuine child contribution/license and (c) lookup of
`unionNode = Node.alternative ... unionCatalogue`. They preserve source versus
arm tags, overlaps and the complete same raw tuple; those constructions remain
useful under their actual inputs.

The checked theorem below proves an actual `Node.call` lookup cannot supply
(c) at the same graph index, for arbitrary catalogues, arms, children and
annotations. This prohibits only a direct constructor cast; it does not exclude
adding a genuinely constructed separate EI alternative node.

`/tmp/yulang-r305-proof/project/AttemptR293.lean` applies the ACTUAL
`sourceContribution` after granting its child packet and catalogue equation
solely to isolate the remaining failure. Lean exits 1 at `found`:

```text
cwd: /tmp/yulang-r305-proof/project
command: ['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--no-cache', 'env', 'lean', '-j1', '-M1024', 'AttemptR293.lean']
exit: 1
AttemptR293.lean:28:56: error: Application type mismatch: The argument
  found
has type
  graph.node index =
    some (Node.call context mark callee argument nodes locals (unionCatalogue inputs state scope source arms))
but is expected to have type
  graph.node index = some (unionNode inputs state scope site left right source arms)
in the application
  sourceContribution inputs state scope site source arms graph original operators index left right raw childNode
    sameCatalogue packet found
```

No partial proof or granted premise from that failing diagnostic is delivered
as source formation. The analogous arm constructor has the identical required
union-node lookup; no second equivalent proof route was attempted.

`/tmp/yulang-r305-proof/project/AttemptR159.lean` applies the actual unchanged
`app_admission_iff.mpr` without assuming any source/local/admission conclusion.
Lean exits 1 with the following first residual goals (full repeated trace in log):

```text
cwd: /tmp/yulang-r305-proof/project
command: ['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--no-cache', 'env', 'lean', '-j1', '-M1024', 'AttemptR159.lean']
exit: 1
AttemptR159.lean:15:57: error: unsolved goals
case refine_1
s : Sorts
View : Type
inputs : Inputs s
readout : RuntimeReadout s View
admissions : LocalAdmissions s View
original : Kernel (Payload s View)
environment : Environment (Payload s View)
context : Context
mark : Mark
callee argument : Source Category.expression
⊢ ∀ (premise : Premise),
    premise ∈ annotationPremises context mark →
      Local (admissionKernel inputs readout admissions original) environment premise

case refine_2
s : Sorts
View : Type
inputs : Inputs s
readout : RuntimeReadout s View
admissions : LocalAdmissions s View
original : Kernel (Payload s View)
environment : Environment (Payload s View)
context : Context
mark : Mark
callee argument : Source Category.expression
⊢ ∃ occurrence data state,
    decode readout environment = some state ∧
      admissions.logical state { site := mark.site, kind := BinderKind.viewLogic } LogicalKind.viewLogic data ∧
        have candidate := scopeCandidate environment occurrence (Payload.logical LogicalKind.viewLogic data);
        have after := environment.extend { site := mark.site, kind := BinderKind.viewLogic } candidate;
        (∀ (premise : Premise),
            premise ∈ appPremises context mark callee argument →
              Local (admissionKernel inputs readout admissions original) after premise) ∧
          SourceJudgment (admissionKernel inputs readout admissions original) after context callee ∧
            SourceJudgment (admissionKernel inputs readout admissions original) after context argument
```

Before/after parent shape is unchanged. Even an actual EI-All introduction
would not by itself supply independent logical admission, original target
Checking, completeCallCertificate, both child derivations, or annotation locals.
The first goal in this completely general parent probe is annotation locals;
the formation route then lacks the typed inputs described above. No fixed
synthesis endpoint was rewritten and no shared witness was split.

## Delivered theorem, commands and complete axiom result

Only repository proof change:
`notes/theory/lean/YulangClosure/ComputedCallSourceFormationR305.lean`.
All original source expression constructors remain in the parent domain;
the theorem itself quantifies arbitrary Call operands and arm lists. It proves
only constructor disjointness. No EI phase cases, semantic arms, checking,
source/native simulation, full soundness or production instance is represented
by this theorem.

Installed native Lake was resolved with read-only `elan which lake` from the
pinned project. The lookup emitted an existing-toolchain/latest-release-query
warning but returned the installed executable. Actual versions:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Verification owner: this leaf, isolated copied project and private `.lake`
under `/tmp/yulang-r305-proof/project`; no shared cache writes. No packages.

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --project /tmp/yulang-r305-proof/project \
  --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake \
  --module YulangClosure.ComputedCallSourceFormationR305 \
  --theorem YulangClosure.ComputedCallSourceFormationR305.call_lookup_excludes_union \
  --timeout 180
```

Checker exits 0, focused 17-job import/module build exits 0; per-theorem type
and full transitive axioms below. One existing warning at byte-frozen R104
line 152 (`unused simp argument`), no warning in R305. Default-root/full build
not run. Both deliberately failing probes use native `lake --no-cache env lean
-j1 -M1024`, each bounded to 60 seconds, and each exits 1 as recorded.

```text
YULANG_AUDIT_BEGIN YulangClosure.ComputedCallSourceFormationR305.call_lookup_excludes_union
@YulangClosure.ComputedCallSourceFormationR305.call_lookup_excludes_union : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View) (scope : List YulangClosure.OriginalSource.Binder)
  (graph :
    YulangClosure.SourceSignatureConstruction.Graph (YulangClosure.OriginalSourceInterpretation.RawObservation s))
  (index : Nat) (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (nodes : YulangClosure.SourceSignatureConstruction.CallNodes)
  (locals :
    List
      (YulangClosure.SourceSignatureConstruction.Introduction
        (YulangClosure.OriginalSourceInterpretation.RawObservation s)))
  (result :
    YulangClosure.SourceSignatureConstruction.Catalogue (YulangClosure.OriginalSourceInterpretation.RawObservation s)),
  graph.node index =
      Option.some
        (YulangClosure.SourceSignatureConstruction.Node.call context mark callee argument nodes locals result) →
    ∀ (site : YulangClosure.OriginalSource.Site) (left right : Nat) (source : YulangClosure.OriginalSource.Endpoint)
      (arms : List YulangClosure.OriginalSource.Endpoint),
      graph.node index ≠
        Option.some
          (YulangClosure.ComputedCallUnionRealizationR293.unionNode inputs state scope site left right source arms)
'YulangClosure.ComputedCallSourceFormationR305.call_lookup_excludes_union' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.ComputedCallSourceFormationR305.call_lookup_excludes_union
```

Import-cone source scan (16 source files) found only the existing comment
about a coinduction axiom and audit error-message strings; no project axiom,
hole or bypass. The theorem uses `[propext, Quot.sound]`; it is not axiom-free.
No checker/model/native/compiler/runtime receipt is claimed beyond these real
commands. Independent review, source correspondence and production authority
are unestablished.

Material execution repair: an initial copy used a repository-relative path
while cwd was the Lean project and failed (`cp: cannot stat ...`); no file was
modified by that failed copy. Absolute-path copy succeeded. Initial manuscript
lookup used theory instead of design for IF definition, failed read-only, then
read the actual design path. No mathematical proof failure was hidden.

## Frozen identities and resources

Proof artifact SHA-256: `0cfdf7e1e3f23cbd0b984e25138126bb36c729cb6dc0430df65d632475915922`.

Source authority/config hashes:

```json
{
  "notes/design/2026-10-24-computed-call-result-constructor.md": "2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6",
  "notes/theory/2026-10-24-generated-computed-result-correspondence.md": "58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b",
  "notes/theory/2026-10-08-call-source-interface-construction.md": "278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98",
  "notes/design/2026-10-08-call-source-interface-definition.md": "20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c",
  "notes/theory/2026-10-08-source-generalize-definition-and-proof.md": "e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240",
  "notes/progress/2026-10-06-source-call-generation-construction.md": "6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073",
  "notes/theory/lean/lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c",
  "notes/theory/lean/lakefile.toml": "212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4",
  "notes/theory/lean/lake-manifest.json": "058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3",
  "tasks/agent-loop/sprints/call-source-formation-r305.md": "9bf670afd72d3f59632ff8214d24033c44390d838427cd4be214d65406160cc6"
}
```

Full actual import-cone source hashes:

```json
{
  "notes/theory/lean/YulangClosure/ComputedCallSourceFormationR305.lean": "0cfdf7e1e3f23cbd0b984e25138126bb36c729cb6dc0430df65d632475915922",
  "notes/theory/lean/YulangClosure/ComputedCallUnionRealizationR293.lean": "50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543",
  "notes/theory/lean/YulangClosure/Contracts.lean": "2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e",
  "notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean": "39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957",
  "notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
  "notes/theory/lean/YulangClosure/OriginalSourceChecking.lean": "a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6",
  "notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean": "0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132",
  "notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean": "126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef",
  "notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean": "feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef",
  "notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean": "3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1",
  "notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean": "5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408",
  "notes/theory/lean/YulangClosure/SourceContributionConstruction.lean": "9755a65a2b3e6b97f7da5bf21c844fb7f5292c12925de9f9081fccaa322380a1",
  "notes/theory/lean/YulangClosure/SourceFunctionMembership.lean": "8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424",
  "notes/theory/lean/YulangClosure/SourceIdentityWorld.lean": "6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168",
  "notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR104.lean": "0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39",
  "notes/theory/lean/YulangClosure/SourceSignatureConstruction.lean": "ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311"
}
```

Raw evidence hashes:

- `/tmp/yulang-r305-proof/check.log`: `44d8fec606cfc1460e7bdef74d90f25963f35f52f4fe574b6911816dda36702b`
- `/tmp/yulang-r305-proof/AttemptR293.log`: `50232d25041b87f7f65b227934ebe143b6521ebb24f46ec3c52813c92d299ba2`
- `/tmp/yulang-r305-proof/AttemptR159.log`: `bff24771e76b7e9c97b0e493e9e0ef8e204e1b7cd73bbb078540aacd57569298`
- `/tmp/yulang-r305-proof/dependency-hashes.json`: `20321c8bbe2cb0504be9d24ee10220cd7c7bfa0635ee94cefe2c666691181a64`
- `/tmp/yulang-r305-proof/source-hashes.json`: `5b3b1fe072b003b09fd3019705c7c3d5d8a75bf02ea4d2d01d8a269ccbb5207a`
- `/tmp/yulang-r305-proof/source-scan.log`: `131097b53b8cd773dd9beaa9778067e9cc84cf85a719bbd36fb87183581b2b68`

All scratch/generated outputs are under `/tmp/yulang-r305-proof`: copied
project sources/config, private `.lake`, the two failing probes and their logs,
checker log and hash/source-scan manifests. The helper also created its normal
`/tmp/yulang-lean-audit-b_xwf0co` temporary audit directory and automatically
removed it. Scratch occupies 186 MiB. One checker at a time; no ongoing process.
Individual Lean bounds `-j1 -M1024`, checker wall bound 180 seconds. Total lane
budget 2400 seconds; exact active elapsed/peak RSS were not instrumented, so no
fabricated measurement is reported; conservatively charge the reservation.

Repository writes are limited to the leased proof file and this handoff.
No shared task/status/index/rules/manifest/lockfile/root-import/other-worker
writes. The source inputs are frozen. **WRITES STOPPED** on this handoff.
Stop reason is the packet's precise missing-input condition, not budget
exhaustion or a claim that a conditional theorem closes the original parent.
