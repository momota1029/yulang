# R19 Lean leaf — frozen handoff revision 1

Sprint: CALL-EFFECT-OWNER-REALIZATION/20261028-r19; contract revision 2 with amendment 01.
Contract SHA-256: `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`.
Amendment SHA-256: `9c90b318aaa322aade2440c9924a1e38d7d8e67b2e1e40fb27bd6c568904aa93`.
Worker: `/root/r19_lean_leaf`; session `CALL-EFFECT-OWNER-REALIZATION-20261028/r19`.
Launch/lease transfer: primary START packet identifying commit `ba38d8fa9`.
Requested role/model/effort: lean_prover / gpt-6.1-sol / high, as recorded by primary; observed model/effort UNKNOWN.
Outcome: missing source equation; no new theorem constructed. Independent review and production authority: NOT_ESTABLISHED.

## Original source and parent

Unchanged fully qualified parent: `YulangClosure.SourceProblem.InferenceSoundness` in pinned `YulangClosure/Contracts.lean:128`:

```text
forall s x d a, p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e and p.sameScoped s x e a.
```

The original Call generation manuscript is `notes/progress/2026-10-06-source-call-generation-construction.md`, §5 (SHA-256 `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073`). Its single scoped existential retains WF_Dec, VIncl, WholeArgCompatible, complete ExecuteCallableImage CIncl, TypedCallCert_Dec, Role_0 and Gen-Call-0. Its scope is the stated decorated rule envelope, not an exhaustive whole-language theorem.

Pinned parent `notes/theory/2026-10-26-original-call-evidence-construction.md`, §§2, 8–9 (SHA-256 `11246f05292b1ed4729e6e953f042d0cbfceea05decfbd0b2e7fbaac3c52539f`) explicitly retains the missing concrete original predicates and sameScoped interpretation. Its F1–F10 candidate is not semantic authority.

Selected authority: `notes/design/2026-10-07-complete-call-contribution-definition.md`, §§2–5 (`4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e`), and `2026-10-08-call-source-interface-definition.md`, §§2–4 (`20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`). C-Call retains the entire authentic operation; J-Owned requires all four accounting conditions. IF preserves independent semantic/primitive/provider/action premises.

Generalize source: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §§3.1–3.3 (`e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`), conditional on independently interpreted local constructors. Current effect correction: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`, §§1.1–1.2, 3 (`a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`): annotation grants permission, actual handler subtracts only its operation; unrelated residual effects remain.

The research manuscript `docs/yulang-source-type-safety-ja.tex`, sec:owners (`2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`) distinguishes expired original receiver from fresh resumed owner. It is explicitly unreviewed/Draft outside selected premises; no authority promoted from it.

## Exact missing equation and parent application

Pinned `YulangClosure.OriginalSource.sourceRules` app clause (`OriginalSourceGeneration.lean:111`) emits descriptorFormation, wholeArgumentCompatibility, completeCallCertificate, sourceCallIncidence and callableImage atoms, plus the singleton role/origin atom when applicable. `YulangClosure.OriginalSource.Kernel.atom` is an abstract independent predicate. `Judgment.rule` and reconstruction reconstruct this local rule tree from solutions; they do not interpret those atoms as the complete original Call certificate, C-Call or J-Owned.

First missing source-owned bridge, owner Luna/source-proof intake (`R68-OWNER-CONSUMER-1`): interpret the actual generated completeCallCertificate/sourceCallIncidence/callableImage at the same source Call, source-selected provider, original shared xi=(nu,K,D), current world and event telescope; show that their actual constructors supply the original complete consumer and J-Owned's four accounting conditions, retaining lexical/checking incidence separately, independent F1/FK1, foreign continuations and arbitrary lawful client allocation. An equality of roots, type terms, graph IDs or replay receipts cannot supply it.

`YulangClosure.OriginalSourceInterpretation.Inputs` still parameterizes actual provider/path/receipt/context and checkedObservation relations; it does not construct that original interpretation. The generic SourceProblem predicates and sameScoped have no concrete original instance here. Supplying the missing bridge as a theorem parameter or redefining sameScoped would only restate the obligation.

Useful existing results: `YulangClosure.OriginalEffectHygiene.generated_new_use_keeps_original_publication` obtains reconstructed source/client judgments in one admitted frame, original publication identity, captures/history replay and alias identity. `published_execution_judgment` obtains an admitted saved event and its body derivation. These can discharge the stored-publication/replay subpremise once the original interpretation is supplied. They do not imply the original complete owner/consumer interpretation. No new theorem is applied to the parent; InferenceSoundness and all full source/native/production gates remain OPEN. No source-qualified counterexample is claimed.

Represented existing cases: raw source 13/11/3 generation inventory, fixed publication replay versus open future events, original scoped binder/payload history. This packet adds no restricted source subset. Unproved application cases remain all original Call alternatives, arbitrary lawful allocations, independent F1/FK1, foreign continuation/current-world interpretation and full effect/permission accounting.

## Authenticated inputs and actual execution

Baseline: `cbd04a4acd9e10f944f50fc0bfefff24671fe387`.
Input manifest SHA-256: `f287059a08410cf644644be214ba622de92d3e2d10c4897441cbb360c91ca22d`.
Python SHA-256 readback checked all 289 isolated Lean input rows and 11 listed parent artifacts: 300 rows, zero mismatches, exit 0. Root source edits and the unadopted proposal were not incorporated.
Direct pinned dependencies:

- Contracts.lean: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- OriginalSourceGeneration.lean: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- OriginalSourceInterpretation.lean: `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- OriginalEffectHygiene.lean: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`.
- lean-toolchain: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- lakefile.toml: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.
- lake-manifest.json: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

Commands from isolated Lean project, exact native path resolved by read-only `elan which lake` (exit 0):

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
exit 0
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
exit 0
```

No delivered theorem, build, checker invocation or #print axioms query: NOT_RUN. No theorem types or axiom results are claimed. Native version execution is not kernel acceptance. Project retains -j1/-M1024; no dependency, global setting or root import edited.

Material non-proof command failures retained: rg of absent Original*Consumer* glob exited 2; attempted notes/design/2026-10-08-source-generalize-definition-and-proof.md exited 2, then located/read the actual notes/theory path; glob search for absent R19 history exited 2. None is mathematical failure evidence.

## Freeze and cessation

Only authored path: this exact handoff. The leased module `isolated/call-effect-owner-realization-r19/lean_project/notes/theory/lean/YulangClosure/OriginalCallEffectOwnerRealizationR19.lean` remains ABSENT. No scratch theorem/audit files, children, Git operations, compiler edits, dependency writes or shared-state writes. Dedicated .lake may contain Lake-generated environment configuration from the version command; no build cache population is claimed.

Resource grant: 300 seconds, one CPU, no renewal. Lean version tool call wall time 0.37754 s; proof-check process time 0. Aggregate wall time, CPU/RSS were not instrumented and remain UNKNOWN. Stopped at the missing-source-equation condition; no remaining budget is claimed. Next action requires primary-supplied concrete original interpretation, not installation or a larger checker budget.

Worker STOPPED; all authored writes stop after creation of this revision. No live child/generated-output writer remains. Frozen handoff hash is sent out of band after write; review/integration remains with Luna.
