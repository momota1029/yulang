# R172 proof/source-semantics handoff, revision 1

Sprint/contract: `formal-entry-source-judgment-input-r172`, SHA-256
`08d2d7d1579ad01a09351d0244d49d6d76bef03d7e7ece44d63ff0341a4c758c`.
Assignment: `R172-PROOF`; handoff revision **1**.
Primary-supplied branch/baseline: `yulang3/008c5fd5bdc17b8a253daf9e5d79916a2db404b0`.
Role: registered `lean_prover`, source-only fixed packet. Worker identity:
`/root/formal_entry_source_judgment_input_proof`, actual current-session task
received from `/root`. Requested model/effort and observed model/effort:
**UNKNOWN** in this worker's runtime metadata. No descendants or other authors.
Luna's exact baseline/contract update was acknowledged before writing.

Outcome class: **source-native-evidence / exact missing-input result**.
No new Lean theorem, checked construction, independently reviewed conclusion,
source-qualified Rust counterexample or production authority is claimed.

## Frozen deliverable

`notes/theory/2026-11-02-formal-entry-source-judgment-input.md`
SHA-256 `3558480ed78086ad7471b96a6e41aa88db3b7b8a6d8b54e092fae7b6dce26ef9`.

The note records Source Generalize construction §2 L1–L5 and §§3.1–3.3,
selected by the Authoritative design §§2–3, plus the current annotation hygiene
policy §§1–1.1. It maps formal type/scope, annotation/entry role, complete
interface/captures, computation entry/effect flow, pattern/body checking and
retained-entry permission to the frozen Lean source and Rust construction.

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:127–130`: for every supported `s`, scope `x`, generated `d` and
solution `a`, produce **one** `e` satisfying both `sourceJudgment s x e` and
`sameScoped s x e a`. No source restriction or quantifier change was made.

The exact candidate theorem is
`YulangClosure.OriginalSource.generated_constraints_imply_source_judgment`
(`OriginalSourceGeneration.lean:1026`). The note transcribes its full source
type. Its namespace is `OriginalSource`, although the filename is
`OriginalSourceGeneration`. It takes `Kernel`, `Environment`, `Context`, raw
`Source` and `Satisfies kernel environment (Build context source)`, and returns
`SourceJudgment` for those same arguments. It does not take `p.generates`,
`p.solves`, or a FormalEntry trace, and never concludes `p.sameScoped`.

Relevant supporting declarations inspected:

- `YulangClosure.OriginalSource.Formal.entry`, `sourceRules`, `Kernel`, `Local`,
  `Judgment`, `Checking`, `Boundary`, `Build`, `Satisfies`, `SourceJudgment`.
- `YulangClosure.OriginalFormalShared.formalContext`, `checkedBody`,
  `entryPremises`, `lambdaTree`, `build_entry`, `annotation_child`,
  `value_entry_shared`, `computation_entry_shared`.
- `YulangClosure.OriginalSourceClosure.closureKernel`, `checked_body_consumer`,
  `generated_value_body_consumer`, `generated_computation_body_consumer`.
- `YulangClosure.OriginalSourceChecking.Declarations`, `FunctionShape`, `kernel`.
- `YulangClosure.OriginalSourceEvents.EntryRegistration`, `lambdaScope`,
  `lambdaEntry`, `source_lambda_entry`, `Joint`.

## Parent application / exact open premises and owners

1. **First concrete composition premise, unchanged from R171:** establish the
   scanned-to-prepared formal projection. `newFormal.entry = none` cannot be
   literally the successfully selected R169 formal with `entry = some port`.
   Preserve owner, Lambda index, parameter, recipe index, scope, role and
   registration index through `initialize_candidate_source_levels`'s real
   `native_root`/`entry_effect` updates (`candidate_source.rs:2303–2325`). Also
   represent record-field recipe appends and duplicate rejection (`:1119–1123`)
   before claiming equality with the real recipe snapshot. Owner: **Luna to
   grant a finite construction/source-correspondence repair packet**. The
   source Lambda judgment defines neither Rust update relation and repairs
   neither defect by itself.
2. **First input missing at the parent-to-reconstruction seam:** prove an
   independently justified concrete interpretation taking the same
   `p.generates s x d` and `p.solves d a` to the whole original-source
   `Satisfies K E (Build C S)`. This requires actual formal/annotation/interface,
   complete body, original admission and effect-row/permission premises, as
   well as every other constructor. `Kernel` parameters and proposition
   definitions do not establish these instances. Owner: **Luna's source/proof
   generation and solution interpretation assignment**, after the local
   construction repair and intake of the source lane's map.
3. After satisfaction, the existing theorem gives its `OriginalSource`
   judgment. A concrete interpretation still must provide one parent witness
   `e` with the original judgment and `sameScoped` for that same solution `a`.
   Owner: **Luna's source-judgment/solution witness bridge**. Separate witnesses
   for uses/challenges cannot replace the shared witness.

Stable requests: `R172-PROOF-PREPARE-1` (item 1),
`R172-PROOF-SATISFACTION-1` (item 2), `R172-PROOF-SHARED-1` (item 3).
These are evidence requests, not new leases. Inputs are the frozen artifacts
below, the actual source lane's construction map, and genuine original local
laws. Proposed later output: finite preparation/recipe relation with origin
preservation, then a source-directed constraint/solution interpretation.
Falsifier: a successful real construction losing an origin/recipe relation,
or a generated solved source whose required local source premise fails.
No such reachable Rust counterexample was established in this packet.

## Source -> constraints -> consumer scope

Collector registration (`candidate_source.rs:1098–1123`) saves source origin and
recipes; action construction (`:1323–1339`) retains the same formal annotation;
preparation (`:2303–2325`) supplies the effect port; action dispatch
(`:2472–2479`) calls formal annotation/entry constructors and equates formal
Name effects with that entry. `candidate_formal_entry_annotation`
(`candidate_effect.rs:1990–2066`) retains concrete permission and optional
variable equality. Entry-permission use functions (`:557–650`) authenticate
source/registration/native incidence without inferring permission identity
from row equality. This is static inference-source evidence. Propagation and
handling laws are not derived from it, and runtime/machine paths were not read.

Represented: exact source Lambda shell for both entry modes, arbitrary original
pattern/body through `sourceRules`, expression annotation boundary, scopes and
Shared/EventProof order; static admitted Rust collection/preparation/action and
permission constructor/readout sites. The generic raw source inventory stays
13 expression / 11 pattern / 3 statement forms; no form was removed.
Omitted proof instances: concrete source parser/HIR encoding, original local
kernel/admission meanings, record/default construction realization, all other
constructors' concrete inference interpretation, effect propagation/consumer
law, parent generation/solution and shared-witness bridges. Recursion, methods,
captures and annotation hygiene remain in the accepted source domain.

## Frozen dependency manifest

Two `sha256sum` passes returned exit 0 and identical values matching the R172
packet. No frozen input was edited.

| Dependency | SHA-256 |
| --- | --- |
| R171 contract | `8289f460cb3a3057118bda0337722699714c1debe3b349db51691cae2d7e541e` |
| `FormalEntryOriginR171.lean` | `03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6` |
| R171 proof handoff | `a1818e9797e8bdef8fac49157dc061fbf94b56b2bbd2981e436e7236a038caca` |
| R171 source handoff | `8db9a9730932aedd162ad4c918000c6c73176323eae797be022a197db2174f22` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| `OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| Source Generalize design | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Annotation hygiene policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |

## Commands, resource and STOP receipt

Applied `.agents/skills/yulang-lean-proofs/SKILL.md` and its `sources.md` and
`execution.md` references. Root AGENTS/base map, sprint rules, design authority,
top-level inference principles, current snapshot and handoff protocol were read.
Commands: read-only `cat`, bounded `sed -n`, `rg -n`, `rg --files`, and two
`sha256sum` dependency passes. Successful commands exited 0. Large combined
tool displays were sometimes truncated; relevant source sections were reread
with bounded commands. Writes used `apply_patch` for the two leased Markdown
files only; artifact/final handoff hashes use `sha256sum`.

Read pinned configuration: `leanprover/lean4:v4.35.0`, `YulangClosure`, no
external packages, `-j1 -M1024`. Actual Lean/Lake version commands: **NOT RUN**.
Lean invocation/build/helper/printed theorem type/`#print axioms`: **NOT RUN**
under R172's explicit zero-check allowance. No new theorem is delivered and
no axiom result is invented. Historical R171 diagnostics and audits remain in
the frozen R171 handoff; they do not count as R172 execution or parent closure.

Budget: at most 900 seconds; completed within the fixed bound. Whole worker
wall time and process RSS were not measured, so exact figures are UNKNOWN.
No compiler changes, builds/tests/Cargo, Git, new dependencies, tool install,
cache/output growth, scratch/generated file, runtime-path read, children,
scheduling changes or independent-review assignment occurred.

Exact writes: the note above and this handoff. Scratch/generated paths: none.
Unresolved descendants: none. Next step returns to Luna for source-lane intake,
fresh independent review of these frozen bytes, and a separately leased repair.
**STOP: all artifact/handoff writes stopped after final hash receipt.**
Commit-ready status: pending fresh independent review and primary adjudication;
original inference-soundness parent and production gates remain OPEN.
