# R167 module schedule: structural order and missing Case classification

Date: 2026-10-20. Status: **UNREVIEWED SOURCE/NATIVE EVIDENCE; NO_SAFE_CODE_SLICE for the missing
Case binding classification and dependent public whole-module entry**.
Author: `/root/r165_native_admission_proof`; no coauthors or descendants.
Assignment: `R167-SOURCE-INITIALIZER-COMPLETENESS`, contract revision 3,
SHA-256 `792b2d8f140d7c8bfd0623a452213228fbe731f377b7494cb8f8bc88d116f535`.
Frozen source baseline: `8efcaaa780b12d0ede0852a63ce931b0a46fe319`; later contract/evidence commits
do not replace that source baseline. All six source owners and R149/R166 authority pins matched.

## 1. Parent application and result

The original goal remains proof-backed inference/evaluation and broad execution of unchanged Yulang2
Web samples in this repository. R149's adopted module behavior requires all source-required computed
initializers and all direct expression roots in source order, cached successful definitions, lazy
values, and honest module completion. It does not define every retained source constructor's
initializer classification.

The inspected source establishes an authentic item/occurrence-to-code-to-root join and a stable
source-order subsequence for successful `RuntimeProgram::from_hir`. All supported direct expression
items enter that list exactly once. A binding enters once exactly when the current runtime predicate
in §3 selects it. This proves structural membership/order for that predicate, not equality with every
source-required computation initializer.

**Missing premise R167-CASE-FETCH-1:** an applicable source-owned law for the initializer fetch class
of an admitted Case binding, carried from its original source occurrence to the schedule consumer.
Current `LocalSource` retains Case syntax but no such marker; the current runtime predicate omits
Case. `HirBinding.evaluation_class` is explicitly generalization eligibility, not this schedule law.
Neither instruction shape nor the effects/purity of a selected example can fill the missing premise.
Therefore the dependent public whole-module entry has **NO_SAFE_CODE_SLICE** in this packet.

This is a precise missing source-authority/correspondence result, not a counterexample proving every
Case must run, every Case must stay lazy, or a full accepted sample fails. The result neither narrows
the admitted language nor proposes rejecting Case. Original inference/evaluator A/B, R149 sample
compatibility/whole-source adequacy, R166 ordinary-provider incidence, R70/R71, replay residual
correspondence and production remain OPEN.

## 2. Actual source-to-HIR-to-schedule order

At `crates/yu-hir/src/module.rs:1180–1186`, the lowering owner enumerates the parsed root's direct
children into one plan vector in source order. `namespace:2006–2029` visits that vector without
sorting it; it allocates distinct same-name ordinals rather than conflating duplicate spellings.
`lower_module_with_counters:1227–1292` visits the same plans in order, constructs the authentic
definition or expression root, calls `lower_plan`, then pushes exactly that item. Unsupported/error
items remain explicit entries rather than shifting an unrelated item's identity.

Bindings retain their real `DefId` and `DefinitionRootId`. Direct expressions get an
`ExpressionRootId` anchored to their actual original HIR occurrence; no DefId is fabricated.
Ordinary source carriers are formed in separate binding/expression passes but stored into
`outcomes[index]`, then flattened in original item-index order (`module.rs:1293–1334`). Thus carrier
allocation order does not reorder execution. `source_carrier_for` validates artifact/root ownership;
`local_source_for:979–987` returns Supported, refuses an explicit Unsupported outcome, or uses the
existing definition-local-source fallback only when the ordinary outcome is absent.

`LocalSource::order_occurrences:101–134` assigns published occurrences by the source owner's
descendant order, retaining a direct-expression body's authentic root occurrence and checking that
no stored source node remains unmatched. The carrier's local indices are checked against its owner
(`local_source.rs:143–148`); a foreign index cannot serve as a child merely by ordinal coincidence.
This is source identity, not execution demand classification.

`RuntimeProgram::from_hir:290–320` iterates `hir.items()` in that order and retrieves each item's own
source root/carrier. `label:337–343` first validates a local source index and maps it to the source's
code-arena offset. Each code node retains that original `source_root`, occurrence and range
(`program.rs:595–608`). For a binding it stores the real DefId/body and conditionally appends one
Definition root. For an expression it stores its authentic expression root/body and unconditionally
appends one authenticated Expression root (`:614–655`). The constructor returns its Arc only after
the complete construction succeeds; a prior Err does not publish a partial schedule.

An induction over this item loop proves the structural statement: after k processed admitted items,
the schedule is exactly their selected binding/direct-expression subsequence in item order; each
next branch appends zero or one corresponding root and preserves the existing prefix. At the end
there are no reordered roots or invented expression identities. This does not prove the binding
selection predicate equals a missing source semantic classification.

The machine validates root IDs, expression code/root joins and duplicate entries at `start`
(`machine.rs:306–337`). These checks protect supplied-list identity and duplicates, not semantic
initializer completeness. No count or successful constructor alone closes the source-classification
premise.

## 3. Exhaustive retained-form table

All fourteen `LocalSourceForm` variants are listed below (`local_source.rs:246–290`). “Selected” means
only the actual binding predicate at `program.rs:624–642`. Direct expression roots of every form
are selected independently of that predicate. Retention/lowering is not a new source classification
decision. This packet does not certify all older rows as new R167 semantic authority.

| Source form | Actual runtime lowering and binding predicate | Coverage boundary |
| --- | --- | --- |
| Unit | Unit; not selected | Source value/lazy policy must retain its actual authority; no effect-based test |
| Integer | Integer; not selected | Literal spelling retained; construction does not eagerly evaluate it |
| Boolean | Boolean; not selected | Boolean source formation does not mark computation demand |
| Plain String | String; not selected | Interpolated strings are outside this retained plain path |
| Name | Name; not selected | Target materialization is separate; do not inherit a target's class through alias/SCC traversal |
| Operation reference | Operation; not selected | The operation reference is distinct from an actual Apply/request |
| Lambda | Lambda; not selected, regardless body | Stop at the function boundary; no eager body traversal for this predicate |
| Apply | Apply; selected | Existing predicate fact; callee/argument effects do not prove its source law |
| If | If; selected | Supported source arm structure is retained; no constant/purity classification |
| Catch | Catch; selected | Retained handler syntax is not a new general receiver/root classification |
| Case | Case; **not selected** | **R167-CASE-FETCH-1 OPEN; NO_SAFE_CODE_SLICE** |
| Group | Forward; follow child | Proper source child; no recursive definition walk |
| Ascription | Forward; follow child | Existing erasure/no-applicable-adapter premise remains separate; type/effect syntax alone supplies no schedule law |
| Block | No bindings: follow final child; at least one binding: selected | Empty/nonempty distinction is actual source structure; neither all Blocks nor all pure tails get a guessed class |

Forward and empty-Block steps follow proper finite source children, so this predicate terminates
without following Name targets or inference SCCs. Values not selected by this predicate receive no
eager root entry from `from_hir`; all definitions still have cells available for ordinary demand.
This describes current behavior, not a universal proof that every source value is classified correctly.

### Case retention supplies syntax and execution, not module fetch class

`Builder::case:1234–1315` admits the supported Case scrutinee/block shape, exactly one pattern per
arm, integer/binder/wildcard patterns and at least one arm. Other patterns/shapes return Unsupported.
It retains the original Case, arm sources/ranges, binder identity and child indices. It does not
compute or retain a `RequiredComputationInitializer`/BindingFetch output.
`program.rs:559–580` validates/translates those children to Instruction::Case, decoding an integer
pattern or returning explicit unavailability on invalid provenance/decoding. The binding predicate
then falls through its `_ => false` arm because Case is not among the selected constructors.

When actually demanded, `machine.rs:690–697,1223–1250` evaluates the Case scrutinee, selects the first
matching actual arm, binds its original binder if needed, and evaluates that arm, or returns
NonExhaustiveCase. These operational facts do not decide whether its enclosing module binding is a
source-required eager initializer. Case children can contain ordinary computations; no argument from
a pure-looking branch licenses executing every Case eagerly, and no missing root proves every Case
is correctly lazy.

`module.rs:571–578,771–791` explicitly documents `EvaluationClass::FetchValue` as frozen source-owned
**generalization eligibility**, with later computation forms unclassified until their exact gate.
It is private, has no computation variant, and may be None for a Lambda with Apply body. Its
recomputation after ordinary admission (`:1653`) does not turn None into a computation certificate.
It cannot substitute for the source initializer law or justify adding Case to the runtime match.

## 4. Unsupported, recovery and failure branches

| Actual owner branch | Result and schedule consequence |
| --- | --- |
| Ordinary supported binding/expression carrier | Source identity retained; runtime loop applies §3 / unconditional expression rule |
| Recovery in source plan | `form:604–605` returns Unsupported(Recovery); no guessed executable carrier |
| Unsupported grammar/form/pattern/interpolated string/tuple path | UnsupportedForm; ordinary carrier outcome remains explicit; runtime local-source lookup returns None and construction returns MissingSource |
| Supported-depth refusal | Unsupported(SupportedDepth); retained refusal, no partial schedule publication |
| Structural identity/foreign-index inconsistency or allocation/identity failure | Availability error propagates; not silently converted into a skipped computation |
| Nonempty HirItem::Error containing only actual registered Act placeholder UnsupportedItem IDs | Exact `program.rs:300–309` guard skips the declaration placeholder; other roots retain relative order |
| Empty error list, unrelated unsupported item, other error IDs or wrong kinds | Runtime program construction returns MissingSource; no arbitrary Error-root erasure |
| Direct-root HIR lowering recovery/error expression | Original expression occurrence/root still exists; supported-carrier lookup is independently required; no success claim from the root handle alone |
| Supported carrier with unresolved/ambiguous Name or Operation resolution | Retention is not successful resolution or accepted inference; no blanket claim that from_hir itself rejects every HIR error |
| Invalid code/index/root join or invalid integer Case pattern decoding | Explicit runtime construction error, no fabricated SourceSite/root or partially returned Arc |

Source and frontend gates remain distinct. `tools/inference-playground/src/lib.rs:266–335` rejects
syntax diagnostics, propagates candidate inference refusal and withholds execution on candidate
conflicts; `execute:165–179` prepares before constructing the runtime. Those facts do not prove
full inference acceptance, classify initializers, or justify arbitrary error recovery. The structural
statement in §2 is scoped to actual successful `from_hir`, not all parse/HIR inputs.

## 5. Laziness, caching and whole-module boundary

Under the existing supplied root list, `begin_root:1851–1890` skips a definition whose cell is already
materialized; otherwise it records its initializer marker/cache-write suffix. An expression gets
ExpressionReturn and no global cell/initialization marker. Root completion saves the exact result;
GlobalRead similarly materializes a demanded definition once and then uses its saved value
(`machine.rs:619–634,1251–1279`). Closure formation retains a body/environment without executing the
body (`:640–658`). These preserve the current operational distinction between root scheduling and
lazy demand. They do not establish whole typed-source materialization adequacy under arbitrary raw
resumption or repair a missing initializer classifier.

At schedule exhaustion the current code calls `complete_selected_definition:1892–1908`, returning a
cached selected definition or evaluating its actual initializer. That fallback can cause an omitted
binding to execute when selected. It cannot certify that a whole-module schedule was complete.
No synthetic selected DefId or source-bearing Unit can stand in for module completion. No public
whole-module entry should be enabled under this packet's missing source classification premise.

## 6. Bounded authority inspection and precise next obligation

Luna authorized only a bounded read of the source-owner note's referenced authority, then adjudicated
that it must remain inspected context rather than newly promoted R167 semantic authority:

- `notes/design/2026-10-16-module-expression-source-owner.md`, SHA-256
  `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`, explicitly retains whole typed-source
  materialization/root adequacy OPEN while requiring original ordered mixed roots.
- `/home/momota1029/rust/yulang2-oracle-capture/spec/2026-06-13-mono-vm-contract.md`, SHA-256
  `9f88e1e21387ebe0ef42e2d857fcd37ba52d51acd1962cdb3cb6b80666819388`, only “Program と roots” was read
  substantively: source-ordered Instance/Expr demands and cached completed instances. It supplies no
  per-constructor Case fetch classification.
- `notes/theory/2026-10-15-playground-ordinary-runtime-simulation.md`, SHA-256
  `16dcc7252c966a6d0f317ed9625cf9f5c101e4bada5f9f00d0788fe4ebe28a8b`, exact module-initialization section
  has a finite historical source BindingFetch table; **Case is absent**. Its conditional old-source
  theorem and annotation premises cannot certify newly retained Case or current full-source coverage.

No binary/sample or unrelated Oracle source was opened or executed. No additional semantic authority
is inferred from that audit. R149 adopted design §4 and its provisional entrypoint adoption remain
the governing intended behavior, not an omitted classification theorem.

**R167-CASE-FETCH-1 handoff:** source owner must supply/establish the actual fetch-class law for an
admitted Case binding and preserve that occurrence-qualified result into runtime schedule construction,
including Group/Ascription/empty-Block forwarding and lazy Lambda boundaries. Then prove the schedule
predicate consumes precisely all source-required computed entries and all direct roots, with no eager
source values. Required source inputs are the real admitted Case/children and governing source rule;
effects, generalized types and runtime instruction shape are not substitutes. The owning seam is
HIR source formation/classification -> `RuntimeProgram::from_hir` binding schedule consumer.
Luna owns authority resolution and any subsequent exact implementation grant.

Falsifier for future correspondence: an authentic source-required initializer omitted, a source value
forced early, an original root duplicated/reordered, or a constructor whose required class lacks its
governing source law. This packet establishes the last missing-law condition for Case, not either
behavioral counterexample. It proposes no all-Case eager rule, source restriction or semantics change.

## 7. Frozen inputs, checks and cessation

```text
R149 contract       31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9
R149 adopted design 1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa
R166 closeout       429139155dc96541eff6f4272d2b1684f5b6d095b71eb92db9df78af5b43ce63
runtime program     28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
runtime machine     875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1
runtime mod         64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
playground lib      a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473
HIR local_source    d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
HIR module          153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
```

Checks: exact source/authority hashes, direct branch-ref reconciliation supplied by Luna, source
constructor/identity/order inspection and prose case audit. No tests/builds/probes, compiler/runtime
or Y2/Y3 executions, instrumentation, code/solver edits, Git commands, network, user/external contact
or descendants. No scratch/generated paths. Exact outputs are this artifact and the leased inbox;
its frozen assignment prefix is preserved and a separately numbered result is appended.
Requested model/effort UNKNOWN/UNKNOWN; observed UNKNOWN/UNKNOWN.

Fresh rev3 launch observation 14:11:31 UTC; grant 1200 seconds, Astra 0, no carryover or extension.
The earlier rev2 baseline mismatch attempt was stopped with no output and no source change, as Luna
reconciled before this grant. Stop condition is the exact missing source classification law.
Frozen for fresh independent review; author cannot certify it. **STOPPED; writes stop with the result
handoff, no descendants/background processes or additional leases.**
