# Centered output conflicts: head selection, failed equations, and V5

Status: Draft — source audit and repair proposal; no Lean changes or new proof.
Date: 2026-11-14.
Baseline: `53c455a30`, `astra2/centered`.
Scope: centered-14; G′ is `GeneralNominalCenteredAdministrativeLocal.boundary`.

## Semantic correction

The supervisor's correction follows the existing [role specification](../../spec/06-roles.md):

- §6.2: 「同じ role と型に対して複数の `impl` が候補になる場合は**曖昧**として拒否される」.
  Candidate choice is by the unnamed inputs/head, not by associated outputs.
- §6.3: 「`impl` が選ばれて `type value = ...` が分かったとき、等式 `'v = value` の制約が足されて、それまでに積まれた制約と合わなければ、その時点で型エラーになる」.
  Output consistency is checked after choosing the implementation.
- §6.3: 「二つの関連型の出力を等しいとし、需要を一つにまとめる」 and
  「impl を選ぶ前、保留のままでも行う」.
  All output requests of a same-input demand class must be retained.

Accordingly, two visible `impl R int` declarations remain ambiguous even if
only one output equation fits a request. A unique `R int` with `out = list int`
and a class request `out = int` instead produces an ordinary type error after
head selection. Neither case licenses another pending rule.

This supersedes the claim in
[the class-local note](2026-11-14-centered-class-local.md) that filtering
Survivor by Joint implements the specification. The G″ Lean results remain
mathematical results about that classifier, but are not a faithful source
boundary. Its second fixture is not a reason to remove head uniqueness from
installation. No historical file is modified here.

## 1. What the current implementation does

### Three consistency gates, without an output-error result

Reading the actual installation path gives the following:

| Definition | Relevant condition |
| --- | --- |
| `GeneralNominalRecursiveCandidates.Prepared` | Includes `RequestReady` and `Consistent`; the latter is existence of `BranchModels`, which includes materialized named-output requests. |
| `GeneralNominalCycleSteps.Installable` | Requires Prepared, old Local selection, a common raw journal/packet model, and Joint. |
| `GeneralNominalJointCandidates.Joint` | Requires one raw journal model satisfying branches at the focus and every aliased registered occurrence, plus compatibility with recorded choices. |
| `GeneralNominalFeedbackSteps.Installable` | Adds feedback Local selection and merge closure to Cycle Installable. |
| `GeneralNominalCenteredSteps.PacketGuard` | Also requires a common centered model: `∃ model, Models state model ∧ plan.Holds model`. |
| `GeneralNominalCenteredSteps.At.install` | Requires Feedback Installable, novelty, and PacketGuard before constructing the installed state. There is no failed-install constructor. |

Sources: [recursive candidates](../../lean/Yulang/GeneralNominalRecursiveCandidates.lean),
[cycle installation](../../lean/Yulang/GeneralNominalCycleSteps.lean),
[Joint](../../lean/Yulang/GeneralNominalJointCandidates.lean),
[feedback installation](../../lean/Yulang/GeneralNominalFeedbackSteps.lean),
[centered transitions](../../lean/Yulang/GeneralNominalCenteredSteps.lean).

An output conflict can therefore **disable installation**. There is no
transition that records “this uniquely chosen implementation's output equations
failed.” G′ Local also has no explicit output-conflict predicate: it inherits
the old Survivor and adds center-aware K2, settled head justification, and
registration/merge closure. G″ moved Joint into Survivor, which is precisely
the incorrect output-based candidate filtering identified by the supervisor.

There is an older instance of the same semantic problem. G′'s inherited
Survivor already uses Prepared, and `Failed` can eliminate a candidate because
its named-output `Consistent` condition is false. Once ordinary feedback
exposes an output conflict, an occurrence with that output request can lose
its candidate and reach the existing zero-survivor rejection. This is not a
separate post-selection type-error judgment, and with multiple heads it can
incorrectly disambiguate. Removing only G″'s added filter does not restore
head-only matching. `HeadReady` is a useful existing starting point, but still
contains location, Fresh, private-context, and projection obligations; it is
not automatically a complete replacement interface.

### Empty models are representable, but are not an error diagnostic

[Raw Models](../../lean/Yulang/GeneralNominalSaturationState.lean) conjoins the
current context, every stored packet's Holds, and every registered site's
conditions. [Centered Models](../../lean/Yulang/GeneralNominalCenteredSteps.lean)
also conjoins site-center bounds and all stored plan equations. Neither State
structure carries an inhabited-model requirement or an error tag.

The existing theorem `GeneralNominalCenteredSteps.install_models` states:

```lean
Models (install state plan support) model ↔
  Models state model ∧ plan.Holds model
```

Thus the installation *function* can represent an inconsistent result. But a
legal centered install Step supplies an inhabitant of its right-hand side
through PacketGuard, so that Step cannot create a model-less result. The raw
common-model gate and Joint separately require witnesses as well.

This does not establish inhabited models for every reachable state. In
particular, merging adds `outputAtoms`; its model law is old Models conjoined
with those equations. The merge guards check same inputs and support, not
existence of a model satisfying the new output equations. Administrative
updates preserve the journal's models, and centered certified refresh preserves
centered models; they are not an output-conflict reporting mechanism.

[Frontier, Tree, and Result](../../lean/Yulang/CommonRoleOutermostResolver.lean)
have only pending, selected, ambiguous, and rejected constructors. There is no
type-error constructor. [V3 RejectReason](../../lean/Yulang/B4TargetV3.lean),
which V5 uses, permits exactly root K2, candidate K2, or zero survivors, with
the existing pending exclusions. It does not mention empty Models or a failed
output equation.

In [V5 Statement](../../lean/Yulang/B4TargetV5.lean):

- SaturationTotal requires model restriction from final to initial, not a
  final model or preservation of model existence.
- DictionarySound quantifies over final models. With no final models, that
  conclusion is vacuous; it does not force an error result.
- Exact equates the returned tree with resolution of Local. It does not add an
  independent consistency check.
- NoFalseRejection still requires the three old RejectReason alternatives.

Consequently **V5 currently does not say “empty Models implies type error.”**
A safe, unique head cannot simply be reported as `.rejected` for an output
conflict while retaining that Local/RejectReason contract. Nor can the error
be recoded as pending, K2, or absence of head candidates.

`B4SkeletonV5.GeneratedChildren` is stronger than a model-conditional property:
it quantifies over every reachable stable selected node, with no Models premise.
Empty models alone would not discharge that field either.

## 2. What is established for the first alias fixture

Let `finish` be `GeneralNominalCenteredCompletionAliasTrace.finish`, and let
`focus` be its plain R occurrence. There is only one R implementation, key 2.

| Claim about this named snapshot | Existing evidence |
| --- | --- |
| Actual ground-source reachability and a centered model | `CompletionAliasTrace.ground_reachable`, `finish_model` |
| G′ selects key 2 with nonempty Z children | `CompletionAliasLocal.child_selected`, `descendants_nonempty` |
| Joint is false because the requested alias requires `out = int` | `CompletionAliasObstruction.no_joint` |
| No selected Frame is Committed | `ClassLocalAliasProgress.no_committed_frame` |
| The snapshot is **not Stable**, even at the plain focus | `ClassLocalAliasProgress.equate_at`, `equate_step`, `not_stable` |
| Some finite extension is stable at root and focus | `ClassLocalAliasProgress.stable_extension` |

All namespace prefixes in this table are `Yulang.GeneralNominalCentered`.
Sources: [original obstruction](../../lean/Yulang/GeneralNominalCenteredCompletionAliasObstruction.lean)
and [progress/stable extension](../../lean/Yulang/GeneralNominalCenteredClassLocalAliasProgress.lean).

The enabled step records `output = 1` in the raw context: the journal already
entails it, while the raw context has a separating model with `output = list int`.
Calling this particular `finish` a stable final state would contradict the
existing `not_stable` theorem.

The actual terminal extension is a different state. The proved statement is
only a finite path to root/focus stability. It does **not** establish the
terminal state's G′ Local, preserved model, packet/edge inventory, or absence
of a generated Z child. In particular, absence of a Committed Frame at the
starting snapshot does not imply absence of Generated at a later state;
Generated includes both edge and alias closure.

**Answer to the proposed stable refutation: not established at this baseline.**
The current snapshot is nonstable; a stable extension exists, but persistent
selection and missing generation are still unproved. The required additional
statement would exhibit a reachable state `s`, generated focus `d`, and
`child ∈ children` with:

```lean
Stable registry s d ∧
GeneralNominalCenteredAdministrativeLocal.Local registry s d
  (.selected key children) ∧
¬ GeneralNominalSaturationState.Generated s.erased.current root child
```

That would refute GeneratedChildren directly; it need not be the fixed
executor's particular terminal. No such statement is claimed here. Proving it
by persistence needs control of all installations, current Fresh and source
locations, reports/Prepared, support and cycle guards, and registrations/edges
through refresh and reobservation. Monotonic Known alone is insufficient.

### The blocker is more precise than “the final common-model guard”

The plain occurrence has no named output request. Its packet's generated
schema is empty (`CompletionAliasLocal.child_schema`), and `child_branch`
constructs its branch in every current raw context model. The contradictory
`out = list int` equation is demanded by the **other** occurrence.

`GeneralNominalMaterialization.rootRequests` enumerates only the packet
occurrence's output requests; `Packet.Holds` uses that occurrence's BranchModels.
Joint is what checks the other alias. In the fixture, `no_joint` already
precludes Feedback Installable, independently of the final centered witness.
The recorded parent still says `output = int`; no R packet records its
conflicting output equation.

Deleting the final common-model conjunct alone leaves Joint blocking the step.
Deleting Joint as well and installing only the plain packet would omit the
other alias's output request rather than record the required conflict.
The general centered witness gate forbids inconsistent installation, but the
fixture also exposes the need for **class-wide output effects after head
selection**, not class-wide candidate filtering.

## 3. Proposed repair and proof impact

### Common semantic split, required for either implementation option

Use new additive definitions; preserve the existing files as historical APIs.

1. Define a head-only Survivor from visible checked declarations, unnamed
   arguments, normalized head inspection, and its capture/interval constraints.
   Split `Prepared`, `Failed`, and `InspectionPending` accordingly. Neither
   `RequestReady`, named-output Consistent, nor Joint may remove a head candidate
   or resolve ambiguity. Keep existing legitimate unknown-head, support, merge,
   and K2 rules, without inventing a deferral for output conflict.
2. Once that set is uniquely keyed, form the chosen implementation's output
   effects for **all requests in its alias class**, using the same centers and
   shared captures. Equal output names denote the same associated result;
   every requested target is constrained to it, including a request present on
   only one occurrence. Existing `outputAtoms` equates matching targets on both
   sides; it does not itself supply these missing class-wide chosen equations.
3. Test or record those effects only for the chosen key. Never try another
   head candidate when the output equations conflict. Distinguish a genuine
   contradiction of well-formed equations from failure to construct a frame,
   missing support, or an unfinished observation.

For example, proposed names could be `HeadSurvivor`, `ChosenClassEffects`, and
`OutputConflict` in a new `GeneralNominalCenteredOutputConflict…` module family.
`ChosenClassEffects` must be a symbolic equation relation, not the old Prepared
predicate with its existential consistency test. The conflict test is
unsatisfiability of current centered Models together with those chosen effects;
it is not negation of Installable or of PacketGuard. To attribute a new
contradiction specifically to the chosen outputs, require an inhabited
pre-state. If current Models is already empty, the same unsatisfiability test
detects pre-existing ordinary inconsistency instead. The new error contract
must distinguish that reason rather than blame a newly chosen implementation;
neither case becomes an additional pending rule.

### Recommended minimal diagnostic repair

Represent an explicit **post-selection output conflict**, without requiring an
inconsistent installation just to expose the error. This can inspect the
chosen class's prospective equations in the current state. Keep successful
installation on the existing journal machinery, but require head-only uniqueness
as an additional guard: the old output-filtered uniqueness must never authorize
a step when there are two matching heads. A successful class completion also
needs a common realization of its chosen class effects, not merely independent
witnesses for separate aliases. General realization/value-support production
remains a proof obligation.

Class realizability is only an existence guard. Keeping the old install update
unchanged does **not** record every alias-class effect. A successful completion
must additionally establish coverage, for example by actually committing the
relevant member packets through the restricted Step. The required conclusion is
that every successor model satisfies all of the chosen class effects, not just
that some prospective model satisfies them. If member-packet completion cannot
supply this, add stored class equations and extend Models and the installation
model law. That larger repair is no longer justified by Step inclusion. This
coverage obligation is distinct from both common-model existence and child-edge
coverage, and is not discharged here.

For an integrated diagnostic, add OutputConflict as a genuine reason for
`.rejected` **after unique-head choice**, and exclude it from the selected case.
Keep the head Survivor set intact; ambiguity still wins when there are two
heads because OutputConflict is defined only for a unique head. Existing K2
and unknown-head priorities are retained. This needs a new boundary/target
interface with an explicit conflict predicate, new SafeKnown/Local/Classify and
RejectReason definitions, and the corresponding Exact and NoFalseRejection
clauses. Existing Frontier/Tree constructors could remain unchanged: the
additional reason is an ordinary type error, not another K2 reason.

This is a proposal for an **additive successor contract**, not a modification
of B4TargetV5 or its main statement. V5's fixed Local and RejectReason cannot
express that integrated repair faithfully.

A smaller reporting interface could instead return an ordinary-typing error
status alongside the head-resolution tree. It would require a separate
soundness/completeness contract for that status. V5 would then describe only
the role projection, not the type-error report; its unconditional
GeneratedChildren obligation would still need resolution. A wrapper alone is
not a proof of the present B4 composition.

### Which definitions and fields are affected

For the integrated diagnostic proposal, the concrete changes are new versions
of RecursiveCandidates' head applicability/inspection predicates; a chosen
alias-class effect relation; centered Installable/PacketGuard/At/Step/Stable
wrappers; boundary fields/frontiers; and the canonical executor's diagnostic
and exit predicates. Successful transitions can initially be defined as a
**restriction of the existing Step**, adding head uniqueness and class
realizability to installation. This preserves the current State, Initial,
Models, and update functions. The error is a diagnostic of the failed chosen
equations, not a failed transition. No claim is made that this restriction
already solves the outstanding production obligations.

| Previously proved field | Required treatment for this proposal |
| --- | --- |
| progress | Reuse old accessibility through Step inclusion and old reachability; prove the restriction bridge. |
| closure | Reprove the structural halted-to-stable/generated closure for the new Step/Stable. |
| stepModels | Transfer through Step inclusion; Models is unchanged. |
| execution, halted | Rebuild the executor for the restricted relation; an old terminal is not automatically reached by allowed new steps. |
| frontierLocal, localIdentity | Reprove for head-only candidates and explicit post-choice error Local. |
| whereAccessible | Reprove the selected-child rank facts using head-only frames; old selection is not implied. Error leaves contribute no children. |
| treeExecution | Reprove for the new diagnostic and Local; generic tree-resolution machinery remains useful. |
| canonicalLocalOrder | Extend permutation transport to head-only selection, class effects and their consistency; rebuild canonical exit lifting for the restricted Step and new Local. |
| dictionaryRefl | Reuse unchanged. |
| initialReorders | Reuse unchanged. |

The two previously open fields remain open: GeneratedChildren must establish
actual child production for non-error selected nodes; EvidenceNode must be
adapted by its owner to the new head/effect contract. The V5 composition theorem
itself cannot be reused unchanged for the integrated new rejection reason.
The fourteenth-field accounting therefore does not carry over as “12 closed”
without the listed new proofs. The Step-inclusion entries are conditional on
implementing successful class-effect coverage with existing updates. An extended
class-effect ledger would require an additional model/trace transport argument
instead, as well as changes to Models and stepModels.

### Alternative: record inconsistent constraints

It is also faithful to choose the unique head, record its entire class-wide
output effects, and let the resulting Models set become empty. This requires
more than dropping the last PacketGuard conjunct: the old Prepared consistency,
raw common-model test, and Joint witness must cease to veto that already-made
head choice, and the installation must actually retain the other aliases'
output equations. The stored class-effect semantics and installation model law
would need extension.

This enlarges the Step relation. Its accessibility, executor, and permutation
simulation would need new proofs; the existing retrospective-model proof cannot
be transferred merely by relation inclusion. An explicit absorbing error state
or equivalent stopping rule would prevent continued normal saturation after a
certified contradiction. Model restriction can still hold, since adding
constraints only removes models, but an empty model set alone does not satisfy
a diagnostic obligation. An explicit ordinary-typing error contract is still
needed, either beside V5 or in the additive successor target described above.

This alternative is not selected or implemented in this turn. The recommended
next scope is the head/effect split plus an explicit post-choice error contract,
with the supervisor deciding its integration with the frozen B4 statement.

## Validation and limits

This note is based on the definitions and existing theorems at the stated
baseline, with a separate read-only review of the final-state claim, inherited
output filtering, and V5 diagnostic limitation. No new theorem is claimed;
no Lean file, build configuration, specification, or Git reference was changed.
No Lean build or audit was run for this documentation-only turn. Documentation
links and the permitted file scope were checked; `git diff --check` exited 0.
