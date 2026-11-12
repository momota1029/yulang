# Cycle144: actual support snapshot readback

## Design and ownership

Fresh integration `6cff680c`, I25 support-aware boundary; cycle143 source retained.
Do not alter Astra-owned state/Step/Stable/Generated, Audit.lean or README.md.
Use new small modules and a small cycle audit. No runtime/language feature is added.

SupportReadback supplies a missing assembly step: cycle143 required a completed
Classify dictionary. Here finite Classify is constructed by accessibility of the
independent current Local child relation, preserving child list order and repeats.
It then yields a single payload whose Evidence holds for every final model.
Premises are actual Reachable, Stable, local selection at every generated demand,
Joint at those selected demands, and independent where accessibility. Neither
Classify nor Evidence nor a ready-made output is an input. Root Joint also proves
this model class is inhabited. This remains conditional, not general V5 completion.

Parallel investigations: complete the actual recursive example's final Local /
Classify / Stable as far as proved; and derive journal coherence for structural
early-merge schedules rather than assuming cross-class key equality. Both are
explicitly scoped, and will not be counted as general V5 bridges.

## Verified first slice

`lake build Yulang.GeneralDictionarySupportReadback --wfail`: initial two public
theorems passed (668 jobs). Final audit and final expanded build are recorded in
the cycle report. General V5 remains six unconditional fields / eight open.

## EarlyMergeChoices and regression

`UncommittedClass` means no installed packet belongs to an alias class. `Early`
allows merging if at least one side is uncommitted. The actual-transition trace
`Scheduled` adds only this structural restriction at merges; administrative
steps (including certified reobservation) and enabled installs are unchanged.
`scheduled_formed` embeds it in actual SourceFormed, `scheduled_coherent` proves
journal-key consistency, and `recorded_choices` obtains the key half of Joint
for a recorded root. No key equality or Current assumption is supplied.
The first regression is an inhabited nonempty installation/reobservation trace,
showing Coherent does not imply Current. It has no merge and is not offered as
evidence of the unrestricted executor's merge ordering.

## Independent local readback and its converse

`GeneralDictionaryLocalReadback.Reach` follows only current selected Local child
edges. `classified_exists` constructs a dictionary from selection on this closure
and its accessibility, without any Step/Stable/Joint/model premise. This is weaker
than requiring every historical Generated demand to be selected. The separate
`support_dictionary` adds actual reachability, stability and model-conditional
Joint for semantic soundness; unlike `SupportReadback.premises_inhabited`, it does
not guarantee a model exists.

`GeneralDictionaryLocalReadbackExact.success_iff` proves the converse too:
Classify selected has a finite dictionary iff the entire independent selected
child closure is locally selected and its Child relation is accessible. Unique
ensures there is no additional hidden selected child branch. This is a syntactic
success characterization, NOT operational termination, general whereAccessible,
canonical order, or a model existence result. Read-only review confirmed this
separation and found no circular output assumption.

## Concrete classification and early-merge boundary

`SupportRecursiveClassification` proves actual current parent Local key1,
terminal Local key3, support-ready guards, and two-node Classify on the same
inhabited reachable snapshot already carrying all-final-model Evidence. Its
module alone does not establish Stable. Independent stability work is separate.

`EarlyMergeBoundary.packetFree_no_merge` proves a reachable empty journal cannot
perform a novel merge, as its only site is the root. `initial_install_merge`
constructs a real early merge after a legal first install if that install emits
a distinct child and a present distinct site has the same inputs. It derives
MergeGuard from formed Exact; this is parametric and NOT an instantiated example.

## Concrete stable recursive completion

`SupportRecursiveClosure` now independently closes the previously missing Stable
obligation for exactly the Display(List Int) installation fixture. It proves:
- varying-source models prevent ANY certified refresh from making a reserved
  origin (>=2) known; PointClosed alone is not misused for this conclusion;
- ContextComplete for this fixture, PointClosed, exact two sites and one edge;
- generated demands are only the parent and child; unequal List Int / Int
  inputs rule out cross-site merging;
- every installable packet at either generated demand is already Committed;
- feedback Stable then actual support Stable, including certified reobservation.
The same snapshot has actual two-node Resolves/Classify, a concrete model and
recursive source Evidence for EVERY final model. Terminal child requires no
fake installation. This is a genuine fixed-fixture stable completion, not the
unrestricted executor, general Progress, or a general Joint theorem.

`SupportRecursiveJoint` also discharges concrete parent/child Joint, including
current BranchAt for every final model and recorded key consistency. The
`SupportReadbackRegression` applies the generic extraction theorem with no
unproved premise: its Acc proof directly uses the two selected Local shapes,
not the already constructed Classify derivation. Extraction returns Classify
and all-final-model Evidence; only afterwards classification functionality
identifies the resulting payload as `.node 1 [.node 3 []]`.

## Exact trace shape and nontrivial early merge

`SupportRecursiveTrace` strengthens the concrete completion: any actual Step
from its initial source reaches exactly the exhibited finish (support proof
choices do not change install output); no Step leaves finish. Hence every finite
trace ends at start or finish, and Stable endpoint iff finish. This is a fixed
fixture, not a general progress/canonical-order field.

`EarlyMergeExample` supplies the missing instantiated positive example. A checked
Display(List Int) declaration has two equal where inputs with distinct clause
IDs. A real source-guarded parent installation emits two different child IDs,
then the real support merge identifies their same inputs. The final journal has
a parent packet and a nonempty alias ledger, and a concrete model and Coherent
are proved. Both merged child classes were uncommitted. No claim about merging
two already-recorded classes, stable completion, or general Joint is made.
