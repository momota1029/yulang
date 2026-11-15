# I39: whole-target proof plan, cycle 211

Start 2026-11-15T11:28:16Z. Fresh integration a1ffb86db and I39 read.
This is a plan for the unchanged I38 boundary, not a new restricted target.

## Exact destination and quantified distinction

Let b = GeneralDictionaryDefaultBoundary208.boundary roles. EvidenceNode is
B4SkeletonV7.EvidenceNode b: for every checked value, reachable state/root,
every assignment satisfying b.Models, every root-or-generated selected demand,
stable demand and immediate children, and ordered child dictionary evidence,
produce evidence for the selected node. Thus an empty journal-model set makes
EvidenceNode vacuous at that state. GeneratedChildren has no model premise.
FreshCompletion208 is a sufficient helper for GeneratedChildren, NOT equivalent
to it: for every such stable selected *unrecorded* demand it demands an installable
extension with an existential joint journal/packet/effect model. Empty-model
states must not be hidden by silently adding an inhabitance hypothesis.

## Exhaustive semantic cases (orthogonal axes, not only examples)

1. Journal Models is empty / inhabited. EvidenceNode: empty is vacuous; inhabited
   must work model by model, not only on one convenient assignment. FreshCompletion:
   no such split is currently discharged; empty implies no Extension exists.
2. Exact current key-and-ordered-children recorded / not recorded. Recorded means
   Production208.Recorded, not merely a plan for the same occurrence.
   Recorded children: Production208.generated_of_recorded already unconditional.
   Current Frame for that stored plan: Recorded208.certificate and evidence_node
   finish local evidence. Historical context not equal to current: still missing
   general current-frame/total-packet reconstruction. Unrecorded: Availability208
   selected_effect gives a current Frame, Ready, key and exact children, not Holds.
3. Historical input point / genuine interval. Report-preserving replay uses the
   retained actual center (ExistentialReplay210), so arbitrary-center equivalence
   is unnecessary. This does not prove all selected nodes have a historical
   certificate, or arbitrary changes of report are replayable.
4. Head syntax: variable, scalar, structural constructors (all recursive pattern
   constructors), nominal, and mixtures/nested combinations. Structural descriptor
   revisions have RevisionEvidence210/ScopedRevision210 for existing evidence;
   nominal changing report only NominalFrame210's terminal one-nested-query
   nonpoint fragment. General nominal capture changes and nonterminal requirements
   remain open. Do not assume nominal constructor interpretation is injective.
5. Transition provenance: initial; administrative enqueue, equate, refresh,
   reobserve; explicit refresh; installation; merge. These exhaust Kernel208.At.
   Trace208 establishes registration/Built; Growth208 preserves sites and plans;
   Simulation208/Recorded208 preserve live default/explicit class obligations.
   Those are not current-frame replay. Installation creates a certificate at its
   own context. Equate/refresh preserve reports only under the appropriate report
   condition. Reobserve can change captures, bindings, and child bounds. Merge
   enlarges output classes and must preserve actual ordered child identity.
6. Output provenance: explicit / role-default / explicit override. Schema208 and
   Commitment208 cover all current aliases including one-sided requests, and
   regressions 199/202/204/206 delimit the old failures. No extra explicit-only
   guard may be introduced. Related output names must preserve equal targets.
7. Child list: empty / nonempty; exact order and multiplicity. Empty production is
   vacuous even if FreshCompletion fails. Nonempty recorded production is done;
   nonempty fresh production remains. Child evidence is an assumption of node
   assembly, not a license to assume parent packet Holds or generated closure.

Taking the Cartesian product of these axes covers selected demands; overlapping
syntactic categories are handled recursively, not by pretending a finite list of
worked examples is exhaustive.

## Dependency graph and largest missing bridge

Availability208.selected_effect gives effect.registry/snapshot/focus/key/children.
Availability208.selected_installable_iff and Live208.extension_iff reduce its
installation to (A) ChoiceCompatible and (B) a SINGLE joint assignment satisfying
journal Models, total packet Holds and effect Holds. Stable plus that extension
implies Kernel208.Committed via Commitment208.enabled_stable_committed; this gives
all-model packet meaning and default effects, then Certificate and evidence_node.
Production208.generated_of_fresh gives exact generated children from the same
extension. The twelve operational laws are already Composition208.twelveLaws.

The main hole is therefore not another isolated replay lemma. It is proving (A)
and (B) on the precise reachable selected domain, or obtaining current certificates
by historical replay where a common extension need not exist. OutputConflict has
an inhabited chosen-head antecedent: negating it does NOT alone produce (B).
Prepared has a raw head witness, not necessarily a joint live-journal witness.
A new universal HeadBaseline is already known false for recorded inconsistent
parents (AllocV7ParentBaseline.not_headBaseline).

## Counterexample-first tests before building the bridge

- Fresh unmerged sibling after another branch makes the journal inconsistent:
  can Local stay selected while exact Recorded is absent? If yes, FreshCompletion
  is false. A terminal sibling alone would NOT refute GeneratedChildren.
- Same scenario with a nonterminal fresh sibling: check generated edge absence;
  if fully checked/reachable/stable/selected, this may refute GeneratedChildren.
- In inhabited states, compare raw Prepared and ChosenHead under retained actual
  centers; reject arbitrary-center and constructor-injectivity shortcuts.
- Changed nominal captures in nonterminal declarations: compare literal child
  endpoint bounds, not just extensional expression values or equal list lengths.
- ChoiceCompatible after a merge: test conflicting historical keys. Local unique
  current head is not automatically historical key agreement without a transport
  theorem in one common model.

No counterexample or global theorem is asserted here. If a designated target is
refuted, publish a closed checked witness and delay proposal, then stop per I34.
No language decision is made by this plan. Subsequent work will target the first
suspect global bridge, before adding further restricted nominal fragments.

## First implementation step (11:36 UTC)

Before a new fragment, prove a syntax-unrestricted provenance bridge: in every
reachable corrected state, a raw registered demand is generated from the original
root, and conversely. This follows by induction over *all* actual Step cases,
including exclusion of enqueue from an already registered reachable demand.
Then actual total evidence implies registered/generated membership, via its Frame.
This separates graph production from existential model availability and identifies
exactly which child-production conclusion cannot be replaced by FreshCompletion.
No selection-domain restriction or model-inhabitance assumption is introduced.
A separate counterexample probe investigates the fresh empty-journal case.

## Global route simplification found at 11:37 UTC

Registration/generation equivalence is checked for corrected traces. Every Local
selected node has a current Frame, hence raw registration. Therefore in a fully
selected dictionary tree, each selected child is already generated from the root,
without assuming the stronger GeneratedChildren for arbitrary selected parents.
The old B4 composition uses GeneratedChildren only in dictionary soundness recursion.
Re-prove that recursion using selected-child registration, then reuse the twelve
operational laws to obtain the *same* B4TargetV7.Statement from EvidenceNode alone.
This does not prove GeneratedChildren or FreshCompletion, nor alter the statement:
it removes an unnecessarily strong sufficient dependency from the composition.

## Result and revised dependency graph (11:42 UTC)

The suspected FreshCompletion obstruction is now a closed Lean counterexample:
FreshProbe211Refutation.not_freshCompletion. It has checked registry, actual
repaired208 reachability/stability/selection, and exact absent Recorded. The third
unmerged terminal sibling remains selected in an empty journal. EvidenceAt and
its empty child-production obligation are separately proved vacuous.

The positive alternative is also checked: Composition211.composition derives
exactly B4TargetV7.Statement boundary208 executor208 from EvidenceNode alone.
SelectedGeneration211.classified_generated and Soundness211.dictionary_evidence
supply the recursive child scope. No new operational, language, or inhabitance
hypothesis replaces FreshCompletion; it is removed from the sufficient proof route.
General GeneratedChildren is still open, and EvidenceNode is still the single
unproved premise of this complete composition. Stop further research under I34
because the explicitly assigned FreshCompletion helper is false; publish the
refutation, delay proposal, unchanged-target alternative, and exact limitations.
