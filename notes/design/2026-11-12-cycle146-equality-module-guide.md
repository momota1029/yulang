# Cycle146: finite equality completion and exact observations

Authority: fresh `integration/m1-final@6cff680cc`, I25 (inbox blob
`3d918314663c6642f9060cf54ac94fd1dc592205`). Existing support State,
Step, Stable and Evidence are unchanged. The current general V5 result remains
6/14 bridges proved, 8/14 open.

## General results, not a concrete-case completion

- `GeneralDictionaryEqualityObservations`: for arbitrary roles, registry,
  journal state, root, key and two registered source endpoints, actual
  journal-entailed equality feedback preserves BranchAt at the same journal
  assignment and Joint iff. Reverse transport does not assume two existential
  models agree. The finite `Equates` certificate preserves Models, full
  recursive Evidence at each original journal model, and Joint (including
  absence) for every root/key. Equates alone is NOT actual reachability:
  novelty is checked by the separate completion proof below.
- `GeneralDictionaryFiniteEqualityCompletion.complete_list`: arbitrary finite
  list of registered pairs entailed by the journal has an endpoint reached by
  real support Steps. A pair already RawEqual is skipped; otherwise the exact
  administrative equate constructor and its novelty premise are used.
  Journal Models and source membership are unchanged, raw models only shrink,
  and every listed pair is RawEqual. The ordinary-context extension and
  equality-only certificate are provided, not assumed.
- `complete_sources`: filter the finite Cartesian list of current sources by
  semantic Equal, then apply complete_list. At the endpoint every registered
  semantic equality is raw equality. Source-domain and Models equivalence
  pull an endpoint equality back to that initial finite list. This is
  **classical existential completion**, not an executable equality decider,
  computable scheduler or total inference implementation. No consistency
  assumption is hidden; the theorem also covers an empty journal model set.
- `GeneralDictionaryFiniteEqualityObservations.complete_observations`: choose
  ONE endpoint before quantifying all roots, keys, models and payloads. It is
  actual-Step reachable and EqualityComplete; all Joint observations and all
  full recursive Evidence at original journal models are unchanged. A
  SourceFormed start yields the SAME SourceFormed endpoint.
- `GeneralDictionaryVariableJournalMerge`: an arbitrary recorded historical
  packet may certify two output sites through actual-mode occurrences of the
  same parent binder for each matching output name. Existing materialization
  coherence derives outputAtoms for EVERY journal model. Real merge function
  Models and full Evidence are equivalent. No scalar-only restriction; no
  current-context packet classification or arbitrary distinct-packet
  compatibility is inferred. At this checkpoint concrete non-scalar
  instantiation is not claimed.

## What remains open

EqualityComplete disables only fresh equality feedback. Refresh, enqueue,
reobservation, installation and merge may still apply. It is not Stable.
The completion therefore does not close general V5 progress, execution,
halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode or
generatedChildren. Separate Joint witnesses are still not a common witness
for a general merge. No fresh language rule or empty-journal interpretation
was introduced.

## Checks and oracle

Focused Lean 4.35 builds and a small `Audit/Cycle146.lean`, with trust=0 direct
source checks. Full repository build is intentionally not run (I25 cycle
scope / standing runtime restriction). `lean/Audit.lean` and `lean/README.md`
are frozen. Existing source is unchanged except appended root imports.
Fresh `work/dots-audit@55574b605` oracle was read; X1–X25 runtime observations
remain separate from these Lean proofs. No runtime agreement is inferred.

## Second checkpoint: quantitative and concrete progress

`GeneralDictionaryEqualityStepBound.complete_sources_quadratic` strengthens
mere finiteness to an explicit bound: for every tracked starting journal with
N entries in its current source list, there are an endpoint and a natural n
with a `Counted` path of n actual support Steps, n ≤ N², EqualityComplete and
an Equates certificate. The proof constructs only equality transitions; the
Counted relation itself counts the existing support Step relation. Duplicate
list entries only enlarge the upper bound. This is a bound on transition
count, NOT on deciding semantic entailment or a full execution.
Independent read-only review checked the finite filter, same-model/source
transport and duplicate-source cases.

`GeneralDictionaryOutputMergeRefresh` extends the cycle145 concrete actual
output-merge example. The old `next` is proved **not Stable**, by supplying a
real administrative refresh. A Fin4 context now records outputTarget10 and
outputTarget11 as int observations. Both identities were already registered;
source membership is exactly preserved. Old state had two slots, new has
four; the model set is unchanged, with the explicit old model retained.
The actual Initial-to-output-merge-to-equate-to-refresh path is Reachable and
SourceFormed. This is not a hand-built unreachable journal counterexample.

`GeneralDictionaryOutputMergeRefreshEvidence` rebuilds the parent and both
child Instances in the NEW context and gives the SAME ordered three-node
root dictionary `[1;7;7]` full recursive Evidence for EVERY post-refresh
journal model. It does not substitute old-context Evidence. Final Stable and
new-context Classify are not asserted by these two modules.

`GeneralDictionaryVariableJournalExample` witnesses the historical variable
merge premise concretely: a checked parent packet generates two actual
binder-0 output requests with common name 0 and distinct allocated target
identities. There is an explicit model of the journal and merged journal;
all-assignment Models equivalence follows. The witness values are int,
not a concrete nominal-valued example. The journal is manually assembled:
SourceFormed/reachability is NOT claimed. General variable-merge theorem
still has no scalar type restriction.

## Third checkpoint: actual Stable endpoint, not just Evidence

The SAME Fin4 `refreshed` now has every rule closed:

- `OutputMergeRefreshClassification`: actual support Local selections and
  full three-node Classify, not an assumed classification premise.
- `OutputMergeInstallClosure`: arbitrary enabled packet at any Generated
  focus is semantically Committed. Generated is exactly root or either child;
  a physically missing child packet does not imply installation is novel.
- `OutputMergeSiteClosure`: every Generated focus is already present, and all
  SameInputs sites are already Alias. Enqueue and merge novelty both fail.
- `OutputMergeContextComplete`: every raw context model satisfies the historical
  packet and all site obligations. Thus every semantic Equal is RawEqual.
- `OutputMergeObservationClosure`: the only nominal descriptor is point-valued,
  so descriptor reobservation cannot improve it.
- `OutputMergeRefreshClosure`: any source other than 0,1,output10,output11 can
  be changed from int to str while retaining a genuine journal model. An
  exact Refresh cannot make that source Known in both models. The four
  constrained sources are already Known. No all-sources-Known premise is used.
- `OutputMergeStabilityResidual` enumerates the unchanged support At rules;
  `OutputMergeStable.stable_classified_dictionary` discharges the last refresh
  residual and proves actual Reachable, inhabited, Stable, Classify and full
  current-context recursive Evidence for EVERY final model at ONE fixed state.

An independent reader checked the full constructor coverage and re-ran the
Stable module with `--trust=0`. The earlier checkpoints' statements that final
Stable/Classify were not yet asserted are now superseded for THIS fixture.
The arbitrary-registry V5 bridge count is still 6 proved / 8 open.

## General completeness preservation, with its exact restriction

`GeneralDictionaryContextCompletePreservation` proves ContextComplete is
preserved by every administrative update, including refresh/reobservation,
and by the actual merge function. Merge need not preserve the old model set:
its new raw equations supply precisely the new obligations.
`OrdinaryEndpoints` restricts an ACTUAL support Step with an additional
administrative-or-merge endpoint description, and the finite trace theorem
preserves completeness from an explicitly complete START. It does not
identify a particular constructor proof and does not assume the desired
endpoint completeness. Installation is not covered, and prior actual
reachable-incomplete-installation counterexamples remain valid.

## Exact general residual after the concrete success

For arbitrary reachable Stable selected focus, derive Joint in that SAME
journal: matching packet keys over its alias class, and a SINGLE journal
model realizing BranchAt simultaneously for every related site. Existing
`reachable_joint_evidence` handles the subsequent source Evidence reasoning.
Separate existential branch witnesses, concrete three-site enumeration,
scalar output facts or the present ContextComplete fixture do not prove this
general bridge. No general V5 evidenceNode claim is upgraded.

The Joint route above is a **sufficient remaining bridge**, not a proof that
Joint is logically necessary for V5 EvidenceNode. V5's EvidenceNode also
supplies a particular journal model and child Evidence; a weaker Joint lemma
may use those premises, or another proof may bypass Joint. Calling the
unconditional stable-selected→Joint implication “minimal” would overstate
what has been established. The current theorem `reachable_joint_evidence`
still takes Joint explicitly alongside those model/child premises.
