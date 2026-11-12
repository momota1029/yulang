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
