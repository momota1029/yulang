# Source evidence through journal-aware feedback

Status: Draft proof design, 2026-11-12. Scope: I-23 / item 5 only.

The concrete boundary is GeneralNominalFeedbackBoundary with the existing
GeneralDictionaryRecursiveEvidence.Evidence at state.context. The transition,
Stable, Survivor, and all source semantics remain Astra's definitions.
FeedbackK2 changes only the K2 predicates; it does not turn Survivor into Joint.
Consequently stable local selection still needs joint applicability to enable
installation. Origin recovery must preserve already present input origins,
so the feedback merge closure also discharges the legacy merge guard.

For every registry, state, root, selected key, and children, Stable plus the
actual feedback Local selected judgment plus Joint will yield a current-context
Committed packet, its source Instance in every journal model, and real Generated
edges for its children. Node assembly uses child Evidence at that same model.
The exact EvidenceNode field only needs the joint condition on states that have
a journal model. This is weaker than requiring Joint on every raw stable state;
GeneratedChildren has no model premise and retains the stronger residual.
Neither residual is claimed established from source formation.

A second useful target is persistence after an actual feedback install: for any
later feedback trace, the original packet's source Instance remains valid in
every final model and its children remain Generated. This is about the packet's
stored inspection context, not an unsupported transport to a refreshed context.
It covers real transition traces and certified refreshes without asserting that
all arbitrary stable journals came from such a trace.

Relevant audit: work/dots-audit notes/audit/y2-claims-casts-roles.md, especially
Y2-ROLE-003, distinguishes final selection components from general saturation;
no historical Yulang2 behavior is promoted into source semantics here.

## Checked refinement of the scope

The source-formation induction now proves, with no Joint premise, that every
packet recorded in any SourceFormed state supplies its original source Instance
in every model of that state, and every emitted child has a real Generated edge.
The proof follows actual enqueue/install/merge/refresh/equate constructors.
Old packets persist by model restriction and edge monotonicity; new packets use
the checked Installable metadata and installed commitment theorem. This does
not prove that a newly selected current-context candidate is such a packet, or
transport an old Instance across inspection-context regeneration. Those are
precisely the remaining connection to the current-context EvidenceNode field.

## Verification

Focused `lake build --wfail Yulang.GeneralDictionaryFeedbackEvidence
Yulang.GeneralDictionaryFeedbackEvidenceExamples` passed (629 jobs, most cached).
All 16 public theorems were individually inspected with `#print axioms` and
`#check @...` under `lean --trust=0`: only `propext`, `Classical.choice`, and
`Quot.sound` occur. No full build or full verification gate was run.

The regression uses Astra's actual two-step install/refresh example. Its journal
has an explicit model, the recorded parent retains its original source Instance,
its child remains Generated, and that child is rejected by the actual feedback
K2 rule. No completed parent dictionary is claimed from a rejected child.

Neither EvidenceNode nor GeneratedChildren is closed unconditionally on the raw
feedback boundary. The former now has the exact model-conditioned Joint residual;
the latter still needs unconditioned Joint for stable selected roots. The new
source-formed theorem removes all such residual hypotheses for already-recorded
packets, but does not identify a newly selected current-context packet with an
old recorded one. Aggregate imports, Audit registration, and the design index
are intentionally left to the integration owner to avoid concurrent edits.
