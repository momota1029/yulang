# Scope repair obligations after the raw EvidenceNode counterexample

This is an analysis of proof obligations, NOT a selected interface change.
The existing target, state type, Models, Stable, and Evidence are unchanged.
The first option remains to defer the repair to the target owner.

The negative theorem uses a concrete checked registry and concrete role set,
actual Stable, actual selected, and an inhabited model. Restricting only to
inhabited states cannot repair it. Requiring Stable again cannot repair it.
The existing SourceFormed invariant excludes it; that exclusion by itself does
not prove a positive EvidenceNode theorem for all source-formed states.

A provenance restriction must remain tied to the SAME registry. Packaging a
raw state together with a proof that it is source formed for *some other*
registry does not establish recorded visibility for the registry being solved.
Likewise, a packet's historical context must not silently replace the current
context in the independent semantic Evidence judgment.

If an owner-approved repair carries initial-source provenance, the composition
proof must transport it through actual execution and retain it at the final
state while recursing over generated demands. SourceFormed is indexed by an
origin root; a generated child's occurrence need not be that origin root. Merely
adding SourceFormed with the recursive child as root is not justified by the
current invariant. The initial-run input scope and preservation of provenance
must be specified together, rather than adding an isolated conclusion-shaped
local soundness assumption.

The new positive tools have deliberately separate quantifiers:

1. CurrentJournal: any restricted ordinary/fixed-view initial trace gives
   current Instance for every recorded packet, even if original-to-final
   ordinary Extension fails. It does not cover arbitrary view-changing refresh.
2. SelectedInstanceCoherence: any current Instance and actual selection at the
   EXACT same occurrence give the same key and ordered children, for arbitrary
   registry, without a Fresh/Joint assumption. Recorded variants additionally
   require the restricted initial trace and a final journal model.
3. SourceChoiceVisibility: arbitrary SourceFormed trace gives registry-visible
   packets without even a model premise. Singleton registries give alias key
   coherence, but not simultaneous branch witnesses.
4. JournalTree: Covered plus accessibility of ALL recorded child edges is
   sufficient to construct a finite tree. Neither condition is presently
   derived from arbitrary stable selection.
5. TerminalClassification: one actual two-step, view-changing execution is
   source formed, stable, inhabited, selected, classified, and semantically
   sound. It is a concrete positive regression, not a universal bridge.

The remaining general proof must still address alias-local simultaneous
applicability, current-context transport beyond fixed-view traces, and selected
child coverage/termination. None is proved by reusing the raw negative example
or by the single positive trace. The exact source signatures are in the cycle138
signature appendix; source owner approval is needed before altering the target.
