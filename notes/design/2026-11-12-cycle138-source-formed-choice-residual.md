# Source-formed choice residual after the raw counterexample

`GeneralDictionarySourceChoiceVisibility.visible` proves by the actual feedback
formation trace that every recorded packet declaration belongs to the same
source registry. It requires neither a model nor stability. This excludes
invisible stale choices even in inconsistent journals, where extracting facts
through a model would not be available.

For a singleton registry, `singleton_choice` fixes each packet declaration,
`singleton_key_coherence` gives alias key coherence, and
`singleton_selected_coherence` ties that coherence to the actual current
feedback classifier's selected key. The latter is precisely the first Joint
conjunct, derived from source formation, registry shape and actual selection;
no Joint or source Evidence premise is used.

The full SourceFormed + Stable + selected theorem is not proved here. Even in
the singleton case, Joint also requires one simultaneous journal-model branch
witness for every aliased site's retained output requests. Local Survivor
provides a branch model for the current occurrence, not automatically a journal
model or a simultaneous model for other sites. In a general registry, visibility
alone also does not identify a historical packet's selected key with today's
selected key. Refresh and equality feedback preserve models but may change
inspection context; a historical-to-current applicability theorem would be
needed. Merge has no explicit ChoiceCompatible guard, so alias coherence must
be established from semantic/source invariants rather than presumed syntactic.

These are residual obligations, not a new counterexample to source-formed
execution. No target/interface changes are made. Four public declarations pass
direct Lean and trust-zero audit with standard axioms only.
