# Final scope and verification self-review

Last mathematical checkpoint: 3bb7d7734021ac8db05b0aba695d156742ab2a98.
Independent read-only review covered the preceding 21 modules in five batches.
A sixth request for GeneralRebaseSourcePool261 was not started: agent thread limit reached.
No independent rebuild was performed. The following review is by the author:

- same_sites, merge_pool, refresh_pool preserve the *candidate output list*, not context,
  raw model sets, capture semantics, Frame or executable inspection.
- absorbed_install assumes the preexisting Absorbed predicate: each emitted raw child's
  output is already an alias request of its occurrence in the old state. The forward
  proof separates old raw sites from added raw children and applies the old snapshot's
  request coverage to the latter. The reverse proof retains old raw sites.
- The result is membership equivalence. Duplicate sites/outputs may increase list length.
- installed_requests_covered combines this result with the actual new snapshot's
  mem_requests_iff. It does not assume every source installation is Absorbed, and does
  not claim fixed-pool closure for new public output targets.
- All new Lean sources and Audit files strictly compile. Full audits the new inductive
  declarations/recursors as well as theorem/def/abbrev names. Complete/AllTypes enumerate
  200 named declarations; this is not the full generated declaration count.
- CandidateBoundaryProbe is a kernel proof about an *internal unused candidate*, not a
  source rejection. The separate alias flood experiment is Python only, not Lean proof.

The selected-root audit reports 35 declarations outside its 41 roots. This includes
old-table first/stop regression APIs, error classifiers, candidate initial-model helpers,
and the reverse Trace→Runs API. It is not evidence that they are dead code; all are
strictly compiled and axiom-audited, and the exact list remains in reach-final.txt.
No frozen declarations were deleted based on this partial dependency analysis.
