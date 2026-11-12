# Cycle151: two actual unrecorded children share one alias-class model

Status: proved concrete regression, not unrestricted V5 completion.
Date: 2026-11-12.

`GeneralDictionaryEarlyMergeScalarExample` builds a new registry containing the existing two-variable-child Display(List Int) declaration AND the visible terminal Int declaration. The original EarlyMerge fixture had only the parent declaration and its children were rejected. We do not reinterpret those old diagnostics as success: the new registry's parent Checked, selected classifier, installation, source guards, real source formation, actual merge and surviving journal model are separately proved in the new module.

After the actual parent install, clause 10 and clause 11 emit different occurrence identities with the same captured Int source. Their real recovered SameInputs and the support guard enable a merge. Both children remain unrecorded. The state is reachable from InitialSource, retains the parent packet, has a nonempty alias graph and a real journal model. No raw-state or vacuous-model example is substituted for reachability.

`GeneralDictionaryEarlyMergeScalarClassification` proves actual current selected key 3 and empty child list for each child. It checks source linkage, source-ID freshness, no raw/feedback K2, no pending candidate, actual scalar branch readiness, failure of the incompatible nominal parent head at a scalar child, and uniqueness against BOTH declarations. The parent declaration was not silently removed to make the child unique.

`GeneralDictionaryEarlyMergeScalarJoint` proves:

- The current sites are exactly the parent and two children.
- Alias preserves membership in the two-child identity class, while the parent is outside it.
- Consequently every Related site has the Int declaration's actual scalar structural shape and current selection.
- The original parent packet has an ordinary context-extension path through install and merge, so all premises of `covered_joint` are established directly.
- For EVERY supplied current journal assignment, both children have Joint. `same_assignment` additionally states explicitly that EVERY related site's `BranchAt` holds in that supplied assignment, avoiding a misleading pair of unrelated existential models.
- A concrete conjunction combines true reachability, inhabited journal Models, distinct child identities, actual Alias, both Joint conclusions and both matching-packet absences.

The merge is real and alias-nontrivial. The children are terminal and have no named output requests. Stability is deliberately NOT claimed for this new extended-registry state. The nonterminal variable-requirement Joint theorem is provided separately by `GeneralDictionaryUnrecordedVariableJoint`; this fixture is nonvacuity for a two-site alias class, not a claim that general nonterminal alias model extension or arbitrary named outputs have been solved. General V5 remains 6/14 supplied and 8/14 open.

## Validation

All three modules compile with Lean 4.35.0 `--trust=0 -DwarningAsError=true` in a separate output directory. Together with the three independent Joint modules, all 52 public theorem axioms and all declarations are checked by a scoped audit allowing only propext, Classical.choice and Quot.sound. Existing Audit.lean, README, semantics and earlier fixtures are unchanged. The new setup reuses the earlier fixture's proof structure but proves the new registry-specific statements rather than importing its old rejected-child conclusions.

The local failed classification attempts were a definitional Fin coercion in the scalar report rewrite and an implicit-endpoint binder in alias induction; both were corrected without weakening statements. Full project build and Yulang2 runtime are outside this worker's checks. The cycle's parent report records the integrated validation and publication status.
