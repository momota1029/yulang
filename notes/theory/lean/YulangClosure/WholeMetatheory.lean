import YulangClosure.NativeScopeTransformer
import YulangClosure.OriginalEffectHygiene
import YulangClosure.OriginalPrincipality
import YulangClosure.OriginalInferenceTermination

/-!
Checked components for the ORIGINAL whole-Yulang metatheory obligation.

This import surface does not replace `SourceProblem`, instantiate its original
roots, or assert that full soundness, hygiene, principality or inference
termination has been proved. It exposes four concrete advances together:

* the native scope transformer's finite content algebra and coherent renaming;
* original publication provenance and the local owned-return/Name invariant;
* the existing finite-use quotient's exact joint descent criterion;
* well-founded local native Context traversal, with callback/global inference
  progress left at its actual owner.

The original supported source domain, complete Call, shared scoped witnesses,
lawful future uses and native execution correspondences remain required. Each
component states the material premises and source boundaries in its own file.
Use `AuditWholeMetatheory.lean` for the complete originating-theorem census,
including private and generated declarations, for these four new modules.
-/
