import Yulang.CorePresenceGenerationExact
import Yulang.Common

/-!
# Monomorphic, ordered pattern prefixes in common inference environments

A pattern extends its incoming lexical environment with the bindings it has
already produced. This module establishes the symbolic/semantic environment
bridge needed by that extension, for arbitrary original environments and
arbitrary shared type slots. It does not infer the types of the bindings or
claim the full pattern-generation theorem.

Every prefix entry is a pure monomorphic binding. The source order is retained;
there is no reversal, freshening, value generalization, or lookup by name in
this bridge. A later default expression is generated in exactly this extended
environment, including all computation instances of captured outer bindings.
-/

namespace Yulang.CommonPatternEnvironment

open Core.PresenceGeneration

abbrev NamedTerms (α : Type) := List (Nat × TyTerm α)
abbrev NamedTypes := List (Nat × Common.Ty)

/-- Evaluate shared type references without changing the source binder order. -/
def evalTypes (ρ : α → Comp Common.model) (bindings : NamedTerms α) : NamedTypes :=
  bindings.map fun binding => (binding.1, binding.2.eval Common.model ρ)

/-- Pattern bindings carry values, hence an empty immediate row. -/
def semanticPrefix (bindings : NamedTypes) : List (Binding Common.model) :=
  bindings.map fun binding => .mono (Comp.pure Common.model binding.2)

/-- This never generalizes a binding, even when the matched expression is a value. -/
def symbolicPrefix (bindings : NamedTerms α) : SchemeEnv α :=
  bindings.map fun binding => Scheme.mono (CompTerm.pure binding.2)

@[simp] theorem evalTypes_names (ρ : α → Comp Common.model) (bindings : NamedTerms α) :
    (evalTypes ρ bindings).map Prod.fst = bindings.map Prod.fst := by
  simp [evalTypes, List.map_map]

@[simp] theorem evalTypes_append (ρ : α → Comp Common.model)
    (first last : NamedTerms α) :
    evalTypes ρ (first ++ last) = evalTypes ρ first ++ evalTypes ρ last := by
  simp [evalTypes]

@[simp] theorem semanticPrefix_append (first last : NamedTypes) :
    semanticPrefix (first ++ last) = semanticPrefix first ++ semanticPrefix last := by
  simp [semanticPrefix]

@[simp] theorem symbolicPrefix_append (first last : NamedTerms α) :
    symbolicPrefix (first ++ last) = symbolicPrefix first ++ symbolicPrefix last := by
  simp [symbolicPrefix]

/-- All instances at every lexical index are preserved by the entire prefix,
not merely the minimum type of each individual binder. No condition is imposed
on the free assignment, and arbitrary captured outer schemes are retained. -/
theorem monomorphic_prefix_environment_exact
    (ρ : α → Comp Common.model) (bindings : NamedTerms α)
    (symbolic : SchemeEnv α) (semantic : List (Binding Common.model))
    (outer : EnvRel Common.model ρ symbolic semantic) :
    EnvRel Common.model ρ (symbolicPrefix bindings ++ symbolic)
      (semanticPrefix (evalTypes ρ bindings) ++ semantic) := by
  induction bindings with
  | nil => exact outer
  | cons binding rest ih =>
      simpa only [symbolicPrefix, semanticPrefix, evalTypes, List.map_cons,
        List.cons_append, CompTerm.eval, CompTerm.pure, RowTerm.eval, Comp.pure]
        using ih.mono (CompTerm.pure binding.2)

end Yulang.CommonPatternEnvironment
