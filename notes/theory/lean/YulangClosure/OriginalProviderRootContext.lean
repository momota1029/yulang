import YulangClosure.OriginalProviderLexicalOwner

/-!
Root-input boundary for the authenticated `pub id x = x` lexical fixture.

`formalContext` is the existing Lambda preparation step, which prepends the
formal row to an incoming Context. These results describe its list data and
the observed formal lookup only. The two lists in the nonidentifiability
proof are mathematical witnesses, not authenticated prepared module contexts.
No closure/capture, semantic equivalence, root Context instance or provider
source judgment follows from them.

PSR-ROOT-CONTEXT-1 still requires an existing source preparation owner producing
ordered `Binding` rows and their exact translation to the incoming Context.
Source/import identity and opaque caller evidence do not supply that equation.
The original `provider_from_total_completion` remains unchanged, with its
Context, kernel, initializer, Shared, binding and publication premises explicit.
-/
namespace YulangClosure.OriginalProviderRootContext

open OriginalSource OriginalProviderSourceSolution OriginalProviderLexicalOwner
  OriginalProviderLexicalOwnerTrace

/-- Lambda preparation retains every incoming row, in order. -/
theorem formal_context_retains_incoming (incoming : Context) :
    (formalContext incoming).tail = incoming := by
  rfl

/-- The observed formal lookup is identical at two distinct incoming lists.
This prevents recovering the incoming Context from that lookup alone. Both
lookups use the same frozen lexical rows and the same formal identity. -/
theorem formal_lookup_does_not_determine_incoming :
    ∃ first second : Context, first ≠ second ∧
      lookupBinding (formalContext first) (occurrences providerOwnerRows).formalName =
      lookupBinding (formalContext second) (occurrences providerOwnerRows).formalName := by
  let row : Binding :=
    ⟨(occurrences providerOwnerRows).formalName,
      (occurrences providerOwnerRows).formal, .formal, none, none, some .value, true⟩
  refine ⟨[], [row], by simp, ?_⟩
  exact (body_name_lookup []).trans (body_name_lookup [row]).symm

end YulangClosure.OriginalProviderRootContext
