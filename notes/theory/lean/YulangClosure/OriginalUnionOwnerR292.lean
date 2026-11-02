import YulangClosure.OriginalSourceChecking
import YulangClosure.OriginalAppConstructionR160

/-!
R292: checked route exclusion for the selected EI-All result constructor.

The authoritative computed-call-result-constructor (2026-10-24), section 4,
forms a COMPLETE COMPUTATION descriptor with source and original arm tags.
It is not the value UnionRegistration of OriginalSourceChecking. These two
audit theorems apply that distinction to R159's actual generated computation
premise. They neither formalize EI-All nor construct an original Catalogue,
Relations.alternative, descriptorFormation atom, or App admission.

The exclusion concerns ValueOccurrence and the direct union_*_shape helpers.
It does NOT exclude computation_shape, registered equations, or a future
source-grounded interpretation of EI-All. In particular Schema.registered
can transport a genuine defining equation; no global impossibility follows.
-/
namespace YulangClosure.OriginalUnionOwnerR292

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceAppAdmissionR159

/-- The computation comparison is an actual R159 local, for both arbitrary
children and every original context/annotation/singleton-formal alternative. -/
theorem app_computation_premise (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    Premise.checking ⟨.computation, mark.site, context,
      ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∈
        appPremises context mark callee argument := by
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

/-- At precisely the parent's unchanged ViewLogic extension, neither direct
value-Union shape helper can obtain its required occurrence for the actual
computation result local. No descriptor/world/witness equality is assumed. -/
theorem no_value_union_occurrence_at_app_result
    {s : Sorts} {View : Type} (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) :
    let after := environment.extend ⟨mark.site, .viewLogic, 0⟩
      (scopeCandidate environment occurrence (.logical .viewLogic data))
    ¬ Nonempty (ValueOccurrence s View readout after
      ⟨.computation, mark.site, context,
        ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩) := by
  dsimp only
  rintro ⟨valueOccurrence⟩
  cases valueOccurrence.mode

end YulangClosure.OriginalUnionOwnerR292
