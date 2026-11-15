import Yulang.GeneralNominalCaptureMerges
import Yulang.GeneralNominalPacketCodes
import Yulang.GeneralNominalCenteredHeadMatStepPackets
import Yulang.GeneralNominalCenteredHeadMatHeadShape

/-! A local allocation obstruction, not a reachable-state counterexample.
Repeated captures reuse their aggregate source names when bounds change. -/
namespace Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
open GeneralDeclarations GeneralNominalAllocation GeneralNominalCaptureMerges
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (All)
variable {lower upper : Nat}

 def twice (name lower upper : Nat) : Bindings := [(name,lower,upper),(name,lower,upper)]

 theorem repeated_lower {model : GeneralNominalCommonBridge.Assignment}
    (named : name ∈ declaration.inputNames)
    (holds : All CommonNominalFullCarrier.model model
      (merges state registry root declaration (twice name lower upper))) :
    Equivalent (model (source state registry root (origin root declaration.id 0 name 0))).1
      (.union (model lower).1 (model lower).1) := by
  apply (equations_exact model _ (.union (.var lower) (.var lower))).mp
  intro atom member
  apply holds atom
  apply List.mem_flatMap.mpr
  refine ⟨name,named,?_⟩
  simpa [twice,occurrences,capture,GeneralNominalAllocation.lower,GeneralNominalAllocation.upper] using
    List.mem_append_left
      (equations (source state registry root (origin root declaration.id 1 name 0))
        (.inter (.var upper) (.var upper))) member

 theorem union_self (value : Ty) : Equivalent (.union value value) value := by
  constructor
  · exact (common_union_is_join value value value).mpr ⟨subtype_refl _,subtype_refl _⟩
  · have both := (common_union_is_join value value (.union value value)).mp (subtype_refl _)
    exact both.1

 theorem repeated_lower_value {model : GeneralNominalCommonBridge.Assignment}
    (named : name ∈ declaration.inputNames)
    (holds : All CommonNominalFullCarrier.model model
      (merges state registry root declaration (twice name lower upper))) :
    Equivalent (model (source state registry root (origin root declaration.id 0 name 0))).1
      (model lower).1 := by
  have one := repeated_lower named holds
  have two := union_self (model lower).1
  exact ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

 theorem reused_lower_forces_equivalence {model : GeneralNominalCommonBridge.Assignment}
    (named : name ∈ declaration.inputNames)
    (one : All CommonNominalFullCarrier.model model
      (merges state registry root declaration (twice name first upper)))
    (two : All CommonNominalFullCarrier.model model
      (merges state registry root declaration (twice name last nextUpper))) :
    Equivalent (model first).1 (model last).1 := by
  have old := repeated_lower_value named one
  have new := repeated_lower_value named two
  exact ⟨subtype_trans old.2 new.1,subtype_trans new.2 old.1⟩

 theorem bottom_int_incompatible {model : GeneralNominalCommonBridge.Assignment}
    (named : name ∈ declaration.inputNames)
    (bottom : (model first).1 = .bottom) (integer : (model last).1 = .base .int) :
    ¬ (All CommonNominalFullCarrier.model model
        (merges state registry root declaration (twice name first upper)) ∧
      All CommonNominalFullCarrier.model model
        (merges state registry root declaration (twice name last nextUpper))) := by
  rintro ⟨one,two⟩
  have same := reused_lower_forces_equivalence named one two
  rw [bottom,integer] at same
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int) same

 theorem changed_state_incompatible {model : GeneralNominalCommonBridge.Assignment}
    (sameSeed : firstState.seed = lastState.seed)
    (named : name ∈ declaration.inputNames)
    (bottom : (model first).1 = .bottom) (integer : (model last).1 = .base .int) :
    ¬ (All CommonNominalFullCarrier.model model
        (merges firstState registry root declaration (twice name first upper)) ∧
      All CommonNominalFullCarrier.model model
        (merges lastState registry root declaration (twice name last nextUpper))) := by
  rw [← GeneralNominalPacketCodes.merges_seed firstState lastState sameSeed]
  exact bottom_int_incompatible named bottom integer

 theorem packet_reinspection_impossible
    {old current : GeneralNominalCenters.Plan roles}
    {model : GeneralNominalCommonBridge.Assignment}
    (registryEq : old.packet.registry = current.packet.registry)
    (rootEq : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
    (declarationEq : old.packet.declaration = current.packet.declaration)
    (sameSeed : old.packet.context.state.seed = current.packet.context.state.seed)
    (named : name ∈ old.packet.declaration.inputNames)
    (oldBindings : old.packet.bindings = twice name first upper)
    (newBindings : current.packet.bindings = twice name last nextUpper)
    (bottom : (model first).1 = .bottom) (integer : (model last).1 = .base .int)
    (oldValid : GeneralNominalCenteredHeadMatStepPackets.Holds old model) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds current model := by
  intro currentValid
  have one := oldValid.2.1.1.2.1
  have two := currentValid.2.1.1.2.1
  rw [oldBindings] at one
  rw [newBindings,← registryEq,← rootEq,← declarationEq] at two
  exact changed_state_incompatible sameSeed named bottom integer ⟨one,two⟩

end Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
