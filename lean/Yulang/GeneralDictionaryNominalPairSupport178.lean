import Yulang.GeneralDictionaryNominalPairExample178
import Yulang.GeneralDictionaryCenteredGuard177

/-! Source-only support for the finite nonpoint nominal regression. Neither
fresh capture endpoint needs head support: the inspector reads slots 0 and 1. -/
namespace Yulang.GeneralDictionaryNominalPairSupport178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralDictionaryNominalPairExample178
open GeneralDeclarationExamples (roles)
open GeneralNominalSupport

variable (root : Occurrence roles)
variable (bounds : ∀ i, root.demand.arguments i = (0,1))
local instance : NeZero (initial context root).current.context.state.base.slots := ⟨by change 4 ≠ 0; decide +kernel⟩

 theorem source_head (i : Fin 4) (small : i.val < 2) :
    Head state i.val (.nominal 0 1) (.nominal base i descriptor) :=
  Head.nominal (snapshot := state) i descriptor (by change (if i.val < 2 then some descriptor else none) = some descriptor; simp [small])

 theorem reads_exact : readsMany state
    (GeneralNominalInspection.queries state context.interpretation declaration) [(0,1)] = [0,1] := by
  rw [shape.query]
  decide +kernel

 theorem ready (i : Fin 4) (small : i.val < 2) :
    ReadyAt (initial context root) [] i.val :=
  source_ready (initial context root) i.val (.nominal 0 1) _ _ (source_head i small) (source_head i small) []

 theorem inspection : Inspection (initial context root) [] declaration [(0,1)] := by
  intro slot member
  change slot ∈ readsMany state (GeneralNominalInspection.queries state context.interpretation declaration) [(0,1)] at member
  rw [reads_exact] at member
  rcases List.mem_cons.mp member with one | tail
  · subst slot; exact ready root 0 (by decide +kernel)
  · have one := List.mem_singleton.mp tail
    subst slot; exact ready root 1 (by decide +kernel)

 theorem guard (bounds : ∀ i, root.demand.arguments i = (0,1)) : Guard (initial context root) root declaration [(0,1)] [] := by
  refine ⟨?_,?_,inspection root⟩
  · intro _ member; cases member
  · intro i
    rw [bounds i]
    exact ready root 0 (by decide +kernel)

 theorem decisions (bounds : ∀ i, root.demand.arguments i = (0,1)) (located : GeneralNominalRecursiveCandidates.arguments context root = some [(0,1)]) :
    DecisionGuard (initial context root) registry root [] := by
  refine ⟨?_,?_,?_⟩
  · intro _ member; cases member
  · exact (guard root bounds).2.1
  · intro d member role intervals found
    have same := List.mem_singleton.mp member
    subst d
    have eq := Option.some.inj (located.symm.trans found)
    subst intervals
    exact inspection root

 theorem value_guard (bounds : ∀ i, root.demand.arguments i = (0,1)) (checked : DeclarationChecked registry.constructors roles declaration)
    (site : GeneralNominalDemandMerging.Site roles) (same : site.occurrence = root)
    (located : GeneralNominalRecursiveCandidates.arguments context root = some [(0,1)]) :
    GeneralNominalValueSupport.PacketGuard (initial context root)
      (⟨registry,context,site,declaration,checked,[(0,1)]⟩ : GeneralNominalSaturationState.Packet roles) [] := by
  apply GeneralNominalValueSupport.source_packet
  constructor
  · subst root
    exact guard site.occurrence bounds
  · subst root
    exact decisions site.occurrence bounds located
end Yulang.GeneralDictionaryNominalPairSupport178
