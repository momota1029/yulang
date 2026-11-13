import Yulang.GeneralNominalSharedCaptures

/-! Bare variable emissions copy certified inherited origins. Compound inputs
retain the existing conservative fallback. Soundness is a theorem of the
emitter and local capture certificates, not a supplied emission-model field. -/
namespace Yulang.GeneralNominalSharedEmission
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging GeneralNominalRecursiveInspection
open GeneralNominalSharedCaptures

abbrev clauseChild := @GeneralNominalFeedbackSites.clauseChild

def OriginAt (packet : Packet roles) (child : Occurrence roles) (position : Nat) (origin : Origin) : Prop :=
  ∃ clause ∈ packet.declaration.requirements, ∃ valid : clause.Signature roles,
    ∃ index : Fin (roles clause.role).arity,
      child = clauseChild packet clause valid ∧ position = index.val ∧
      ∃ name, Usable packet name origin ∧
        GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name

theorem origin_sound (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) (origin : Origin)
    (recorded : OriginAt packet child index.val origin)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    (∃ actual, Observes model origin actual) ∧ ∀ actual, Observes model origin actual →
      GeneralNominalCaptureMerges.Fits model (child.demand.arguments index) actual := by
  obtain ⟨clause,_,signature,position,rfl,same,name,usable,pattern⟩ := recorded
  have equal : index = position := Fin.ext same
  subst position
  have bounds : (clauseChild packet clause signature).demand.arguments index =
      (GeneralNominalPacketSupport.capture packet).inputs name := by
    change GeneralDeclarationDemands.inputInterval _ _ _ = _
    simp only [GeneralDeclarationDemands.inputInterval,pattern]
    rfl
  rw [bounds]
  exact usable.2 model valid

noncomputable def childOrigin (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) : Option Origin := by
  classical
  exact if h : ∃ origin, OriginAt packet child index.val origin then some (Classical.choose h)
    else GeneralNominalFeedbackSites.childOrigin packet child index

noncomputable def childSite (packet : Packet roles) (child : Occurrence roles) : Site roles where
  occurrence := child
  inputs := List.ofFn (childOrigin packet child)
  arity := List.length_ofFn

theorem retains (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) (available : ∃ origin, OriginAt packet child index.val origin) :
    ∃ origin, (childSite packet child).inputs[index.val]? = some (some origin) ∧
      OriginAt packet child index.val origin := by
  classical
  exact ⟨Classical.choose available,by simp [childSite,childOrigin,available],Classical.choose_spec available⟩

theorem child_sound (packet : Packet roles) (child : Occurrence roles)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    SiteHolds (childSite packet child) model := by
  classical
  intro index origin recorded
  change Fin (roles child.demand.role).arity at index
  have entry : childOrigin packet child index = some origin := by
    change (List.ofFn (childOrigin packet child))[index.val]? = some (some origin) at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact Option.some.inj recorded
    · contradiction
  by_cases available : ∃ origin, OriginAt packet child index.val origin
  · have same : Classical.choose available = origin := Option.some.inj (by simpa [childOrigin,available] using entry)
    subst origin
    exact origin_sound packet child index _ (Classical.choose_spec available) model valid
  · apply GeneralNominalFeedbackSites.child_sound packet child model valid index origin
    change (List.ofFn (GeneralNominalFeedbackSites.childOrigin packet child))[index.val]? = _
    rw [List.getElem?_ofFn]
    split
    · rename_i bound
      have sameIndex : (⟨index.val,bound⟩ : Fin (roles child.demand.role).arity) = index := Fin.ext rfl
      rw [sameIndex]
      exact congrArg some (by simpa only [childOrigin,dite_eq_right available] using entry)
    · rename_i absent
      exact False.elim (absent index.isLt)

noncomputable def emitted (packet : Packet roles) : GeneralNominalFeedbackSites.Emission packet where
  sites := packet.children.map (childSite packet)
  exact := by simp [childSite,List.map_map,Function.comp_def]
  sound := by
    intro model valid site member
    obtain ⟨child,_,rfl⟩ := List.mem_map.mp member
    exact child_sound packet child model valid

end Yulang.GeneralNominalSharedEmission
