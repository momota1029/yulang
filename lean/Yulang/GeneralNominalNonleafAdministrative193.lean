import Yulang.GeneralNominalNonleafSafety193
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafAdministrative193
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193
open GeneralNominalExamples (registry context state displayRoot displayChild model)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier

private theorem same_inputs_symm {models : GeneralNominalCommonBridge.Assignment → Prop}
    {first last : GeneralNominalDemandMerging.Site roles}
    (same : GeneralNominalDemandMerging.SameInputs models first last) :
    GeneralNominalDemandMerging.SameInputs models last first := by
  refine ⟨same.1.symm,?_⟩
  have relation := same.2
  generalize first.inputs = xs at relation ⊢
  generalize last.inputs = ys at relation ⊢
  induction relation with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨a,b,one,two,equal⟩ := head
    exact .cons ⟨b,a,two,one,fun m valid =>
      ⟨(equal m valid).2.1,(equal m valid).1,fun x y hx hy =>
        ⟨((equal m valid).2.2 y x hy hx).2,((equal m valid).2.2 y x hy hx).1⟩⟩⟩ ih

private theorem point_same_values {models : GeneralNominalCommonBridge.Assignment → Prop}
    (valid : models m) (first last : GeneralNominalDemandMerging.Site roles)
    (one : first.occurrence.demand.role = 0) (two : last.occurrence.demand.role = 0)
    (firstFits : GeneralNominalSaturationState.SiteHolds first m)
    (lastFits : GeneralNominalSaturationState.SiteHolds last m)
    (a b : Nat) (firstArg : ∀ index, first.occurrence.demand.arguments index = (a,a))
    (lastArg : ∀ index, last.occurrence.demand.arguments index = (b,b))
    (same : GeneralNominalDemandMerging.SameInputs models first last) : Equivalent (m a).1 (m b).1 := by
  have firstArity : first.inputs.length = 1 := by rw [first.arity,one]; rfl
  have lastArity : last.inputs.length = 1 := by rw [last.arity,two]; rfl
  have relation := same.2
  cases firstInputs : first.inputs with
  | nil => simp [firstInputs] at firstArity
  | cons x xs =>
    cases lastInputs : last.inputs with
    | nil => simp [lastInputs] at lastArity
    | cons y ys =>
      rw [firstInputs,lastInputs] at relation
      cases relation with
      | cons related rest =>
        obtain ⟨origin,target,original,other,equal⟩ := related
        have firstIndex : 0 < (roles first.occurrence.demand.role).arity := by rw [one]; decide +kernel
        have lastIndex : 0 < (roles last.occurrence.demand.role).arity := by rw [two]; decide +kernel
        have left := firstFits ⟨0,firstIndex⟩ origin (by rw [firstInputs]; exact congrArg some original)
        have right := lastFits ⟨0,lastIndex⟩ target (by rw [lastInputs]; exact congrArg some other)
        obtain ⟨x,hx⟩ := left.1
        obtain ⟨y,hy⟩ := right.1
        have xf := left.2 x hx
        have yf := right.2 y hy
        rw [firstArg] at xf
        rw [lastArg] at yf
        have related := (equal m valid).2.2 x y hx hy
        exact ⟨subtype_trans xf.1 (subtype_trans related.1 yf.2),
          subtype_trans yf.1 (subtype_trans related.2 xf.2)⟩


theorem raw_sites : finish.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite displayRoot,GeneralNominalSharedEmission.childSite packet displayChild] := by
  change [_] ++ plan.packet.children.map _ = _
  rw [children_exact]; rfl

theorem center_sites : finish.core.sites = [plan.input,centerSite] := by
  change [_] ++ plan.emitted = _
  change [_] ++ [plan.childSite _ _] = _
  rw [first_child]; rfl

private theorem distinct_values : ¬ Equivalent (model 0).1 (model 1).1 := by
  intro equal
  have impossible : 1 = 0 := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp equal
  cases impossible

private theorem raw_no_cross : ¬ GeneralNominalFeedbackSites.SameInputs finish.core.erased.current
    (GeneralNominalDemandMerging.pointSite displayRoot) (GeneralNominalSharedEmission.childSite packet displayChild) := by
  intro same
  have valid := final_model.1.1
  have one : GeneralNominalDemandMerging.pointSite displayRoot ∈ finish.core.erased.current.sites := by rw [raw_sites]; simp
  have two : GeneralNominalSharedEmission.childSite packet displayChild ∈ finish.core.erased.current.sites := by rw [raw_sites]; simp
  exact distinct_values (point_same_values valid _ _ rfl rfl
    (GeneralNominalFeedbackSites.recover_sound _ _ model valid (valid.2.2 _ one))
    (GeneralNominalFeedbackSites.recover_sound _ _ model valid (valid.2.2 _ two))
    0 1 (fun _ => rfl) (fun _ => rfl) same)

theorem raw_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ finish.core.erased.current.sites) (two : last ∈ finish.core.erased.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs finish.core.erased.current first last) :
    GeneralNominalSaturationState.Alias finish.core.erased.current first.occurrence.identity last.occurrence.identity := by
  rw [raw_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · exact False.elim (raw_no_cross same)
  · exact False.elim (raw_no_cross (same_inputs_symm same))
  · exact .refl _

private theorem center_no_cross : ¬ SameInputs (Models finish.core) plan.input centerSite := by
  intro same
  have valid := final_model.1
  exact distinct_values (point_same_values valid _ _ rfl rfl
    (observed_holds _ _ (valid.2.1 _ (by rw [center_sites]; simp)))
    (observed_holds _ _ (valid.2.1 _ (by rw [center_sites]; simp)))
    0 1 (fun _ => rfl) (fun _ => rfl) same)

theorem center_closed (first last : Site roles)
    (one : first ∈ finish.core.sites) (two : last ∈ finish.core.sites)
    (same : SameInputs (Models finish.core) first last) :
    GeneralNominalSaturationState.Alias finish.core.erased.current first.occurrence.identity last.occurrence.identity := by
  rw [center_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · exact False.elim (center_no_cross same)
  · exact False.elim (center_no_cross (same_inputs_symm same))
  · exact .refl _

theorem child_ready : GeneralNominalCenteredAdministrativeLocal.AdministrativeReady finish.core displayChild := by
  refine ⟨⟨centerSite,by rw [center_sites]; simp,rfl⟩,?_,?_⟩
  · intro first present _ last recorded same
    exact raw_closed first last present recorded same
  · intro first present _ last recorded same
    exact center_closed first last present recorded same

theorem parent_ready : GeneralNominalCenteredAdministrativeLocal.AdministrativeReady finish.core displayRoot := by
  refine ⟨⟨plan.input,by rw [center_sites]; simp,rfl⟩,?_,?_⟩
  · intro first present _ last recorded same
    exact raw_closed first last present recorded same
  · intro first present _ last recorded same
    exact center_closed first last present recorded same
end Yulang.GeneralNominalNonleafAdministrative193
