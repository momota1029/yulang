import Yulang.GeneralDictionaryOutputMergeInstallClosure

/-! Concrete enqueue and merge closure of the unchanged generated site graph.
Cross-kind root/child inputs are separated by the actual common model. -/
namespace Yulang.GeneralDictionaryOutputMergeSiteClosure
open GeneralDictionaryOutputMergeSuccess GeneralDictionaryOutputMergeRefresh
open GeneralDictionaryOutputMergeInstallClosure
open GeneralNominalExamples (displayRoot model)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState CommonNominalFullCarrier
noncomputable abbrev rootSite := GeneralNominalDemandMerging.pointSite displayRoot

theorem sites_exact : refreshed.current.sites = [rootSite,site 10,site 11] :=
  GeneralDictionaryOutputMergeSuccess.sites_exact

theorem generated_present (focus : GeneralSourceDictionaries.Occurrence roles)
    (given : Generated refreshed.current displayRoot focus) :
    ∃ s ∈ refreshed.current.sites, s.occurrence = focus := by
  rcases generated_cases focus given with same | same | same
  · exact ⟨rootSite,by rw [sites_exact]; exact List.mem_cons_self ..,same.symm⟩
  · exact ⟨site 10,by rw [sites_exact]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..),same.symm⟩
  · exact ⟨site 11,by rw [sites_exact]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),same.symm⟩

theorem sameInputs_no_cross (n : Nat) (which : n = 10 ∨ n = 11) :
    ¬ GeneralNominalFeedbackSites.SameInputs refreshed.current rootSite (site n) := by
  intro same
  have member : site n ∈ refreshed.current.sites := by
    rw [sites_exact]
    rcases which with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have left := GeneralNominalFeedbackSites.recover_sound refreshed.current rootSite model inhabited (point_holds displayRoot model)
  have right := GeneralNominalFeedbackSites.recover_sound refreshed.current (site n) model inhabited
    (inhabited.2.2 (site n) member)
  have relation := same.2
  change GeneralNominalDemandMerging.All₂ _
    [GeneralNominalFeedbackSites.recoverOrigin refreshed.current rootSite ⟨0,by change 0 < 1; decide +kernel⟩]
    [GeneralNominalFeedbackSites.recoverOrigin refreshed.current (site n) ⟨0,by change 0 < 1; decide +kernel⟩] at relation
  cases relation with
  | cons related _ =>
    obtain ⟨a,b,one,two,equal⟩ := related
    have firstFits := left ⟨0,by change 0 < 1; decide +kernel⟩ a (by
      change some (GeneralNominalFeedbackSites.recoverOrigin refreshed.current rootSite _) = some (some a)
      exact congrArg some one)
    have lastFits := right ⟨0,by change 0 < 1; decide +kernel⟩ b (by
      change some (GeneralNominalFeedbackSites.recoverOrigin refreshed.current (site n) _) = some (some b)
      exact congrArg some two)
    obtain ⟨x,hx⟩ := firstFits.1
    obtain ⟨y,hy⟩ := lastFits.1
    have xfit := firstFits.2 x hx
    have yfit := lastFits.2 y hy
    have sameValue := (equal model inhabited).2.2 x y hx hy
    have impossible : Equivalent (GeneralNominalOutputGrowth.tower 1) (GeneralNominalOutputGrowth.tower 0) :=
      ⟨subtype_trans xfit.1 (subtype_trans sameValue.1 yfit.2),
        subtype_trans yfit.1 (subtype_trans sameValue.2 xfit.2)⟩
    have contradiction := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp impossible
    cases contradiction

private theorem sameInputs_symm {first last : GeneralNominalDemandMerging.Site roles}
    (same : GeneralNominalFeedbackSites.SameInputs refreshed.current first last) :
    GeneralNominalFeedbackSites.SameInputs refreshed.current last first := by
  refine ⟨same.1.symm,?_⟩
  have relation := same.2
  generalize (GeneralNominalFeedbackSites.recover refreshed.current first).inputs = xs at relation ⊢
  generalize (GeneralNominalFeedbackSites.recover refreshed.current last).inputs = ys at relation ⊢
  induction relation with
  | nil => exact .nil
  | cons head tail ih =>
    refine .cons ?_ ih
    obtain ⟨a,b,one,two,equal⟩ := head
    refine ⟨b,a,two,one,?_⟩
    intro m valid
    have original := equal m valid
    exact ⟨original.2.1,original.1,fun x y hx hy => ⟨(original.2.2 y x hy hx).2,(original.2.2 y x hy hx).1⟩⟩

theorem child_alias : Alias refreshed.current (site 10).occurrence.identity (site 11).occurrence.identity :=
  .edge (List.mem_singleton_self _)

theorem merges_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ refreshed.current.sites) (two : last ∈ refreshed.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs refreshed.current first last) :
    Alias refreshed.current first.occurrence.identity last.occurrence.identity := by
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
  · exact .refl _
  · exact False.elim (sameInputs_no_cross 10 (Or.inl rfl) same)
  · exact False.elim (sameInputs_no_cross 11 (Or.inr rfl) same)
  · exact False.elim (sameInputs_no_cross 10 (Or.inl rfl) (sameInputs_symm same))
  · exact .refl _
  · exact child_alias
  · exact False.elim (sameInputs_no_cross 11 (Or.inr rfl) (sameInputs_symm same))
  · exact .symm child_alias
  · exact .refl _
end Yulang.GeneralDictionaryOutputMergeSiteClosure
