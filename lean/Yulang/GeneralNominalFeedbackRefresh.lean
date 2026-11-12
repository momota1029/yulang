import Yulang.GeneralNominalFeedbackObstruction

/-! An actual journal-justified normalized refresh for the R packet.
The old nonpoint descriptors are preserved. A newly known child root receives
a point descriptor justified by its installed associated-output equation. -/
namespace Yulang.GeneralNominalFeedbackRefresh

open GeneralNominalFeedbackObstruction
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

private theorem nominal_congr (first last : Ty) (equal : Equivalent first last) :
    Equivalent (nominal 0 [.inl first]) (nominal 0 [.inl last]) := by
  constructor
  · apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro index a b one two
    have zero : index = 0 := by
      have := (List.getElem?_eq_some_iff.mp one).1
      simp only [List.length_cons,List.length_nil] at this
      omega
    subst index
    have left := Option.some.inj one; have right := Option.some.inj two
    subst a; subst b; exact equal
  · apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro index a b one two
    have zero : index = 0 := by
      have := (List.getElem?_eq_some_iff.mp one).1
      simp only [List.length_cons,List.length_nil] at this
      omega
    subst index
    have left := Option.some.inj one; have right := Option.some.inj two
    subst a; subst b; exact ⟨equal.2,equal.1⟩

theorem self_equation (m : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds m) :
    Equivalent (m 2).1 (nominal 0 [.inl (m 2).1]) := by
  have material := valid.2.2
  change GeneralNominalMaterialization.Models source declaration _ _
    (GeneralNominalRecursiveCandidates.generated registry context root declaration declaration_checked [(0,0)]) m at material
  rw [schema_exact] at material
  obtain ⟨args,size,equal⟩ := (material.1 (.source 2,.nominal 0 1) (by simp)).2 _ (.source 2)
  obtain ⟨actual,seen,actualEqual⟩ := packet_self_argument m valid
  cases seen with
  | argument parent observed found =>
    cases parent
    have invariant := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 observed.1)
    cases args with
    | nil => cases size
    | cons first tail =>
      have tailNil : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
      subst tail
      have compared := invariant.2.2 0 first (.inl actual) rfl found
      cases first with
      | inr => cases compared
      | inl original =>
        have fixed : Equivalent original (m 2).1 :=
          ⟨subtype_trans compared.1 actualEqual.1,subtype_trans actualEqual.2 compared.2⟩
        have lifted := nominal_congr original (m 2).1 fixed
        exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩

abbrev descriptor : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (2,2)],rfl⟩

noncomputable def refreshedState : GeneralNominalState.State :=
  { packet.privateContext.state with
    nominals := fun slot => if slot.val = 2 then some descriptor else packet.privateContext.state.nominals slot
    catalogue := by
      intro slot d recorded
      split at recorded
      · have same := Option.some.inj recorded; subst d; rfl
      · exact packet.privateContext.state.catalogue slot d recorded
    bodies_opaque := by intro _ _ _; rfl }

noncomputable def refreshedContext : GeneralNominalCandidates.Context := ⟨refreshedState,context.interpretation⟩
noncomputable def refreshed := regenerate installed refreshedContext

noncomputable def refines : GeneralNominalRefinements.Refines installed.context.state refreshedState := by
  have retained : ∀ slot d, packet.privateContext.state.nominals slot = some d → refreshedState.nominals slot = some d := by
    intro slot d recorded
    have different : slot.val ≠ 2 := by
      intro two
      have same : slot = (2 : Fin 4) := Fin.ext two
      subst slot
      cases recorded
    simpa only [refreshedState,ite_eq_right different] using recorded
  refine { GeneralNominalRefinements.refl packet.privateContext.state with
    nominals := ?_
    known := ?_ }
  · intro slot d recorded
    exact retained slot _ ((GeneralNominalRefinements.refl packet.privateContext.state).nominals slot d recorded)
  · intro source known
    obtain ⟨slot,equal,head | nominal⟩ := known
    · exact ⟨slot,equal,Or.inl head⟩
    · obtain ⟨d,recorded⟩ := nominal
      exact ⟨slot,equal,Or.inr ⟨d,retained slot d recorded⟩⟩

noncomputable def refresh_certificate : GeneralNominalCycleSteps.Refresh installed refreshedContext where
  refines := refines
  interpretation := rfl
  exact := by
    intro m valid
    refine ⟨valid.1.1,?_,valid.1.2.2⟩
    intro slot d recorded
    change Fin 4 at slot
    change GeneralNominalState.Descriptor 4 at d
    change (if slot.val = 2 then some descriptor else source.nominals slot) = some d at recorded
    by_cases two : slot.val = 2
    · rw [ite_eq_left two] at recorded
      have same := Option.some.inj recorded; subst d
      have index : slot = (2 : Fin 4) := Fin.ext two
      subst slot
      refine ⟨[.inl (m 2).1],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,?_⟩
      exact self_equation m (valid.2.1 packet (by simp [installed,GeneralNominalFeedbackSites.install]))
    · rw [ite_eq_right two] at recorded
      exact valid.1.2.1 slot d recorded
  support := fun _ member => member

theorem child_known : GeneralNominalState.Known refreshedState 2 :=
  ⟨⟨2,by decide +kernel⟩,rfl,Or.inr ⟨descriptor,rfl⟩⟩

theorem refresh_step : GeneralNominalFeedbackSteps.Step registry root installed refreshed := by
  refine ⟨child,GeneralNominalFeedbackSteps.installed_children initialState packet child (by rw [children_exact]; simp),?_⟩
  apply GeneralNominalFeedbackSteps.At.refresh child refreshedContext refresh_certificate 2
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨⟨2,by decide +kernel⟩,rfl⟩
  · exact old_child_pending.choose_spec
  · exact child_known

theorem refresh_models (m : GeneralNominalCommonBridge.Assignment) : Models refreshed m ↔ Models installed m :=
  GeneralNominalCycleSteps.refresh_models refresh_certificate m

theorem child_linked : GeneralNominalState.Linked refreshedState child.demand := by
  constructor
  · intro index
    have supported (slot : Fin 4) : slot.val ∈ GeneralNominalState.sources refreshedState :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
    exact ⟨supported 2,supported 3⟩
  · intro o member
    have same := List.mem_singleton.mp member; subst o
    have key : GeneralNominalAllocation.origin root.identity 2 5 21 0 ∈ GeneralNominalAllocation.keys registry root.identity := by
      simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys]
    exact (GeneralNominalSourceFormation.installation_reserves packet _ key).1

theorem child_raw_K2 : GeneralNominalCycleK2.RootK2 refreshedState child.demand := by
  refine ⟨child_linked,?_,⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩,rfl,Or.inl ?_⟩
  · rintro ⟨index,unknown⟩
    exact unknown child_known
  · exact ⟨⟨2,by decide +kernel⟩,Or.inr ⟨descriptor,rfl,0,rfl⟩,.nil _⟩

theorem child_rejected : GeneralNominalFeedbackK2.Local registry refreshed child .rejected :=
  GeneralNominalFeedbackK2.root_rejected registry refreshed child (Or.inl child_raw_K2)

theorem child_never_expanded (next : Packet roles) (focus : next.site.occurrence = child) :
    ¬ GeneralNominalFeedbackSteps.Installable registry refreshed next := by
  apply GeneralNominalFeedbackSteps.rootK2_never_installed
  rw [focus]
  exact Or.inl child_raw_K2

end Yulang.GeneralNominalFeedbackRefresh
