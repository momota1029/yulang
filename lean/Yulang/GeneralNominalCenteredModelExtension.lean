import Yulang.GeneralNominalCenteredAllocation

/-! Conservative interpretation of fresh center names on the general carrier.
The supplied values are model witnesses; they do not change the endpoints or
the candidate inspector. Shared names must receive the same supplied value. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState GeneralNominalCenters
open Core.PresenceGeneration (TyTerm RowTerm)
open CommonNominalFullCarrier

variable {first last : Assignment}

theorem row_eval_same (term : RowTerm Nat)
    (same : ∀ name ∈ rowSources term, first name = last name) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => simp only [RowTerm.eval,same name (by simp [rowSources])]
  | empty => rfl
  | join left right ih₁ ih₂ =>
    simp only [RowTerm.eval,ih₁ (fun n h => same n (List.mem_append_left _ h)),
      ih₂ (fun n h => same n (List.mem_append_right _ h))]

theorem type_eval_same (term : TyTerm Nat)
    (same : ∀ name ∈ typeSources term, first name = last name) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => simp only [TyTerm.eval,same name (by simp [typeSources])]
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | required label child ih | variant label child ih =>
    simp only [TyTerm.eval,ih same]
  | union a b ia ib | inter a b ia ib | pair a b ia ib =>
    simp only [TyTerm.eval,ia (fun n h => same n (List.mem_append_left _ h)),
      ib (fun n h => same n (List.mem_append_right _ h))]
  | record label a b ia ib | recordDefault label a b ia ib =>
    simp only [TyTerm.eval,ia (fun n h => same n (List.mem_append_left _ h)),
      ib (fun n h => same n (List.mem_append_right _ h))]
  | arrow a incoming b outgoing ia ib =>
    have one := ia (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inl (Or.inl h))))
    have two := row_eval_same incoming (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inl (Or.inr h))))
    have three := ib (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inr h)))
    have four := row_eval_same outgoing (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inr h))
    simp only [TyTerm.eval,one,two,three,four]

theorem atom_same (atom : PresenceNormalForm.Atom Nat)
    (same : ∀ name ∈ atomSources atom, first name = last name) :
    atom.Holds model first ↔ atom.Holds model last := by
  cases atom with
  | tyLe a b =>
    simp only [PresenceNormalForm.Atom.Holds,type_eval_same a (fun n h => same n (List.mem_append_left _ h)),
      type_eval_same b (fun n h => same n (List.mem_append_right _ h))]
  | rowLe a b =>
    simp only [PresenceNormalForm.Atom.Holds,row_eval_same a (fun n h => same n (List.mem_append_left _ h)),
      row_eval_same b (fun n h => same n (List.mem_append_right _ h))]

theorem source_models_same (state : GeneralNominalState.State)
    (same : ∀ name ∈ sources state, first name = last name)
    (valid : GeneralNominalState.Models state first) : GeneralNominalState.Models state last := by
  have types (slot : Fin state.base.slots) : first (state.base.source slot) = last (state.base.source slot) :=
    same _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))))
  have rows (slot : Fin state.base.slots) : first (state.base.rowSource slot) = last (state.base.rowSource slot) :=
    same _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))))
  have environment : GeneralNominalCommonBridge.assignment state.base first =
      GeneralNominalCommonBridge.assignment state.base last := by
    funext slot
    simp only [GeneralNominalCommonBridge.assignment,types slot,rows slot]
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [environment] using valid.1.1
  · intro slot term recorded
    simpa only [types slot,environment] using valid.1.2.1 slot term recorded
  · intro pair present
    simpa only [types pair.1,types pair.2] using valid.1.2.2 pair present
  · intro slot descriptor recorded
    obtain ⟨arguments,fit,equal⟩ := valid.2.1 slot descriptor recorded
    refine ⟨arguments,?_,by simpa only [types slot] using equal⟩
    have transfer (parameters values) (fit : FitsAll state.base first parameters values) :
        FitsAll state.base last parameters values := by
      induction fit with
      | nil => exact .nil
      | @cons parameter value parameters values head rest ih =>
        refine .cons ?_ ih
        cases parameter <;> cases value <;> simp only [GeneralNominalState.Fits] at head ⊢
        all_goals first | simpa only [types] using head | simpa only [rows] using head
    exact transfer _ _ fit
  · intro atom present
    exact (atom_same atom (fun n h => same n (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨atom,present,h⟩)))).mp (valid.2.2 atom present)

noncomputable def assign (previous : Assignment) (names : Fin count → Nat)
    (values : Fin count → Ty) : Assignment := by
  classical
  exact fun name => if found : ∃ index, names index = name then
    (values (Classical.choose found),(previous name).2) else previous name

theorem assign_outside (previous : Assignment) (names : Fin count → Nat) (values : Fin count → Ty)
    (absent : ∀ index, names index ≠ name) : assign previous names values name = previous name := by
  classical
  simp only [assign]
  rw [dite_eq_right (by rintro ⟨index,equal⟩; exact absent index equal)]

theorem assign_value (previous : Assignment) (names : Fin count → Nat) (values : Fin count → Ty)
    (coherent : ∀ first last, names first = names last → values first = values last) (index : Fin count) :
    (assign previous names values (names index)).1 = values index := by
  classical
  unfold assign
  rw [dite_eq_left ⟨index,rfl⟩]
  exact coherent _ index (Classical.choose_spec (show ∃ other, names other = names index from ⟨index,rfl⟩))

theorem assign_preserves (previous : Assignment) (names : Fin count → Nat) (values : Fin count → Ty)
    (kept : ∀ index, names index = name → values index = (previous name).1) :
    assign previous names values name = previous name := by
  classical
  unfold assign
  split
  · rename_i found
    rw [kept _ (Classical.choose_spec found)]
  · rfl

theorem site_extension (context : GeneralNominalCandidates.Context) (site : Site roles)
    (previous : Assignment) (valid : GeneralNominalState.Models context.state previous)
    (values : Fin (roles site.occurrence.demand.role).arity → Ty)
    (bounds : ∀ index, GeneralNominalCaptureMerges.Fits previous
      (site.occurrence.demand.arguments index) (values index))
    (linked : GeneralNominalState.Linked context.state site.occurrence.demand)
    (coherent : ∀ first last, site.center first = site.center last → values first = values last)
    (preserved : ∀ index, site.center index ∈ sources context.state →
      values index = (previous (site.center index)).1) :
    ∃ extended, GeneralNominalCenteredSteps.Models (GeneralNominalCenteredSteps.initialAt context site) extended ∧
      (∀ name ∈ sources context.state, extended name = previous name) ∧
      ∀ index, (extended (site.center index)).1 = values index := by
  let extended := assign previous site.center values
  have kept (name : Nat) (member : name ∈ sources context.state) : extended name = previous name := by
    apply assign_preserves
    intro index equal
    simpa only [equal] using preserved index (equal ▸ member)
  refine ⟨extended,(GeneralNominalCenteredSteps.initialAt_models context site extended).mpr
    ⟨source_models_same context.state (fun n h => (kept n h).symm) valid,?_⟩,kept,assign_value _ _ _ coherent⟩
  intro index
  change Subtype (extended (site.occurrence.demand.arguments index).1).1 (extended (site.center index)).1 ∧
    Subtype (extended (site.center index)).1 (extended (site.occurrence.demand.arguments index).2).1
  rw [kept _ (linked.1 index).1,kept _ (linked.1 index).2,assign_value _ _ _ coherent]
  exact bounds index


theorem root_extension {roles : Roles.RoleDecls} {root : GeneralSourceDictionaries.Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (previous : Assignment) (valid : GeneralNominalState.Models context.state previous) :
    ∃ extended, GeneralNominalCenteredSteps.Models (GeneralNominalCenteredSteps.initial context root) extended ∧
      ∀ name ∈ sources context.state, extended name = previous name := by
  let site := rootSite context.state.seed root
  let values := fun index : Fin (roles root.demand.role).arity => (previous (root.demand.arguments index).1).1
  have named (index : Fin (roles root.demand.role).arity)
      (present : site.center index ∈ sources context.state) :
      site.center index = (root.demand.arguments index).1 := by
    by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
    · exact point_center _ _ index point
    · have above := nonpoint_center_fresh context.state.seed root index point
      have below := source.below_seed _ present
      change context.state.seed < site.center index at above
      omega
  have coherent (first last : Fin (roles root.demand.role).arity)
      (same : site.center first = site.center last) : values first = values last := by
    by_cases one : (root.demand.arguments first).1 = (root.demand.arguments first).2
    · have present : site.center first ∈ sources context.state := by
        rw [show site.center first = (root.demand.arguments first).1 from point_center _ _ first one]
        exact (source.linked.1 first).1
      have lastNamed := named last (same ▸ present)
      have firstNamed := named first present
      unfold values
      rw [← firstNamed,← lastNamed,same]
    · by_cases two : (root.demand.arguments last).1 = (root.demand.arguments last).2
      · have present : site.center last ∈ sources context.state := by
          rw [show site.center last = (root.demand.arguments last).1 from point_center _ _ last two]
          exact (source.linked.1 last).1
        have firstNamed := named first (same.symm ▸ present)
        have lastNamed := named last present
        unfold values
        rw [← firstNamed,← lastNamed,same]
      · have keys : (root.identity,0,7,first.val,0) = (root.identity,0,7,last.val,0) := by
          apply (GeneralNominalIdentities.source_identity context.state.seed _ _).mp
          simpa only [site,rootSite,one,two,ite_false,fresh] using same
        have indices : first = last := Fin.ext (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys)
        rw [indices]
  obtain ⟨extended,models,kept,_⟩ := site_extension context site previous valid values
    (fun index => ⟨subtype_refl _,source.intervals previous valid index⟩) source.linked coherent
    (fun index present => by change _ = (previous (site.center index)).1; rw [named index present])
  exact ⟨extended,models,kept⟩

open GeneralNominalRecursiveInspection (Origin Observes)

def originSource : Origin → Nat
  | .source name => name
  | .nominal parent _ _ | .structural parent _ _ => originSource parent

theorem observes_same (seen : Observes first origin value)
    (same : first (originSource origin) = last (originSource origin)) : Observes last origin value := by
  induction seen with
  | source name => rw [show first name = last name from same]; exact .source name
  | nominal parent equal found ih => exact .nominal (ih same) equal found
  | structural parent length equal found ih => exact .structural (ih same) length equal found

theorem nested_extension (state : GeneralNominalState.State)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalState.Models state previous) (values : Fin count → Ty)
    (linked : ∀ index, (arguments index).argument.endpoints.1 ∈ sources state ∧
      (arguments index).argument.endpoints.2 ∈ sources state ∧ originSource (arguments index).origin ∈ sources state)
    (bounds : ∀ index, GeneralNominalCaptureMerges.Fits previous (arguments index).argument.endpoints (values index))
    (readback : ∀ index, (∃ actual, Observes previous (arguments index).origin actual) ∧
      ∀ actual, Observes previous (arguments index).origin actual → Equivalent actual (values index))
    (coherent : ∀ first last, (arguments first).argument.center = (arguments last).argument.center → values first = values last)
    (preserved : ∀ index, (arguments index).argument.center ∈ sources state →
      values index = (previous (arguments index).argument.center).1) :
    ∃ extended, GeneralNominalState.Models state extended ∧
      (∀ name ∈ sources state, extended name = previous name) ∧
      ∀ index, (arguments index).Holds extended := by
  let names := fun index => (arguments index).argument.center
  let extended := assign previous names values
  have kept (name : Nat) (member : name ∈ sources state) : extended name = previous name := by
    apply assign_preserves
    intro index equal
    simpa only [names,equal] using preserved index (show names index ∈ sources state from equal ▸ member)
  have centerValue (index : Fin count) : (extended (arguments index).argument.center).1 = values index :=
    assign_value previous names values coherent index
  refine ⟨extended,source_models_same state (fun n h => (kept n h).symm) valid,kept,?_⟩
  intro index
  constructor
  · change Subtype (extended (arguments index).argument.endpoints.1).1
        (extended (arguments index).argument.center).1 ∧
      Subtype (extended (arguments index).argument.center).1 (extended (arguments index).argument.endpoints.2).1
    rw [kept _ (linked index).1,kept _ (linked index).2.1,centerValue index]
    exact bounds index
  · obtain ⟨actual,seen⟩ := (readback index).1
    refine ⟨⟨actual,observes_same seen (kept _ (linked index).2.2).symm⟩,⟨_,.source _⟩,?_⟩
    intro actual center seen named
    cases named
    rw [centerValue index]
    exact (readback index).2 actual (observes_same seen (kept _ (linked index).2.2))

end Yulang.GeneralNominalCenteredModelExtension
