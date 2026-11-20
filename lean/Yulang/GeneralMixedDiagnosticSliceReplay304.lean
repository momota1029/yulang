import Yulang.GeneralMixedDiagnosticCompiler304
import Yulang.GeneralDeferredLadderReinstall304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticSliceReplay304
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install installCore)
open GeneralNominalVersionedMergedConflict232 (HistoryModels ClassEquations)
open GeneralNominalVersionedEffects231 (ClassEffects class_effects_iff)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs mem_requests_iff)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeferredLadderResnapshot304 (HeadView resnapshot new_effect_iff)
open GeneralMixedDiagnosticSlice304 (Semantics)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem alias_to {x y : GeneralNominalSaturationState.State roles}
    (same : x.aliases = y.aliases) (path : Alias x i j) : Alias y i j := by
  induction path with
  | refl => exact .refl _
  | edge member => exact .edge (same ▸ member)
  | symm _ ih => exact .symm ih
  | trans _ _ first last => exact .trans first last

theorem install_alias (s : State roles) (p : GeneralNominalCenters.Plan roles) (i j : Nat) :
    Alias (installCore s.core p).erased.current i j ↔ Alias s.core.erased.current i j :=
  ⟨alias_to (x := (installCore s.core p).erased.current) (y := s.core.erased.current) rfl,
    alias_to (x := s.core.erased.current) (y := (installCore s.core p).erased.current) rfl⟩

def KeepsRequests (s : State roles) (p : GeneralNominalCenters.Plan roles) : Prop :=
  ∀ (root : Occurrence roles) (o : GeneralSourceState.Output),
    o ∈ requests (installCore s.core p) root ↔ o ∈ requests s.core root

theorem keeps_of_outputless_rows (s : State roles) (p : GeneralNominalCenters.Plan roles)
    (empty : ∀ row ∈ GeneralNominalVersionedChildren232.rawSites p, row.occurrence.demand.outputs = []) :
    KeepsRequests s p := by
  intro root output
  constructor
  · intro got
    obtain ⟨row,listed,alias,asked⟩ := mem_requests_iff.mp got
    change row ∈ s.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites p at listed
    rcases List.mem_append.mp listed with old|new
    · exact mem_requests_iff.mpr ⟨row,old,(install_alias s p _ _).mp alias,asked⟩
    · rw [empty row new] at asked
      cases asked
  · exact GeneralNominalVersionedInstall232.requests_included s.core p output

theorem equal_outputs_iff {first last : GeneralNominalCenteredSteps.State roles} (root : Occurrence roles)
    (same : ∀ output, output ∈ requests first root ↔ output ∈ requests last root) (m : Assignment) :
    EqualOutputs first root m ↔ EqualOutputs last root m := by
  unfold EqualOutputs
  simp only [same]

theorem class_iff {first last : GeneralNominalCenteredSteps.State roles} (root : Occurrence roles)
    (same : ∀ output, output ∈ requests first root ↔ output ∈ requests last root)
    (p : GeneralNominalCenters.Plan roles) (m : Assignment) :
    ClassEffects first root p m ↔ ClassEffects last root p m := by
  unfold ClassEffects
  simp only [same,equal_outputs_iff root same m]

theorem history_after (s : State roles) (e : Effect roles) (m : Assignment) :
    HistoryModels (install s e) m ↔ HistoryModels s m ∧
      GeneralNominalVersionedPlans231.Holds e.plan m ∧ e.Holds m := by
  constructor
  · intro new
    exact ⟨⟨new.1,fun old listed => new.2.1 old (List.mem_cons_of_mem _ listed),
      fun old listed => new.2.2 old (List.mem_cons_of_mem _ listed)⟩,
      new.2.1 e.plan List.mem_cons_self,new.2.2 e List.mem_cons_self⟩
  · rintro ⟨old,hp,he⟩
    refine ⟨old.1,?_,?_⟩
    · intro q listed
      rcases List.mem_cons.mp listed with rfl|tail
      · exact hp
      · exact old.2.1 q tail
    · intro prior listed
      rcases List.mem_cons.mp listed with rfl|tail
      · exact he
      · exact old.2.2 prior tail

theorem class_after (s : State roles) (e : Effect roles) (stable : KeepsRequests s e.plan)
    (root : Occurrence roles) (m : Assignment) :
    ClassEquations (install s e) root m ↔ ClassEquations s root m ∧
      (Alias s.core.erased.current root.identity e.plan.packet.site.occurrence.identity →
        e.Live (install s e).core m) := by
  have equal := equal_outputs_iff root (stable root) m
  have clauses (root : Occurrence roles) (p : GeneralNominalCenters.Plan roles) :=
    class_iff root (stable root) p m
  have oldClauses (root : Occurrence roles) (p : GeneralNominalCenters.Plan roles) :
      GeneralNominalCenteredHeadMatEffects.ClassEffects (install s e).core root p m ↔
        GeneralNominalCenteredHeadMatEffects.ClassEffects s.core root p m :=
    (class_effects_iff ..).symm.trans ((clauses root p).trans (class_effects_iff ..))
  constructor
  · intro new
    refine ⟨⟨⟨equal.mp new.1.1,?_⟩,?_⟩,fun oldAlias => new.2 e List.mem_cons_self ((install_alias s e.plan _ _).mpr oldAlias)⟩
    · intro old listed alias
      exact (oldClauses _ _).mp (new.1.2 old listed ((install_alias s e.plan _ _).mpr alias))
    · intro old listed alias
      exact (clauses _ _).mp (new.2 old (List.mem_cons_of_mem _ listed) ((install_alias s e.plan _ _).mpr alias))
  · rintro ⟨old,latest⟩
    refine ⟨⟨equal.mpr old.1.1,?_⟩,?_⟩
    · intro earlier listed alias
      exact (oldClauses _ _).mpr (old.1.2 earlier listed ((install_alias s e.plan _ _).mp alias))
    · intro prior listed alias
      rcases List.mem_cons.mp listed with rfl|tail
      · exact latest ((install_alias s prior.plan _ _).mp alias)
      · exact (clauses _ _).mpr (old.2 prior tail ((install_alias s e.plan _ _).mp alias))

theorem stays_on_other_side (head : HeadView a b) (p : GeneralNominalCenters.Plan roles)
    (stable : KeepsRequests a p) : KeepsRequests b p := by
  intro root output
  exact (GeneralDeferredLadderReinstall304.future_requests_iff head.raw p root output).symm.trans
    ((stable root output).trans (GeneralDeferredLadderOperationalView304.requests_iff head.raw root output))

theorem semantics_after (head : HeadView a b) (slices : Semantics a b) (e : Effect roles)
    (atA : e.snapshot = a.core) (stable : KeepsRequests a e.plan) :
    Semantics (install a e) (install b (resnapshot head e atA)) := by
  let f := resnapshot head e atA
  constructor
  · intro m
    exact (history_after a e m).trans
      ((and_congr (slices.history m) (and_congr Iff.rfl (new_effect_iff head e atA m).symm)).trans
        (history_after b f m).symm)
  · intro root m valid
    have old := ((history_after a e m).mp valid).1
    exact (class_after a e stable root m).trans
      ((and_congr (slices.class_on_history root m old)
        (imp_congr
          ⟨GeneralDeferredLadderOperationalView304.alias_forward head.raw,
           GeneralDeferredLadderOperationalView304.alias_forward head.raw.symm⟩
          (class_iff _ (GeneralDeferredLadderReinstall304.future_requests_iff head.raw e.plan _) _ m))).trans
        (class_after b f (stays_on_other_side head e.plan stable) root m).symm)

end Yulang.GeneralMixedDiagnosticSliceReplay304
