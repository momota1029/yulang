import Yulang.GeneralNominalCanonicalOutputForkClassification
import Yulang.GeneralNominalReobservationExecutor

/-! A concrete limit of observation-only completion. The only strict point
revision of this reachable wide snapshot is its precise snapshot. That snapshot
must still install a non-entailed associated-output equation before it is stable. -/
namespace Yulang.GeneralNominalCanonicalCompletionObstruction

open GeneralNominalCanonicalOutputFork GeneralNominalCanonicalOutputForkClassification
open GeneralNominalReobservationSteps GeneralNominalSaturationState
open GeneralNominalRefreshFork (descriptor list)
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)

private theorem int_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem inner_not_outer : ¬ Subtype (list (.base .int)) (list (list (.base .int))) := by
  intro below
  have same := (nominal_regular_invariant_exact _ _ _ _).mp below
  exact int_not_nominal 0 _ (same.2.2 0 _ _ rfl rfl).1

private theorem inner_slot (slot : Fin 5)
    (equal : Equivalent (list (.base .int)) (GeneralNominalRefreshFork.model slot.val).1) : slot = 2 := by
  have alternatives : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (inner_not_outer equal.1)
  · exact False.elim (inner_not_outer equal.1)
  · rfl
  · exact False.elim (int_not_nominal 0 _ equal.2)
  · exact False.elim (GeneralNominalTopObservation.top_not_nominal 0 _ equal.2)

private theorem int_slot (slot : Fin 5)
    (equal : Equivalent (.base .int) (GeneralNominalRefreshFork.model slot.val).1) : slot = 3 := by
  have alternatives : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · exact False.elim (int_not_nominal 0 _ equal.1)
  · rfl
  · exact False.elim (GeneralNominalTopObservation.top_not_scalar .int equal.2)

private theorem descriptor_point (slot : Fin 5) (payload : Ty)
    (atSlot : (GeneralNominalRefreshFork.model slot.val).1 = list payload)
    (d : GeneralNominalState.Descriptor 5)
    (catalogue : constructors d.constructor = some d.declaration)
    (point : PointDescriptor d)
    (denotes : GeneralNominalState.Denotes GeneralNominalRefreshFork.base GeneralNominalRefreshFork.model slot d) :
    ∃ index : Fin 5, d = descriptor (index,index) ∧
      Equivalent payload (GeneralNominalRefreshFork.model index.val).1 := by
  obtain ⟨values,fits,equal⟩ := denotes
  change Equivalent (GeneralNominalRefreshFork.model slot.val).1 (nominal d.declaration.name values) at equal
  rw [atSlot] at equal
  have invariant := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
  have name : d.declaration.name = d.constructor :=
    (congrArg GeneralDeclarationPatterns.Constructor.name (Option.some.inj catalogue)).symm
  have key : d.constructor = 0 := name.symm.trans invariant.1.symm
  rcases d with ⟨constructor,decl,parameters,layout⟩
  dsimp only at key
  subst constructor
  have declEq := Option.some.inj catalogue
  change (⟨[.type],0⟩ : GeneralDeclarationPatterns.Constructor) = decl at declEq
  subst decl
  cases parameters with
  | nil => cases layout
  | cons parameter rest =>
    have length := congrArg List.length layout
    simp only [List.length_map,List.length_cons,List.length_nil,Nat.add_right_cancel_iff] at length
    have empty : rest = [] := List.length_eq_zero_iff.mp length
    subst rest
    cases parameter with
    | row bounds => cases layout
    | type bounds =>
      obtain ⟨lower,upper⟩ := bounds
      have endpoints : lower = upper := point (.type (lower,upper)) (List.mem_singleton_self _)
      subst upper
      refine ⟨lower,rfl,?_⟩
      change GeneralNominalState.FitsAll GeneralNominalRefreshFork.base GeneralNominalRefreshFork.model
        [.type (lower,lower)] values at fits
      obtain ⟨value,found,head⟩ := GeneralNominalIntervalLaws.fitsAll_at _ _ _ _ fits 0 (.type (lower,lower)) rfl
      cases value with
      | inr value => cases head
      | inl value =>
        have same := invariant.2.2 0 (.inl payload) (.inl value) rfl found
        exact ⟨subtype_trans same.1 head.2,subtype_trans head.1 same.2⟩

theorem point_descriptor_forced (slot : Fin 5) (d : GeneralNominalState.Descriptor 5)
    (small : slot.val < 3) (catalogue : constructors d.constructor = some d.declaration)
    (point : PointDescriptor d)
    (denotes : GeneralNominalState.Denotes GeneralNominalRefreshFork.base GeneralNominalRefreshFork.model slot d) :
    d = descriptor (if slot = 2 then (3,3) else (2,2)) := by
  have alternatives : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
  rcases alternatives with rfl | rfl | rfl
  · obtain ⟨index,same,equal⟩ := descriptor_point 0 (list (.base .int)) rfl d catalogue point denotes
    rw [inner_slot index equal] at same
    exact same
  · obtain ⟨index,same,equal⟩ := descriptor_point 1 (list (.base .int)) rfl d catalogue point denotes
    rw [inner_slot index equal] at same
    exact same
  · obtain ⟨index,same,equal⟩ := descriptor_point 2 (.base .int) rfl d catalogue point denotes
    rw [int_slot index equal] at same
    exact same

private theorem old_point_nonzero (slot : Fin 5) (nonzero : slot ≠ 0)
    (d : GeneralNominalState.Descriptor 5) (recorded : (state (some true)).nominals slot = some d) :
    PointAt (state (some true)) slot := by
  refine ⟨d,recorded,?_⟩
  apply GeneralNominalReobservationExamples.point_closed slot d
  simpa only [state,GeneralNominalRefreshFork.state,ite_eq_right nonzero] using recorded

private theorem revision_old_present (change : Revision (after true)) (slot : Fin 5)
    (d : GeneralNominalState.Descriptor 5) (recorded : change.entries slot = some d) :
    ∃ old, (state (some true)).nominals slot = some old := by
  cases found : (state (some true)).nominals slot with
  | none =>
    have missing := (change.domain slot).mpr found
    rw [missing] at recorded
    cases recorded
  | some old => exact ⟨old,rfl⟩

theorem revision_pointClosed (change : Revision (after true)) (improved : Improves change) :
    PointClosed change.snapshot := by
  have zeroPoint : PointAt change.snapshot (0 : Fin 5) := by
    obtain ⟨slot,absent,present⟩ := improved.2
    by_cases zero : slot = (0 : Fin 5)
    · exact zero ▸ present
    · obtain ⟨d,recorded,_⟩ := present
      obtain ⟨old,found⟩ := revision_old_present change slot d recorded
      exact False.elim (absent (old_point_nonzero slot zero old found))
  intro slot d recorded
  by_cases zero : slot = (0 : Fin 5)
  · subst slot
    obtain ⟨other,found,point⟩ := zeroPoint
    have same := Option.some.inj (found.symm.trans recorded)
    exact same ▸ point
  · obtain ⟨old,found⟩ := revision_old_present change slot d recorded
    obtain ⟨other,seen,point⟩ := improved.1 slot (old_point_nonzero slot zero old found)
    have same := Option.some.inj (seen.symm.trans recorded)
    exact same ▸ point

theorem revision_entries_forced (change : Revision (after true)) (certified : Certified change)
    (improved : Improves change) : change.entries = (state (some false)).nominals := by
  have valid : Models change.result GeneralNominalRefreshFork.model :=
    (certified.exact _).mpr ((GeneralNominalSaturationState.initial_models ..).mpr
      (GeneralNominalRefreshFork.after_models true).1)
  funext slot
  change Fin 5 at slot
  cases found : change.entries slot with
  | none =>
    have old := (change.domain slot).mp found
    exact ((revision.domain slot).mpr old).symm
  | some d =>
    obtain ⟨old,recorded⟩ := revision_old_present change slot d found
    have small : slot.val < 3 := by
      by_cases small : slot.val < 3
      · exact small
      · have alternatives : slot = 3 ∨ slot = 4 := by omega
        rcases alternatives with rfl | rfl <;> cases recorded
    have forced := point_descriptor_forced slot d small (change.catalogue slot d found)
      (revision_pointClosed change improved slot d found) (valid.1.2.1 slot d found)
    rw [forced]
    have alternatives : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
    rcases alternatives with rfl | rfl | rfl <;> rfl

theorem revision_result_forced (change : Revision (after true)) (certified : Certified change)
    (improved : Improves change) : change.result = after false := by
  have entries := revision_entries_forced change certified improved
  rcases change with ⟨values,catalogue,opaqueHeads,domain⟩
  change values = (state (some false)).nominals at entries
  subst values
  rfl

theorem step_from_wide (next : State roles)
    (update : Step registry root (after true) next) : next = after false := by
  obtain ⟨focus,generated,action⟩ := update
  cases action with
  | ordinary action => exact False.elim (wide_stable focus generated _ action)
  | reobserve change certified improved => exact revision_result_forced change certified improved

theorem point_packet_excludes_bad (p : Packet roles) (same : p.site.occurrence = root)
    (enabled : GeneralNominalFeedbackSteps.Installable registry (after false) p) : ¬ p.Holds (model .str) := by
  rcases p with ⟨reg,ctx,site,d,checked,bounds⟩
  have regEq := enabled.1.1
  have ctxEq := enabled.1.2.1
  have visible := enabled.1.2.2.2.1
  have found := enabled.1.2.2.2.2.2.1
  dsimp only at regEq ctxEq visible found same
  subst reg
  change ctx = context (some false) at ctxEq
  subst ctx
  have declarationEq := List.mem_singleton.mp visible
  subst d
  rw [same] at found
  have boundsEq := Option.some.inj ((located _).symm.trans found)
  subst bounds
  intro holds
  change GeneralNominalRecursiveCandidates.BranchModels registry (context (some false))
    site.occurrence declaration checked [(0,0)] (model .str) at holds
  rw [same] at holds
  exact GeneralDictionaryRecursiveObstruction.bad_output_equation (branch_output checked (model .str) holds)

theorem step_from_point_excludes_bad (next : State roles)
    (update : Step registry root (after false) next) : ¬ Models next (model .str) := by
  obtain ⟨focus,generated,action⟩ := update
  have same := generated_only_root false focus generated
  cases action with
  | reobserve change _ improved =>
    exact False.elim (pointClosed_no_revision GeneralNominalReobservationExamples.point_closed change improved)
  | ordinary action =>
    cases action with
    | enqueue focus _ absent => exact False.elim (absent _ (List.mem_singleton_self _) same.symm)
    | install p enabled _ =>
      intro valid
      exact point_packet_excludes_bad p same enabled
        (valid.2.1 p (List.mem_cons_self))
    | merge first last one two _ novel =>
      have a := List.mem_singleton.mp one
      have b := List.mem_singleton.mp two
      subst first; subst last
      exact False.elim (novel (.refl _))
    | refresh _ next certified source member unknown known =>
      exact False.elim (no_refresh false next certified source member unknown known)
    | equate _ first last _ _ equal novel =>
      exact False.elim (novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw
        (context (some false)) root first last equal))

theorem trace_trichotomy (final : State roles)
    (path : B4Target.Steps (Step registry root) (after true) final) :
    final = after true ∨ final = after false ∨ ¬ Models final (model .str) := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ update ih =>
    rcases ih with beforeWide | beforePoint | lost
    · subst beforeWide
      exact Or.inr (Or.inl (step_from_wide _ update))
    · subst beforePoint
      exact Or.inr (Or.inr (step_from_point_excludes_bad _ update))
    · exact Or.inr (Or.inr (fun valid => lost (stepModels update _ valid)))

theorem stable_trace_loses_bad (final : State roles)
    (path : B4Target.Steps (Step registry root) (after true) final)
    (stable : Stable registry final root) : ¬ Models final (model .str) := by
  rcases trace_trichotomy final path with wide | point | lost
  · subst final
    exact False.elim (stable_halted stable _ repair_step)
  · subst final
    exact False.elim (point_not_stable stable)
  · exact lost

theorem no_same_models_stable_extension : ¬ ∃ final : State roles,
    B4Target.Steps (Step registry root) (after true) final ∧ Stable registry final root ∧
      ∀ assignment, Models final assignment ↔ Models (after true) assignment := by
  rintro ⟨final,path,stable,same⟩
  exact stable_trace_loses_bad final path stable ((same _).mpr (after_models true .str))

theorem installed_models_exact (assignment : GeneralNominalCommonBridge.Assignment) :
    Models installed assignment ↔ Models (after true) assignment ∧
      Equivalent (assignment 5).1 (.base .int) := by
  rw [GeneralNominalFeedbackSites.install_models _ packet _ rfl assignment]
  constructor
  · rintro ⟨valid,branch⟩
    exact ⟨(same_models true assignment).mpr ((same_models false assignment).mp valid),
      branch_output declaration_checked assignment branch⟩
  · rintro ⟨valid,output⟩
    have point := (same_models false assignment).mpr ((same_models true assignment).mp valid)
    exact ⟨point,point_branch declaration_checked assignment point.1 output⟩

theorem canonical_views_equal : GeneralCanonicalObservations.canonical (after true) =
    GeneralCanonicalObservations.canonical (after false) :=
  GeneralCanonicalObservations.equal_of_same_information ⟨fun _ member => member,rfl⟩
    ⟨fun _ member => member,rfl⟩
    (fun assignment => (same_models true assignment).trans (same_models false assignment).symm)

theorem boundary_completion_obstruction :
    (GeneralNominalReobservationBoundary.boundary roles).Checked registry ∧
    B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles) registry root (after true) ∧
    (∀ next, ¬ GeneralNominalFeedbackSteps.Step registry root (after true) next) ∧
    ¬ ∃ final,
      B4Target.Steps ((GeneralNominalReobservationBoundary.boundary roles).Step registry root) (after true) final ∧
      (GeneralNominalReobservationBoundary.boundary roles).Stable registry final root ∧
      ∀ assignment, (GeneralNominalReobservationBoundary.boundary roles).Models final assignment ↔
        (GeneralNominalReobservationBoundary.boundary roles).Models (after true) assignment :=
  ⟨⟨rfl,registry_checked⟩,
    GeneralNominalReobservationBoundary.old_reachable registry (after true) root (after_reachable true),
    GeneralNominalFeedbackSteps.stable_halted wide_stable,no_same_models_stable_extension⟩

/-- The universal same-model completion request fails in the exact checked,
old-reachable, old-halted domain, for the full extended transition relation. -/
theorem not_old_halted_same_models_completion : ¬
    (∀ (r : GeneralDeclarations.Registry), (GeneralDictionaryReachableBoundary.boundary roles).Checked r →
      ∀ (start : State roles) (d : GeneralSourceDictionaries.Occurrence roles),
        B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) r d start →
        (∀ next, ¬ GeneralNominalFeedbackSteps.Step r d start next) →
        ∃ final, B4Target.Steps (Step r d) start final ∧ Stable r final d ∧
          ∀ assignment, Models final assignment ↔ Models start assignment) := by
  intro completion
  exact no_same_models_stable_extension (completion registry ⟨rfl,registry_checked⟩ (after true) root
    (after_reachable true) (GeneralNominalFeedbackSteps.stable_halted wide_stable))

/-- The model-decreasing restatement follows from the existing executor with
only its Progress field. This supplies no proof of Progress or maximal inspection. -/
theorem model_decreasing_completion_of_progress (roleDecls : Roles.RoleDecls)
    (progress : GeneralNominalReobservationExecutor.Progress roleDecls)
    (r : GeneralDeclarations.Registry) (checked : (GeneralNominalReobservationBoundary.boundary roleDecls).Checked r)
    (start : State roleDecls) (d : GeneralSourceDictionaries.Occurrence roleDecls)
    (reached : B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roleDecls) r d start) :
    ∃ final, B4Target.Steps (Step r d) start final ∧ Stable r final d ∧
      ∀ assignment, Models final assignment → Models start assignment :=
  ⟨((GeneralNominalReobservationExecutor.executor roleDecls progress).run r start d).1,
    GeneralNominalReobservationExecutor.execution roleDecls progress r checked start d reached,
    (GeneralNominalReobservationExecutor.final_stable roleDecls progress r checked start d reached).1,
    GeneralNominalReobservationExecutor.final_models roleDecls progress r checked start d reached⟩

end Yulang.GeneralNominalCanonicalCompletionObstruction
