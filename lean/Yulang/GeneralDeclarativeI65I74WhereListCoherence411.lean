import Yulang.GeneralDeclarativeI65I74WhereListFidelity411

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open CommonRoleOutermostResolver (Result Tree Summarizes)
open List410 (listPoint410)

theorem any_where_event_retains_its_exact_child411 {s q} {e : Event s q}
    (source : WhereListRead e) :
    e.frame.input source.test.binder = point source.test.payload ∧
      e.kids = [source.test.child] := by
  let a := source.test
  have capture : e.frame.input a.binder = point a.payload := by
    rw [source.input,source.head]
    change a.capture a.binder = _
    simp [WhereListHead.capture]
  have whereDemand : (e.frame.whereFor a.clause).demand = a.childDemand := by
    have literal := literal_variable_where_uses_actual_names403 e.frame
      (binders := [a.binder]) (by simpa using a.whereArgs) a.whereOutputs
    have binderSource : a.binder ∈ e.frame.decl.inputNames := by
      simp [Declaration.inputNames,a.named,GeneralDeclarationPatterns.normalizeArgs,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables]
    have exactName : e.frame.names.input a.binder = e.frame.input a.binder :=
      GeneralDeclarativeProducedNames325.exact_input a.checked binderSource
    simpa [WhereListHead.childDemand,exactName,capture] using literal
  refine ⟨capture,?_⟩
  change frameWhereKids400 e.frame = _
  unfold frameWhereKids400 children AuthoredBodyFrame393.clauses
  simp [a.exactWhere]
  change (⟨q.occurrence ++ [0],(e.frame.whereFor a.clause).demand⟩ : I72.Request) = a.child
  rw [whereDemand]
  rfl

/-- The native syntax function of any fitting model assigns a single exact
source endpoint at the original point. It cannot turn different payload
names into the same literal child merely because their model values agree. -/
theorem fitting_snapshot_has_exactly_same_where_demand411 {s q d d'}
    (a : WhereListHead s q d) (b : WhereListHead s q d')
    (m : I72.Model) (fit : Fits s m) : a.child = b.child := by
  have args := (List.cons.inj (a.asked.symm.trans b.asked)).1
  have sameSlot : a.origin.slot = b.origin.slot :=
    a.lower.trans ((congrArg (fun a : GeneralDeclarativeWhere319.Capture => a.lower) args).trans b.lower.symm)
  have ha := fit.2 _ a.authored
  have hb := fit.2 _ b.authored
  rw [sameSlot] at ha
  have endpoint := Option.some.inj (ha.symm.trans hb)
  rw [a.endpoint,b.endpoint] at endpoint
  have payloadSame : a.payload = b.payload := by
    injection endpoint with _ span
    injection span with one _
    injection one with pt
    injection pt with o
    injection o with v
    injection v with n
  unfold WhereListHead.child WhereListHead.childDemand
  rw [payloadSame,a.whereRole,b.whereRole]

/-- An older local election on this very parent is impossible. This
does not assume that the older and newer evidence share the same Event. -/
theorem no_prior_R2_election_of_actual_where_parent411 {s q d}
    (a : WhereListHead s q d) (e : Event s q) {needs} : ¬List410.R2.elected s q e needs := by
  have inScope := e.frame.inScope
  rw [a.only] at inScope
  have same : e.frame.decl = d := List.mem_singleton.mp inScope
  rintro (old|leaf)
  · rcases old with legacy|named
    · rcases R0_selection_uses_independent_original_rule407 e legacy with general|native
      · have head : Pattern.app a.key [.var a.binder] ∈ d.head := by simp [a.named]
        obtain ⟨_,bad,_⟩ := general.2 d (by simp [a.only]) _ head
        cases bad
      · obtain ⟨native⟩ := native
        have h := (List.cons.inj (native.test.writtenHead.symm.trans
          ((congrArg Declaration.head same).trans a.named))).1
        change Pattern.app native.test.key [.var native.test.binder] =
          Pattern.app a.key [.var a.binder] at h
        have key := (Pattern.app.inj h).1
        have mode := native.test.table
        rw [key,a.table] at mode
        cases mode
    · obtain ⟨_,⟨bare⟩⟩ := named
      have h := (List.cons.inj (bare.test.named.symm.trans
        ((congrArg Declaration.head same).trans a.named))).1
      have lengths := congrArg List.length (Pattern.app.inj h).2
      cases lengths
  · obtain ⟨_,⟨leaf⟩⟩ := leaf
    have h := a.exactWhere.symm.trans
      ((congrArg Declaration.requirements same).symm.trans leaf.test.noWhere)
    cases h

theorem any_where_forest_at_its_single_raw_child411 {R s q trees}
    (cycle : RootCycle s q) (forest : WhereForest R s [q] trees) : trees = [.rejected] := by
  cases forest with
  | cons head rest =>
    cases rest
    rw [(raw_cycle_forces_the_exact_child_trace411 cycle head).1]

/-- In a fitting State every R3 declarative trace of this supported
parent has the same tree, independently of which source evidence an
alternative proof chose. This is not global classification completeness
and does not say whether an operational solver supplies a witness. -/
theorem checked_X9_tree_is_forced_in_fitting_state411
    {p : Checker408.Problem} {d : Declaration} (a : VerifiedWhereList p d)
    (cycle : RootCycle p.state a.known.child)
    (m : I72.Model) (fit : Fits p.state m)
    {t e} (trace : SourceTrace R3 p.state p.root t e) :
    t = .selected d.id [.rejected] := by
  cases trace with
  | rootK2 parent => exact (a.rawSafe parent).elim
  | other v _ impossible _ => exact (invariant_list_keeps_actual_inspection_priority411 a.known impossible).elim
  | selected event _ picked _ forest =>
    cases picked with
    | inl prior => exact (no_prior_R2_election_of_actual_where_parent411 a.known event prior).elim
    | inr current =>
      obtain ⟨_,⟨read⟩⟩ := current
      have kids := (any_where_event_retains_its_exact_child411 read).2
      have sameChild := fitting_snapshot_has_exactly_same_where_demand411 a.known read.test m fit
      have actualChild : event.kids = [a.known.child] := kids.trans (by rw [sameChild])
      have childTrees := any_where_forest_at_its_single_raw_child411 cycle (actualChild ▸ forest)
      have seen := event.frame.inScope
      rw [a.known.only] at seen
      rw [List.mem_singleton.mp seen,childTrees]

theorem checked_X9_has_no_competing_declarative_verdict_in_fitting_state411
    (p : Checker408.Problem) (r : Checker408.Result) (w : CycleWire)
    (yes : check p r (.whereChild w) = true)
    (m : I72.Model) (fit : Fits p.state m) {v : Result}
    (other : Classifies R3 p.state p.root v) : v = .rejected := by
  obtain ⟨d,_,a,_,cycle,_⟩ := accepted_where_wire_reflects_actual_child411 p r w yes
  obtain ⟨t,e,⟨trace⟩,summary⟩ := other
  rw [checked_X9_tree_is_forced_in_fitting_state411 a cycle m fit trace] at summary
  have exactReject : Summarizes (.selected d.id [.rejected]) .rejected :=
    .selected (.cons .rejected .nil) (.rejected List.mem_cons_self)
  exact (CommonRoleOutermostResolver.classification_exact _ _).mpr summary |>.symm.trans
    ((CommonRoleOutermostResolver.classification_exact _ _).mpr exactReject)

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411
