import Yulang.GeneralDeclarativeI65I74WhereSamePhaseSource454

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open InternalK2452
open GroupedEntry453 (GroupedReport OriginView)

private theorem relabelClassKeys (f : Nat → Nat) (xs : List Nat)
    (inject : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    classKeys (xs.map f) = (classKeys xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have small := ih (fun u hu v hv => inject u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
    have inBoth : f x ∈ (classKeys xs).map f ↔ x ∈ classKeys xs := by
      constructor
      · intro yes
        obtain ⟨y,hy,e⟩ := List.mem_map.mp yes
        have h := (seen_class_keys_exact451 xs y).mp hy
        have same := inject y (List.mem_cons_of_mem _ h) x List.mem_cons_self e
        exact same ▸ hy
      · intro yes
        exact List.mem_map.mpr ⟨x,yes,rfl⟩
    have leftKeys : (x::xs).map f = f x :: xs.map f := rfl
    rw [leftKeys]
    simp only [classKeys]
    rw [small]
    by_cases xIn : x ∈ classKeys xs
    · simp [xIn,inBoth.mpr xIn]
    · have no : f x ∉ (classKeys xs).map f := fun h => xIn (inBoth.mp h)
      simp [xIn,no]

private def relabelMark (f : Nat → Nat) (m : OriginalMark) : OriginalMark :=
  {m with classLabel := f m.classLabel}

private theorem marked_group_relabels (f : Nat → Nat) (marks : List OriginalMark)
    (inject : ∀ u ∈ marks.map OriginalMark.classLabel,
      ∀ v ∈ marks.map OriginalMark.classLabel, f u = f v → u = v)
    (k : Nat) (active : k ∈ marks.map OriginalMark.classLabel) :
    (marks.map (relabelMark f)).filter (fun m => m.classLabel == f k) =
      (marks.filter fun m => m.classLabel == k).map (relabelMark f) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro m known
  change (f m.classLabel == f k) = (m.classLabel == k)
  by_cases same : m.classLabel = k
  · simp [same]
  · have different : f m.classLabel ≠ f k := fun eq =>
      same (inject _ (List.mem_map.mpr ⟨m,known,rfl⟩) _ active eq)
    exact (beq_eq_false_iff_ne.mpr different).trans (beq_eq_false_iff_ne.mpr same).symm

private def groupsAt (marks : List OriginalMark) : List CohortOrigins :=
  (classKeys (marks.map OriginalMark.classLabel)).map fun k =>
    ⟨k,marks.filter fun m => m.classLabel == k⟩

private def cyclicViews (marks : List OriginalMark) : List (List OriginView) :=
  ((groupsAt marks).filter fun g => g.marks.any OriginalMark.rawK2).map fun g =>
    g.marks.map OriginalMark.literal

private theorem visible_cyclic_views_invariant_under_injective_relabeling
    (f : Nat → Nat) (marks : List OriginalMark)
    (inject : ∀ u ∈ marks.map OriginalMark.classLabel,
      ∀ v ∈ marks.map OriginalMark.classLabel, f u = f v → u = v) :
    cyclicViews (marks.map (relabelMark f)) = cyclicViews marks := by
  have labelMap : (marks.map (relabelMark f)).map OriginalMark.classLabel =
      (marks.map OriginalMark.classLabel).map f := by
    simp [List.map_map,Function.comp_def,relabelMark]
  let relabelGroup : CohortOrigins → CohortOrigins := fun g =>
    ⟨f g.key,g.marks.map (relabelMark f)⟩
  have grouped : groupsAt (marks.map (relabelMark f)) =
      (groupsAt marks).map relabelGroup := by
    unfold groupsAt
    rw [labelMap,relabelClassKeys f _ inject]
    simp only [List.map_map]
    apply List.map_eq_map_iff.mpr
    intro k selected
    have active := (seen_class_keys_exact451 _ _).mp selected
    simp only [Function.comp_apply,relabelGroup]
    rw [marked_group_relabels f marks inject k active]
  unfold cyclicViews
  rw [grouped,List.filter_map]
  have bits (g : CohortOrigins) :
      (relabelGroup g).marks.any OriginalMark.rawK2 = g.marks.any OriginalMark.rawK2 := by
    change (g.marks.map (relabelMark f)).any OriginalMark.rawK2 = _
    rw [List.any_map]
    rfl
  have values (g : CohortOrigins) :
      (relabelGroup g).marks.map OriginalMark.literal = g.marks.map OriginalMark.literal := by
    change (g.marks.map (relabelMark f)).map OriginalMark.literal = _
    rw [List.map_map]
    rfl
  have filterEq : ((fun g : CohortOrigins => g.marks.any OriginalMark.rawK2) ∘ relabelGroup) =
      (fun g : CohortOrigins => g.marks.any OriginalMark.rawK2) := funext bits
  have mapEq : ((fun g : CohortOrigins => g.marks.map OriginalMark.literal) ∘ relabelGroup) =
      (fun g : CohortOrigins => g.marks.map OriginalMark.literal) := funext values
  rw [filterEq,List.map_map,mapEq]

private theorem transfer_diagnostic_mark {p : Checker408.Problem} {a : ParentSelection p}
    (d e : OriginalDiagnostic a) {i : Nat} {u : OriginalMark}
    (left : d.marks[i]? = some u) :
    ∃ v : OriginalMark, e.marks[i]? = some v ∧ u.literal = v.literal := by
  have row := congrArg (fun xs : List OriginView => xs[i]?)
    (exact_all_original_literal_marks_independent_of_wires451 d e)
  rw [List.getElem?_map,List.getElem?_map,left] at row
  cases right : e.marks[i]? with
  | none => simp [right] at row
  | some v =>
    simp only [right,Option.map_some,Option.some.injEq] at row
    exact ⟨v,rfl,row⟩

private theorem transfer_two_label_equalities {p : Checker408.Problem} {a : ParentSelection p}
    (d e : OriginalDiagnostic a) {i j : Nat} {u v u' v' : OriginalMark}
    (ui : d.marks[i]? = some u) (vj : d.marks[j]? = some v)
    (ui' : e.marks[i]? = some u') (vj' : e.marks[j]? = some v')
    (first : u.literal = u'.literal) (last : v.literal = v'.literal) :
    u.classLabel = v.classLabel ↔ u'.classLabel = v'.classLabel := by
  let d' : InternalReport (liftProblem p) := ⟨⟨a,d⟩⟩
  let e' : InternalReport (liftProblem p) := ⟨⟨a,e⟩⟩
  have f := same_phase_key_iff_same_role_and_raw_alias_at_actual_marks454 d'
    (List.mem_of_getElem? ui) (List.mem_of_getElem? vj)
  have t := same_phase_key_iff_same_role_and_raw_alias_at_actual_marks454 e'
    (List.mem_of_getElem? ui') (List.mem_of_getElem? vj')
  have firstTag : (u.request.demand.role,u.actualCenter) = (u'.request.demand.role,u'.actualCenter) := by
    exact congrArg (fun x : OriginView => (x.2.2.2.1,x.2.2.2.2.1)) first
  have lastTag : (v.request.demand.role,v.actualCenter) = (v'.request.demand.role,v'.actualCenter) := by
    exact congrArg (fun x : OriginView => (x.2.2.2.1,x.2.2.2.2.1)) last
  rw [firstTag,lastTag] at f
  exact f.trans t.symm

private theorem same_actual_mark_index {p : Checker408.Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) {i : Nat} {u : OriginalMark}
    (h : d.marks[i]? = some u) : u.ordinal = i := by
  have inside : i < a.decl.requirements.length :=
    (ordered_marks_no_fewer_and_no_extra_original_clauses451 d) ▸
      (List.getElem?_eq_some_iff.mp h).choose
  have clause : a.decl.requirements[i]? = some a.decl.requirements[i] :=
    List.getElem?_eq_getElem inside
  obtain ⟨_,_,_,_,_,_,found,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d clause
  exact congrArg OriginalMark.ordinal (Option.some.inj (h.symm.trans found))

private theorem full_mark_match_after_relabel
    {p : Checker408.Problem} {a : ParentSelection p} (d e : OriginalDiagnostic a)
    {i : Nat} (f : Nat → Nat) {u v : OriginalMark}
    (left : d.marks[i]? = some u) (right : e.marks[i]? = some v)
    (literal : u.literal = v.literal) (rel : f u.classLabel = v.classLabel) :
    relabelMark f u = v := by
  have pos : u.ordinal = v.ordinal :=
    (same_actual_mark_index d left).trans (same_actual_mark_index e right).symm
  have lu := (any_mark_is_actual_original_diagnostic451 d (List.mem_of_getElem? left)).1
  have rv := (any_mark_is_actual_original_diagnostic451 e (List.mem_of_getElem? right)).1
  rw [pos] at lu
  have request := Option.some.inj (lu.symm.trans rv)
  cases u with
  | mk uo ui uq uc ul ub =>
    cases v with
    | mk vo vi vq vc vl vb =>
      change uo = vo at pos
      change uq = vq at request
      subst vo
      subst vq
      simp only [OriginalMark.literal,Prod.mk.injEq,true_and] at literal
      rcases literal with ⟨wid,_,_,payload,cycle⟩
      change f ul = vl at rel
      subst vi
      subst vc
      subst vl
      rfl

private def AtKey {p : Checker408.Problem} {a : ParentSelection p}
    (d e : OriginalDiagnostic a) (l r : Nat) : Prop :=
  ∃ (i : Nat) (u v : OriginalMark), d.marks[i]? = some u ∧ e.marks[i]? = some v ∧
    u.classLabel = l ∧ v.classLabel = r

private theorem related_keys_agree_iff {p : Checker408.Problem} {a : ParentSelection p}
    (d e : OriginalDiagnostic a) {l r l' r' : Nat}
    (first : AtKey d e l r) (last : AtKey d e l' r') : l = l' ↔ r = r' := by
  obtain ⟨i,u,v,ui,vi,ul,vr⟩ := first
  obtain ⟨j,u',v',uj,vj,ul',vr'⟩ := last
  obtain ⟨u2,seen,obs⟩ := transfer_diagnostic_mark d e ui
  obtain ⟨v2,found,obs'⟩ := transfer_diagnostic_mark d e uj
  cases Option.some.inj (seen.symm.trans vi)
  cases Option.some.inj (found.symm.trans vj)
  rw [←ul,←ul',←vr,←vr']
  exact transfer_two_label_equalities d e ui uj vi vj obs obs'

private theorem active_key_has_exact_other_key {p : Checker408.Problem} {a : ParentSelection p}
    (d e : OriginalDiagnostic a) {k : Nat} (active : k ∈ d.marks.map OriginalMark.classLabel) :
    ∃ r, AtKey d e k r := by
  obtain ⟨u,mem,label⟩ := List.mem_map.mp active
  obtain ⟨i,atU⟩ := List.mem_iff_getElem?.mp mem
  obtain ⟨v,atV,_⟩ := transfer_diagnostic_mark d e atU
  exact ⟨v.classLabel,i,u,v,atU,atV,label,rfl⟩

theorem same_parent_reports_are_independent_of_all_wire_label_choices454
    {p : FullProblem} (a : ParentSelection p.old) (d e : OriginalDiagnostic a) :
    exactReport (⟨⟨a,d⟩⟩ : InternalReport p) = exactReport (⟨⟨a,e⟩⟩ : InternalReport p) := by
  classical
  let f (k : Nat) : Nat := if h : ∃ r, AtKey d e k r then Classical.choose h else 0
  have chosen {k} (ha : ∃ r, AtKey d e k r) : AtKey d e k (f k) := by
    simpa [f,ha] using Classical.choose_spec ha
  have inject : ∀ l ∈ d.marks.map OriginalMark.classLabel,
      ∀ r ∈ d.marks.map OriginalMark.classLabel, f l = f r → l = r := by
    intro l lIn r rIn eq
    exact (related_keys_agree_iff d e
      (chosen (active_key_has_exact_other_key d e lIn))
      (chosen (active_key_has_exact_other_key d e rIn))).mpr eq
  have align : d.marks.map (relabelMark f) = e.marks := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map]
    cases found : d.marks[i]? with
    | none =>
      have lengthEq : d.marks.length = e.marks.length :=
        (ordered_marks_no_fewer_and_no_extra_original_clauses451 d).trans
          (ordered_marks_no_fewer_and_no_extra_original_clauses451 e).symm
      have empty : e.marks[i]? = none := List.getElem?_eq_none_iff.mpr
        (lengthEq ▸ List.getElem?_eq_none_iff.mp found)
      rw [empty]
      rfl
    | some u =>
      obtain ⟨v,atV,obs⟩ := transfer_diagnostic_mark d e found
      have matched : AtKey d e u.classLabel v.classLabel := ⟨i,u,v,found,atV,rfl,rfl⟩
      have reflected := (related_keys_agree_iff d e (chosen ⟨_,matched⟩) matched).mp rfl
      rw [atV]
      exact congrArg some (full_mark_match_after_relabel d e f found atV obs reflected)
  have views := visible_cyclic_views_invariant_under_injective_relabeling f d.marks inject
  rw [align] at views
  change (⟨p.root.occurrence,a.decl.id,cyclicViews d.marks⟩ : GroupedReport) =
    ⟨p.root.occurrence,a.decl.id,cyclicViews e.marks⟩
  rw [views]

private theorem literal_mark_injective_on_actual_roster
    {p : Checker408.Problem} {a : ParentSelection p} (d : OriginalDiagnostic a)
    {u v : OriginalMark} (lm : u ∈ d.marks) (rm : v ∈ d.marks)
    (same : u.literal = v.literal) : u = v := by
  obtain ⟨i,h⟩ := List.mem_iff_getElem?.mp lm
  obtain ⟨j,k⟩ := List.mem_iff_getElem?.mp rm
  have ord : u.ordinal = v.ordinal := congrArg Prod.fst same
  rw [same_actual_mark_index d h,same_actual_mark_index d k] at ord
  subst j
  exact Option.some.inj (h.symm.trans k)

theorem accepted_raw_diagnostic_never_duplicates_a_projected_group454
    {p : FullProblem} {r : GroupedReport} (valid : Exact p r) :
    r.origins.Nodup := by
  obtain ⟨x,_,same⟩ := valid
  apply same.2.2.nodup_iff.mpr
  change (x.groups.map fun g => g.marks.map OriginalMark.literal).Nodup
  apply List.pairwise_map.mpr
  have keys : x.groups.Pairwise (fun g h => g.key ≠ h.key) :=
    List.pairwise_map.mp (cyclic_groups_keep_unique_keys452 x.original.diagnostics)
  apply List.Pairwise.imp_of_mem ?_ keys
  intro g h gMem hMem differ eq
  have gValid := one_checked_entry_means_K2_at_every_original452 x.original.diagnostics gMem
  have hValid := one_checked_entry_means_K2_at_every_original452 x.original.diagnostics hMem
  obtain ⟨m,ms,members⟩ := List.exists_cons_of_ne_nil gValid.2.1
  have mIn : m ∈ g.marks := members.symm ▸ List.mem_cons_self
  have listed : m.literal ∈ h.marks.map OriginalMark.literal :=
    eq ▸ List.mem_map.mpr ⟨m,mIn,rfl⟩
  obtain ⟨n,nIn,sameLit⟩ := List.mem_map.mp listed
  have individual := literal_mark_injective_on_actual_roster x.original.diagnostics
    (gValid.2.2.1.subset mIn) (hValid.2.2.1.subset nIn) sameLit.symm
  subst n
  have both := (actual_cycle_has_exactly_one_internal_diagnostic452 x.original.diagnostics
      (gValid.2.2.1.subset mIn)).mp (gValid.2.2.2 m mIn)
  obtain ⟨_,_,unique⟩ := both
  have sameGroup := (unique g ⟨gMem,mIn⟩).trans (unique h ⟨hMem,nIn⟩).symm
  exact differ (congrArg CohortOrigins.key sameGroup)

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
