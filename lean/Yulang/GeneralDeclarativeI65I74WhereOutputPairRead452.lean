import Yulang.GeneralDeclarativeI65I74WhereLiteralInternal452

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open ListSites449.Frame (frame_lookup_preserves_original_capture449)

private theorem actual_capture_position452 {p : Checker408.Problem}
    (a : ParentSelection p) {i : Nat} {c : Clause}
    (theClause : a.decl.requirements[i]? = some c) {binder : Nat}
    (written : c.arguments = [.var binder]) :
    let z := (a.chosen.roster.capture binder).center
    (binder,z) ∈ a.chosen.roster.bindings ∧
      (roleDecls p c.role).arity = 1 ∧
      a.children[i]? = some ⟨p.root.occurrence ++ [i],⟨c.role,[point z],[]⟩⟩ := by
  obtain ⟨b,n,args,binding,cap,request⟩ := known_original_clause_has_actual_payload451 a theClause
  have identity : b = binder := by simpa using args.symm.trans written
  subst b
  have count := (a.chosen.checked.signature.2.2.2 c (List.mem_of_getElem? theClause)).1
  rw [written] at count
  dsimp only
  rw [cap]
  exact ⟨binding,count.symm,request⟩

/-- Read the actual authored clause and its original binding at the
given ordinal. Neither the chosen payload nor a guessed site name
is accepted as input. -/
def readActualSite452 {p : Checker408.Problem} (a : ParentSelection p) (i : Nat) :
    Option (SourcePointAt a i) :=
  match actual : a.decl.requirements[i]? with
  | none => none
  | some c =>
    match header : c.arguments with
    | [.var binder] =>
      let slot := (a.chosen.roster.capture binder).center
      have body := actual_capture_position452 a actual header
      some ⟨c,actual,binder,slot,header,body.1,body.2.1,body.2.2⟩
    | _ => none

theorem sites_at_same_exact_ordinal_are_unique452 {p : Checker408.Problem}
    {a : ParentSelection p} {i} (x y : SourcePointAt a i) : x = y := by
  cases x with
  | mk c same binder slot h binding arity req =>
    cases y with
    | mk c' same' binder' slot' h' binding' arity' req' =>
      have clause := Option.some.inj (same.symm.trans same')
      subst c'
      have names : binder = binder' := by simpa using h.symm.trans h'
      subst binder'
      have xs := frame_lookup_preserves_original_capture449 a.chosen.roster a.chosen.distinct binding
      have ys := frame_lookup_preserves_original_capture449 a.chosen.roster a.chosen.distinct binding'
      have centers := congrArg GeneralDeclarativeWhere319.Capture.center (xs.symm.trans ys)
      change slot = slot' at centers
      subst slot'
      rfl

theorem actual_source_site_replay_is_exact452 {p : Checker408.Problem}
    {a : ParentSelection p} {i} (x : SourcePointAt a i) : readActualSite452 a i = some x := by
  unfold readActualSite452
  split
  · rename_i miss
    rw [x.indexed] at miss
    contradiction
  · rename_i c actual
    have eq := Option.some.inj (actual.symm.trans x.indexed)
    subst c
    split
    · rename_i binder header
      exact congrArg some (sites_at_same_exact_ordinal_are_unique452 _ x)
    · rename_i skip
      exact (skip _ x.header).elim

theorem mark_is_read_at_its_own_source_ordinal452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m : OriginalMark} (found : m ∈ d.marks) :
    d.marks[m.ordinal]? = some m := by
  obtain ⟨i,position⟩ := List.mem_iff_getElem?.mp found
  have enough : i < a.decl.requirements.length :=
    (ordered_marks_no_fewer_and_no_extra_original_clauses451 d) ▸
      (List.getElem?_eq_some_iff.mp position).choose
  let clause := a.decl.requirements[i]
  have authored : a.decl.requirements[i]? = some clause := List.getElem?_eq_getElem enough
  obtain ⟨_,_,_,_,_,_,location,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d authored
  have eq := Option.some.inj (position.symm.trans location)
  subst m
  exact position

theorem any_replayed_site_uses_the_marked_request452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m : OriginalMark}
    (genuine : m ∈ d.marks) (x : SourcePointAt a m.ordinal) :
    x.original.id = m.writtenId ∧ x.capture = m.actualCenter ∧ x.request = m.request := by
  obtain ⟨y,proof⟩ := original_mark_has_exact_actual_source_site452 d genuine
  rwa [sites_at_same_exact_ordinal_are_unique452 x y]

private theorem actual_group_from_pair452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m n : OriginalMark}
    (first : m ∈ d.marks) (last : n ∈ d.marks) (same : m.classLabel = n.classLabel) :
    let g : CohortOrigins := ⟨m.classLabel,d.atClass m.classLabel⟩
    g ∈ d.cohortsWithOrigins ∧ m ∈ g.marks ∧ n ∈ g.marks := by
  exact ⟨List.mem_map.mpr ⟨m.classLabel,(seen_class_keys_exact451 _ _).mpr
    (List.mem_map.mpr ⟨m,first,rfl⟩),rfl⟩,
    (only_marks_of_selected_class451 d _ _).mpr ⟨first,rfl⟩,
    (only_marks_of_selected_class451 d _ _).mpr ⟨last,same.symm⟩⟩

/-- Data-only pair addressing. A wrong ordinal or a cross-class pair
does not supply evidence. Both source sites are reconstructed. -/
def readActualPhasePair452 {p : FullProblem} {a : ParentSelection p.old}
    (d : OriginalDiagnostic a) (i j : Nat) : Option (ActualPair (p := p) d) :=
  match li : d.marks[i]?, rj : d.marks[j]? with
  | some m,some n => do
    if same : m.classLabel = n.classLabel then
      let x ← readActualSite452 a m.ordinal
      let y ← readActualSite452 a n.ordinal
      let lm := List.mem_of_getElem? li
      let rm := List.mem_of_getElem? rj
      let ⟨group,left,right⟩ := actual_group_from_pair452 d lm rm same
      let lx := any_replayed_site_uses_the_marked_request452 d lm x
      let ry := any_replayed_site_uses_the_marked_request452 d rm y
      pure ⟨⟨m.classLabel,d.atClass m.classLabel⟩,group,m,n,left,right,x,y,lx.2.1,ry.2.1,lx.2.2,ry.2.2⟩
    else none
  | _,_ => none

theorem actual_pairs_at_exact_original_ordinals_have_finite_read452 {p : FullProblem}
    {a : ParentSelection p.old} {d : OriginalDiagnostic a} (x : ActualPair (p := p) d) :
    readActualPhasePair452 d x.left.ordinal x.right.ordinal = some x := by
  have src := (generated_group_has_exact_source_order451 d x.genuine)
  have lm := src.2.2.subset x.inLeft
  have rm := src.2.2.subset x.inRight
  have lk := (only_marks_of_selected_class451 d _ _).mp (src.1 ▸ x.inLeft) |>.2
  have rk := (only_marks_of_selected_class451 d _ _).mp (src.1 ▸ x.inRight) |>.2
  have group : x.group = ⟨x.left.classLabel,d.atClass x.left.classLabel⟩ := by
    cases h : x.group with
    | mk key marks =>
      simp only [h] at lk src ⊢
      rw [src.1,lk]
  unfold readActualPhasePair452
  split
  · rename_i left right tl tr
    rw [mark_is_read_at_its_own_source_ordinal452 d lm] at tl
    rw [mark_is_read_at_its_own_source_ordinal452 d rm] at tr
    cases Option.some.inj tl
    cases Option.some.inj tr
    rw [dite_eq_left (lk.trans rk.symm)]
    simp only [actual_source_site_replay_is_exact452 x.first,
      actual_source_site_replay_is_exact452 x.second,Bind.bind,Option.bind,Option.pure_def]
    cases x with
    | mk g valid m n left right u v ax ay bx byx =>
      change g = ⟨m.classLabel,d.atClass m.classLabel⟩ at group
      subst g
      rfl
  · rename_i h
    exact (h _ _ (mark_is_read_at_its_own_source_ordinal452 d lm)
      (mark_is_read_at_its_own_source_ordinal452 d rm)).elim

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
