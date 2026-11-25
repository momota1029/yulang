import Yulang.GeneralDeclarativeI65I72GroundedDependencies405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem binder_map_at405 (ns : List Nat) (first : Nat) (p : VariablePosition405) :
    p ∈ ns.mapIdx (fun i n => ⟨first,i,n⟩) ↔
      p.visibleOrdinal = first ∧ ns[p.argumentOrdinal]? = some p.binder := by
  constructor
  · intro found
    obtain ⟨i,within,atI⟩ := List.mem_mapIdx.mp found
    rw [← atI]
    exact ⟨rfl,List.getElem?_eq_getElem within⟩
  · intro ⟨atRow,atArg⟩
    obtain ⟨h,value⟩ := List.getElem?_eq_some_iff.mp atArg
    apply List.mem_mapIdx.mpr
    cases p
    simp_all

/-- Both directions retain each written binder at its real source
position. The order/pruning of a registry lookup cannot turn a matched
entry's argument into one from another declaration or another request. -/
theorem variable_scan_position_iff405 {s : State} {q rows} {t : CandidateTape s.core q rows}
    (scan : VariableScan405 t) (first : Nat) (p : VariablePosition405) :
    p ∈ scan.positions first ↔
      ∃ (i : Nat) (row : Declaration) (a : Capture), p.visibleOrdinal = first + i ∧
        rows[i]? = some row ∧ row.head[p.argumentOrdinal]? = some (.var p.binder) ∧
        q.demand.arguments[p.argumentOrdinal]? = some a := by
  induction scan generalizing first with
  | nil => simp [VariableScan405.positions]
  | @matched row rows tail pick original more ih =>
    simp only [VariableScan405.positions,List.mem_append,binder_map_at405,ih]
    constructor
    · rintro (⟨atRow,atArg⟩ | ⟨idx,d,a,atRow,atDecl,atHead,atArg⟩)
      · have below : p.argumentOrdinal < original.binders.length :=
          (List.getElem?_eq_some_iff.mp atArg).choose
        have inArgs : p.argumentOrdinal < q.demand.arguments.length :=
          original.sameArity ▸ below
        refine ⟨0,row,q.demand.arguments[p.argumentOrdinal],by simpa using atRow,rfl,?_,
          List.getElem?_eq_getElem inArgs⟩
        rw [original.literal,List.getElem?_map,atArg]
        rfl
      · refine ⟨idx+1,d,a,by omega,?_,atHead,atArg⟩
        simpa using atDecl
    · rintro ⟨i,d,a,atRow,atDecl,atHead,atArg⟩
      cases i with
      | zero =>
        have originalRow : row = d := Option.some.inj atDecl
        subst d
        left
        refine ⟨by simpa using atRow,?_⟩
        rw [original.literal,List.getElem?_map] at atHead
        cases read : original.binders[p.argumentOrdinal]? with
        | none => simp [read] at atHead
        | some written =>
          simpa [read] using atHead
      | succ i =>
        exact .inr ⟨i,d,a,by omega,by simpa using atDecl,atHead,atArg⟩

private theorem zip_strict405 (xs : List α) (first : Nat) :
    xs.zipIdx first |>.Pairwise (fun a b => a.2 < b.2) := by
  induction xs generalizing first with
  | nil => simp [List.zipIdx]
  | cons a t ih =>
    rw [List.zipIdx_cons,List.pairwise_cons]
    refine ⟨?_,ih _⟩
    rintro ⟨b,i⟩ found
    have atLeast := (List.mem_zipIdx found).1
    exact Nat.lt_of_succ_le atLeast

/-- Iteration is lexicographic in the original visible rows and
argument ordinals, even when the same binder occurs several times. -/
theorem variable_positions_keep_source_order405 {s : State} {q rows}
    {t : CandidateTape s.core q rows} (scan : VariableScan405 t) (first : Nat) :
    (scan.positions first).Pairwise (fun a b =>
      a.visibleOrdinal < b.visibleOrdinal ∨
      a.visibleOrdinal = b.visibleOrdinal ∧ a.argumentOrdinal < b.argumentOrdinal) := by
  induction scan generalizing first with
  | nil => simp [VariableScan405.positions]
  | @matched row rows tail pick original more ih =>
    simp only [VariableScan405.positions,List.pairwise_append]
    refine ⟨?_,ih _,?_⟩
    · rw [List.mapIdx_eq_zipIdx_map,List.pairwise_map]
      apply List.Pairwise.imp _ (zip_strict405 original.binders 0)
      exact fun hh => .inr ⟨rfl,hh⟩
    · intro a head b tail
      have atA := (binder_map_at405 _ _ _).mp head |>.1
      obtain ⟨i,d,c,atB,_,_,_⟩ := (variable_scan_position_iff405 more (first+1) b).mp tail
      exact .inl (by omega)

theorem grounded_argument_has_unique_literal_address405 {R s q e needs support}
    (selected : GroundedSelection405 (s := s) (q := q) R e needs support)
    {p : VariablePosition405} (present : p ∈ selected.scan.positions) :
    ∃ (raw : Nat) (row : Declaration) (a : Capture),
      unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
        (authoredRegistry s.core.current).declarations p.visibleOrdinal = some raw ∧
      (authoredRegistry s.core.current).declarations[raw]? = some row ∧
      row.head[p.argumentOrdinal]? = some (.var p.binder) ∧ q.demand.arguments[p.argumentOrdinal]? = some a := by
  obtain ⟨i,d,a,visibleI,atDecl,head,atArg⟩ :=
    (variable_scan_position_iff405 selected.scan 0 p).mp present
  obtain ⟨raw,read,same⟩ := unfilterOrdinal395_exact (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations i atDecl
  exact ⟨raw,d,a,by simpa [visibleI] using read,same,head,atArg⟩

end Yulang.GeneralDeclarativeI65.I72
