import Yulang.GeneralDeclarativeWhereRawAtoms346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereRawReads346
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralNominalVersionedExpressionFrame236 (reads readsMany variableSource)
open GeneralDeclarativeWhereRawExpr346 (compile)
open GeneralNominalCenters (Plan)
open GeneralSourceState (State)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralVersionedEndpointAddress315 (footprint)
open Core.PresenceGeneration (TyTerm)

theorem located (locate : Nat → Option (Fin n)) (mode : Mode) (e : Expr) {term : TyTerm (Fin n)}
    (ran : compile locate e = some term) :
    ∀ r ∈ reads mode e, r.1 = mode ∧ ∃ i, locate r.2 = some i := by
  cases e with
  | «variable» name =>
    obtain ⟨i,found,_⟩ := Option.map_eq_some_iff.mp ran
    intro r picked
    cases List.mem_singleton.mp picked
    exact ⟨rfl,i,found⟩
  | primitive constructor args =>
    cases constructor with
    | scalar _ | emptyRecord | exactEmpty =>
      cases args with
      | nil => intro _ no; cases no
      | cons => cases ran
    | pair =>
      cases args with
      | nil => cases ran
      | cons x xs =>
        cases xs with
        | nil => cases ran
        | cons y rest =>
          cases rest with
          | cons => cases ran
          | nil =>
            cases a : compile locate x <;> cases b : compile locate y <;> simp [compile,a,b] at ran
            intro r h
            change r ∈ reads mode x ++ (reads mode y ++ []) at h
            rw [List.append_nil] at h
            rcases List.mem_append.mp h with front | back
            · exact located locate mode x a r front
            · exact located locate mode y b r back
  | nominal _ _ => cases ran
  | record label x y | join x y =>
    cases a : compile locate x <;> cases b : compile locate y <;> simp [compile,a,b] at ran
    intro r h
    change r ∈ reads mode x ++ reads mode y at h
    rcases List.mem_append.mp h with front | back
    · exact located locate mode x a r front
    · exact located locate mode y b r back
  | variant tag x =>
    cases a : compile locate x <;> simp [compile,a] at ran
    exact located locate mode x a
termination_by sizeOf e
decreasing_by all_goals subst_vars; simp_wf; omega

private theorem positions (s : State) (f : α → Nat) (rs : List α)
    (routes : ∀ x ∈ rs, ∃ i, sourceSlot s (f x) = some i) :
    ∃ ids, rs.mapM (fun k => sourceSlot s (f k)) = some ids ∧
      ids.map s.source = rs.map f := by
  induction rs with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons a as ih =>
    obtain ⟨i,known⟩ := routes a List.mem_cons_self
    obtain ⟨is,rest,same⟩ := ih (fun x h => routes x (List.mem_cons_of_mem _ h))
    exact ⟨i::is,by simp [List.mapM_cons,known,rest],by simp [(sourceSlot_exact ..).mp known,same]⟩

/-- Every operand read has its literal physical position, in the same
order as recorded in the address's footprint. Repetitions stay. -/
theorem exact_paths {p : Plan rs} {s : State} {mode : Mode} {e : Expr} {term : TyTerm (Fin s.slots)}
    (ran : compile (fun name => sourceSlot s (variableSource p mode name)) e = some term) :
    ∃ ids, (reads mode e).mapM (fun k => sourceSlot s (variableSource p k.1 k.2)) = some ids ∧
      ids.map s.source = footprint p mode e := by
  apply positions
  intro x present
  obtain ⟨same,stored⟩ := located _ _ _ ran x present
  rw [same]
  exact stored

theorem nominal_declines (locate : Nat → Option (Fin n)) (key : Nat) (args : List Expr) :
    compile locate (.nominal key args) = none := rfl

end Yulang.GeneralDeclarativeWhereRawReads346
