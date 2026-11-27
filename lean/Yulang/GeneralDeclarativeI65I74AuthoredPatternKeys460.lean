import Yulang.GeneralDeclarativeI65I74WrittenPath460
import Yulang.GeneralDeclarativeI65I74AuthoredInspectQuery456

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (legacyApply AuthoredApplication compileApply compile_apply_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RoutedNominalPoint456 (cov)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)

abbrev CoreState := Yulang.GeneralDeclarativeI65.State

private def marker : Expr := .variable 0

def emptyKey (s : CoreState) (k : Nat) : Bool :=
  match legacyApply s k [] with
  | some (.primitive .emptyRecord []) => true
  | _ => false

def pairKey (s : CoreState) (k : Nat) : Bool :=
  match legacyApply s k [marker,marker] with
  | some (.primitive .pair [_,_]) => true
  | _ => false

def declaredCovKey (s : CoreState) (k : Nat) : Bool :=
  match readUse s.current.environment k 1 with
  | some use =>
    match use.mode with
    | .declared ps => decide (ps = [cov] ∧ s.modes[k]? = some [cov])
    | _ => false
  | none => false

def nominalKey (s : CoreState) (k : Nat) : Bool :=
  match readUse s.current.environment k 1 with
  | some use =>
    match use.mode with
    | .declared _ | .invariant => true
    | .primitive _ => false
  | none => false

/-- The last two cases are boundaries, not failures of source admission.
The point class describes the declared operator only, not an assertion
about a physical endpoint at a visited site. -/
def queryKeys (s : CoreState) (k : Nat) : KeyView :=
  if emptyKey s k then .emptyRow
  else if pairKey s k then .binaryPair
  else if declaredCovKey s k then .covariantPoint
  else if nominalKey s k then .deferredNominal else .opaque

theorem declared_covariance_iff_actual_use (s : CoreState) (k : Nat) :
    declaredCovKey s k = true ↔
      (∃ use : Use s.current.environment k 1, use.mode = .declared [cov]) ∧
      s.modes[k]? = some [cov] := by
  constructor
  · intro h
    unfold declaredCovKey at h
    split at h
    · rename_i use _
      split at h
      · rename_i ps hm
        obtain ⟨yes,table⟩ := of_decide_eq_true h
        exact ⟨⟨use,by simpa [yes] using hm⟩,table⟩
      · contradiction
    · contradiction
  · rintro ⟨⟨use,mode⟩,table⟩
    have chosen := RoutedNominalPoint456.actual_declared_use_is_readable456 use mode
    simp [declaredCovKey,chosen,mode,table]

theorem query_point_key_uses_actual_declaration {s k} (h : queryKeys s k = .covariantPoint) :
    (∃ use : Use s.current.environment k 1, use.mode = .declared [cov]) ∧
       s.modes[k]? = some [cov] := by
  by_cases e : emptyKey s k = true
  · simp [queryKeys,e] at h
  by_cases p : pairKey s k = true
  · simp [queryKeys,e,p] at h
  by_cases c : declaredCovKey s k = true
  · exact (declared_covariance_iff_actual_use s k).mp c
  · simp [queryKeys,e,p,c] at h
    split at h <;> contradiction

theorem query_point_key_exact {s k} :
    queryKeys s k = .covariantPoint ↔
      emptyKey s k = false ∧ pairKey s k = false ∧
      (∃ use : Use s.current.environment k 1, use.mode = .declared [cov]) ∧
      s.modes[k]? = some [cov] := by
  have splitClass : queryKeys s k = .covariantPoint ↔
      emptyKey s k = false ∧ pairKey s k = false ∧ declaredCovKey s k = true := by
    cases a : emptyKey s k <;> cases b : pairKey s k <;>
      cases c : declaredCovKey s k <;> cases d : nominalKey s k <;>
      simp [queryKeys,a,b,c,d]
  rw [splitClass, declared_covariance_iff_actual_use]

theorem query_empty_key_exact {s k} :
    queryKeys s k = .emptyRow ↔ legacyApply s k [] = some (.primitive .emptyRecord []) := by
  have c : queryKeys s k = .emptyRow ↔ emptyKey s k = true := by
    cases a : emptyKey s k <;> cases b : pairKey s k <;>
      cases c : declaredCovKey s k <;> cases d : nominalKey s k <;>
      simp [queryKeys,a,b,c,d]
  rw [c]
  unfold emptyKey
  split <;> simp_all

theorem query_pair_key_has_actual_pair {s k} (h : queryKeys s k = .binaryPair) :
    ∃ first second, legacyApply s k [.variable 0,.variable 0] = some (.primitive .pair [first,second]) := by
  have c : pairKey s k = true := by
    cases a : emptyKey s k <;> cases b : pairKey s k <;>
      cases c : declaredCovKey s k <;> cases d : nominalKey s k <;>
      simp [queryKeys,a,b,c,d] at h ⊢
  unfold pairKey at c
  split at c
  · rename_i a b p
    exact ⟨a,b,p⟩
  · contradiction

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
