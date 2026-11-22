import Yulang.GeneralDeclarativeExactDeleteFinite337
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativeExactDelete337
open CommonNominalFullDemand (Environment Observation ProbeAt ProbeStep MaskedProbeStep ProducerLe outerLabels)
open GeneralDeclarativeExactDeleteFinite337 (delete fields Query remaining)
open CommonNominalSyntax (Layer)
open CommonNominalFullCarrier (Ty Row Subtype Equivalent observeTy)

private def fresh : List Nat → Nat
  | [] => 0
  | a::as => max (a+1) (fresh as)

private theorem before {n : Nat} {ys : List Nat} (h : n ∈ ys) :
    n < fresh ys := by
  induction ys with
  | nil => cases h
  | cons k more ih =>
    rcases List.mem_cons.mp h with rfl|tail
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
    · exact Nat.lt_of_lt_of_le (ih tail) (Nat.le_max_right ..)

theorem outside (keys : List Nat) (t : CommonNominalFullDemand.Ty R) (hidden : List Nat)
    (env : Environment R) (order) (o : Observation R) (off : ¬ o.isOuterField) :
    MaskedProbeStep relation env order hidden (delete keys t) o ↔
      MaskedProbeStep relation env order hidden t o := by
  induction t using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) generalizing hidden with
  | union a b ia ib =>
    cases o <;> simp_all [delete,Observation.isOuterField,MaskedProbeStep]
  | inter a b ia ib =>
    cases o <;> simp_all [delete,Observation.isOuterField,MaskedProbeStep]
  | mask hs a ih =>
    have no := CommonNominalFullDemand.maskedProbeStep_other
      (leRow := relation) (env := env) (argumentOrder := order) a
      (hidden ++ remaining keys hs) (hidden ++ hs) o off
    simpa only [delete,CommonNominalFullDemand.maskedProbeStep_mask] using (ih _).trans no
  | record k p a _ _ =>
    by_cases removed : k ∈ keys
    · rw [delete,ite_eq_left removed]
      refine (GeneralDeclarativeDeleteShell337.outside _ _ o off).trans ?_
      cases o <;> simp_all [Observation.isOuterField,MaskedProbeStep]
    · rw [delete,ite_eq_right removed]
      cases o <;> simp_all [Observation.isOuterField,MaskedProbeStep]
  | recordDefault k a p _ _ =>
    by_cases removed : k ∈ keys
    · rw [delete,ite_eq_left removed]
      refine (GeneralDeclarativeDeleteShell337.outside _ _ o off).trans ?_
      cases o <;> simp_all [Observation.isOuterField,MaskedProbeStep]
    · rw [delete,ite_eq_right removed]
      cases o <;> simp_all [Observation.isOuterField,MaskedProbeStep]
  | _ => first | exact Iff.rfl | trivial

theorem finite_mono {a b : CommonNominalFullDemand.Ty R} (keys : List Nat)
    (sub : ProducerLe relation a b) : ProducerLe relation (delete keys a) (delete keys b) := by
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs actual
  have previous := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp sub rank env
  have other {o : Observation R} (off : ¬o.isOuterField) (seen : ProbeAt relation rank env (delete keys b) o) :
      ProbeAt relation rank env (delete keys a) o := by
    have law (t : CommonNominalFullDemand.Ty R) :
        ProbeAt relation rank env (delete keys t) o ↔ ProbeAt relation rank env t o := by
      cases rank <;> exact outside keys t [] env _ o off
    exact (law a).mpr (previous _ ((law b).mp seen))
  have someQuery (q : Nat) : ∃ q', Query keys (outerLabels a) q q' ∧ Query keys (outerLabels b) q q' := by
    by_cases used : q ∈ keys
    · let all := (keys ++ outerLabels a) ++ outerLabels b
      let n := fresh all
      have no : n ∉ all := fun e => Nat.lt_irrefl _ (before e)
      have key : n ∉ keys := fun e => no (List.mem_append_left _ (List.mem_append_left _ e))
      have first : n ∉ outerLabels a := fun e => no (List.mem_append_left _ (List.mem_append_right _ e))
      have last : n ∉ outerLabels b := fun e => no (List.mem_append_right _ e)
      exact ⟨n,⟨fun _ => ⟨key,first⟩,fun impossible => False.elim (impossible used)⟩,
        ⟨fun _ => ⟨key,last⟩,fun impossible => False.elim (impossible used)⟩⟩
    · exact ⟨q,⟨fun impossible => False.elim (used impossible),fun _ => rfl⟩,
        ⟨fun impossible => False.elim (used impossible),fun _ => rfl⟩⟩
  have query {t : CommonNominalFullDemand.Ty R} {q q' : Nat}
      (ok : Query keys (outerLabels t) q q') (o : Observation R) :
      (ProbeAt relation rank env (delete keys t) (.field q o) ↔ ProbeAt relation rank env t (.field q' o)) ∧
      (ProbeAt relation rank env (delete keys t) (.optional q o) ↔ ProbeAt relation rank env t (.optional q' o)) := by
    cases rank <;> exact fields keys t q q' [] [] ok (by simp) o
  cases obs
  case field q o =>
    obtain ⟨n,qa,qb⟩ := someQuery q
    exact (query qa o).1.mpr (previous _ ((query qb o).1.mp actual))
  case optional q o =>
    obtain ⟨n,qa,qb⟩ := someQuery q
    exact (query qa o).2.mpr (previous _ ((query qb o).2.mp actual))
  all_goals exact other (by simp [Observation.isOuterField]) actual

def recordShell : Ty → Ty
  | .bottom => .record 0 (.node .bottom) .bottom
  | .union a b => .union (recordShell a) (recordShell b)
  | .inter a b => .inter (recordShell a) (recordShell b)
  | .mask hs a => .mask hs (recordShell a)
  | t@(.emptyRecord) | t@(.exactEmpty) | t@(.record _ _ _) | t@(.recordDefault _ _ _) => t
  | _ => .emptyRecord

/-- Standalone field deletion for the full regular observation carrier.
Payloads are retained verbatim, including any recursive state graph. -/
def subtract (keys : List Nat) : Ty → Ty
  | .union a b => .union (subtract keys a) (subtract keys b)
  | .inter a b => .inter (subtract keys a) (subtract keys b)
  | .mask hs a => .mask (remaining keys hs) (subtract keys a)
  | .record k p a => if k ∈ keys then recordShell (subtract keys a) else .record k p (subtract keys a)
  | .recordDefault k a p =>
    if k ∈ keys then recordShell (subtract keys a) else .recordDefault k (subtract keys a) p
  | t => t

open GeneralDeclarativeDeleteShell337 (shell)

theorem observe_shell (t : Ty) (d : Nat) : observeTy d (recordShell t) = shell (observeTy d t) := by
  induction t with
  | union a b ia ib =>
    change CommonNominalFinite.Ty.union (observeTy d (recordShell a)) (observeTy d (recordShell b)) =
      CommonNominalFinite.Ty.union (shell (observeTy d a)) (shell (observeTy d b))
    rw [ia,ib]
  | inter a b ia ib =>
    change CommonNominalFinite.Ty.inter (observeTy d (recordShell a)) (observeTy d (recordShell b)) =
      CommonNominalFinite.Ty.inter (shell (observeTy d a)) (shell (observeTy d b))
    rw [ia,ib]
  | mask hs t ih =>
    change CommonNominalFinite.Ty.mask hs (observeTy d (recordShell t)) = CommonNominalFinite.Ty.mask hs (shell (observeTy d t))
    rw [ih]
  | bottom => cases d <;> rfl
  | recordDefault _ _ _ _ => cases d <;> rfl
  | _ => rfl

theorem observe_subtract (keys : List Nat) (t : Ty) (d : Nat) :
    observeTy d (subtract keys t) = delete keys (observeTy d t) := by
  induction t with
  | record k p a ih =>
    by_cases inside : k ∈ keys
    · rw [subtract,ite_eq_left inside,observe_shell,ih]
      change shell (delete keys (observeTy d a)) =
        delete keys (CommonNominalFinite.Ty.record k _ (observeTy d a))
      rw [delete,ite_eq_left inside]
    · rw [subtract,ite_eq_right inside]
      change CommonNominalFinite.Ty.record k _ (observeTy d (subtract keys a)) = delete keys (CommonNominalFinite.Ty.record k _ (observeTy d a))
      rw [ih,delete,ite_eq_right inside]
  | recordDefault k a p ih =>
    by_cases inside : k ∈ keys
    · rw [subtract,ite_eq_left inside,observe_shell,ih]
      cases d with
      | zero =>
        change shell (delete keys (observeTy 0 a)) = delete keys (CommonNominalFinite.Ty.record k .bottom (observeTy 0 a))
        rw [delete,ite_eq_left inside]
      | succ d =>
        change shell (delete keys (observeTy (d+1) a)) = delete keys (CommonNominalFinite.Ty.recordDefault k (observeTy (d+1) a) _)
        rw [delete,ite_eq_left inside]
    · rw [subtract,ite_eq_right inside]
      cases d with
      | zero =>
        change CommonNominalFinite.Ty.record k .bottom (observeTy 0 (subtract keys a)) =
          delete keys (CommonNominalFinite.Ty.record k .bottom (observeTy 0 a))
        rw [ih,delete,ite_eq_right inside]
      | succ d =>
        change CommonNominalFinite.Ty.recordDefault k (observeTy (d+1) (subtract keys a)) _ =
          delete keys (CommonNominalFinite.Ty.recordDefault k (observeTy (d+1) a) _)
        rw [ih,delete,ite_eq_right inside]
  | union a b ia ib =>
    change CommonNominalFinite.Ty.union (observeTy d (subtract keys a)) (observeTy d (subtract keys b)) =
      CommonNominalFinite.Ty.union (delete keys (observeTy d a)) (delete keys (observeTy d b))
    rw [ia,ib]
  | inter a b ia ib =>
    change CommonNominalFinite.Ty.inter (observeTy d (subtract keys a)) (observeTy d (subtract keys b)) =
      CommonNominalFinite.Ty.inter (delete keys (observeTy d a)) (delete keys (observeTy d b))
    rw [ia,ib]
  | mask hs a ih =>
    change CommonNominalFinite.Ty.mask (remaining keys hs) (observeTy d (subtract keys a)) =
      CommonNominalFinite.Ty.mask (remaining keys hs) (delete keys (observeTy d a))
    rw [ih]
  | _ => rfl

theorem monotone (keys : List Nat) (included : Subtype a b) :
    Subtype (subtract keys a) (subtract keys b) := by
  intro depth
  rw [observe_subtract,observe_subtract]
  exact finite_mono keys (included depth)

theorem congruent (keys : List Nat) (same : Equivalent a b) :
    Equivalent (subtract keys a) (subtract keys b) :=
  ⟨monotone keys same.1,monotone keys same.2⟩

end Yulang.GeneralDeclarativeExactDelete337
