import Yulang.GeneralDeclarativeRecordNames330
import Yulang.GeneralNominalCommonBridge

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordTail330
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeRecordNames330 (expose lifts)
open GeneralDeclarativeOpaqueNames328 (kept first second extend right_value)
open CommonNominalFullCarrier (Ty Equivalent record exactEmpty observeTy)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment shadow)
open CommonNominalFullDemand (ProbeAt ProbeStep MaskedProbeStep Environment)

theorem show_shadow {s : State} (key root : Nat) (protect : List Nat) (m : Assignment) (payload buried tail : Ty)
    (old : Models s m) (whole : Equivalent (m root).1 (record key payload tail)) :
    (Models (expose s root key protect) (extend s root protect m payload tail) ∧
      ∀ n ∈ kept s root protect, extend s root protect m payload tail n = m n) ∧
    (Models (expose s root key protect) (extend s root protect m payload (record key buried tail)) ∧
      ∀ n ∈ kept s root protect, extend s root protect m payload (record key buried tail) n = m n) :=
  ⟨lifts root key protect m old whole,
    lifts root key protect m old (eqv_trans whole (eqv_symm (shadow key payload buried tail)))⟩

def env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => []⟩

theorem distinct_tails (key : Nat) (extra : Ty) :
    ¬Equivalent exactEmpty (record key extra exactEmpty) := by
  intro e
  have yes : ProbeAt Common.rowLe 0 env (observeTy 0 (record key extra exactEmpty)) (.field key .trivial) := by
    simp [record,exactEmpty,observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalSyntax.observe,
      ProbeAt,ProbeStep,MaskedProbeStep]
  have no := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (e.1 0) 0 env (.field key .trivial) yes
  exact no

abbrev clean : State := ⟨⟨[],[]⟩,[]⟩
def input (key : Nat) : Assignment := fun _ => (record key .top exactEmpty, Common.rowEmpty)

theorem incoming (key : Nat) : Models clean (input key) :=
  ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,
     fun _ h => False.elim (List.not_mem_nil h)⟩

/-- Merely storing the full record equation is insufficient for source
tail subtraction: the genuinely hidden key can occur in one admissible
tail and be absent in another, without changing any old or fixed target
name. A canonical source remainder must be justified separately. -/
theorem does_not_fix_remainder (key root : Nat) (protect : List Nat) :
    ∃ m n, (Models (expose clean root key protect) m ∧ Models (expose clean root key protect) n) ∧
      (∀ q ∈ kept clean root protect, m q = n q) ∧
      ¬Equivalent (m (second clean root protect)).1 (n (second clean root protect)).1 := by
  obtain ⟨⟨firstModel,left⟩,⟨secondModel,right⟩⟩ :=
    show_shadow key root protect (input key) .top .bottom exactEmpty (incoming key) (eqv_refl _)
  refine ⟨_,_,⟨firstModel,secondModel⟩,fun n keptName => (left n keptName).trans (right n keptName).symm,?_⟩
  rw [right_value,right_value]
  exact distinct_tails key .bottom

end Yulang.GeneralDeclarativeRecordTail330
