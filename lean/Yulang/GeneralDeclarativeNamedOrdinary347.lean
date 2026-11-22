import Yulang.GeneralDeclarativeNamedTable347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedOrdinary347
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralNominalRebaseRawView243 (atom slot all_exact)
open GeneralStoppedLower335 (normal)
open Core.PresenceGeneration (TyTerm CompTerm)
open PresenceNormalForm (Atom All all_append)
open CommonNominalFullCarrier (Equivalent model)

abbrev EqRow := Nat × TyTerm Nat

def atHead (raw : State) (i : Fin raw.base.slots) : Option EqRow :=
  ((raw.base.heads i).equation).map (fun t => (raw.base.source i,t.subst (slot raw.base CompTerm.var)))

def equations (raw : State) : List EqRow := (List.finRange raw.base.slots).filterMap (atHead raw)

def atoms (e : EqRow) : List (Atom Nat) :=
  [.tyLe (.var e.1) e.2,.tyLe e.2 (.var e.1)]

theorem atom_pair_exact (m : Assignment) (e : EqRow) :
    All model m (atoms e) ↔ Equivalent (m e.1).1 (e.2.eval model m) := by
  unfold atoms
  constructor
  · intro both
    exact ⟨both _ List.mem_cons_self,both _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · intro both a present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl
    · exact both.1
    · exact both.2

theorem eval_named (raw : State) (m : Assignment) (tm : TyTerm (Fin raw.base.slots)) :
    (tm.subst (slot raw.base CompTerm.var)).eval model m = tm.eval model (assignment raw.base m) := by
  rw [TyTerm.eval_subst]
  rfl

theorem stored_exact (raw : State) (m : Assignment) :
    All model m ((equations raw).flatMap atoms) ↔
      ∀ i t, (raw.base.heads i).equation = some t →
        Equivalent (m (raw.base.source i)).1 (t.eval model (assignment raw.base m)) := by
  constructor
  · intro all i t present
    let e : EqRow := (raw.base.source i,t.subst (slot raw.base CompTerm.var))
    have h : e ∈ equations raw := List.mem_filterMap.mpr ⟨i,List.mem_finRange _,by simp [atHead,present,e]⟩
    have both : All model m (atoms e) := fun a used => all a (List.mem_flatMap.mpr ⟨_,h,used⟩)
    simpa only [e,eval_named] using (atom_pair_exact m e).mp both
  · intro complete a found
    obtain ⟨e,listed,used⟩ := List.mem_flatMap.mp found
    obtain ⟨i,_,printed⟩ := List.mem_filterMap.mp listed
    obtain ⟨t,present,rfl⟩ := Option.map_eq_some_iff.mp printed
    exact ((atom_pair_exact m _).mpr (by simpa only [eval_named] using complete i t present)) a used

/-- All stored raw ordinary heads have exact named atoms. This does not
declare those equations available for head selection. There is no
point-only guard and no discard of unsupported Expr constructors. -/
def ordinary (raw : State) : GeneralDeclarativeWhere319.State :=
  ⟨(normal raw).ordinary ++ (equations raw).flatMap atoms, (normal raw).intervals⟩

theorem ordinary_exact (raw : State) (m : Assignment) :
    GeneralDeclarativeWhere319.Models (ordinary raw) m ↔
      GeneralNominalCommonBridge.Models raw.base m ∧ All model m raw.ordinary := by
  change (All model m ((raw.base.ordinary.map (atom (slot raw.base CompTerm.var)) ++ raw.ordinary) ++ _) ∧
    _) ↔ _
  rw [all_append,all_append,all_exact,stored_exact]
  have intervals :
      (∀ ab ∈ (normal raw).intervals, CommonNominalFullCarrier.Subtype (m ab.1).1 (m ab.2).1) ↔
      ∀ ab ∈ raw.base.intervals,
        CommonNominalFullCarrier.Subtype (m (raw.base.source ab.1)).1 (m (raw.base.source ab.2)).1 := by
    constructor
    · intro h p used
      exact h _ (List.mem_map_of_mem used)
    · intro h p used
      obtain ⟨prior,there,rfl⟩ := List.mem_map.mp used
      exact h prior there
  change (((_ ∧ _) ∧ _) ∧ (∀ ab ∈ (normal raw).intervals, _)) ↔ _
  rw [intervals]
  exact ⟨fun ⟨⟨⟨a,b⟩,c⟩,d⟩ => ⟨⟨a,c,d⟩,b⟩,fun ⟨⟨a,b,c⟩,d⟩ => ⟨⟨⟨a,d⟩,b⟩,c⟩⟩

end Yulang.GeneralDeclarativeNamedOrdinary347
