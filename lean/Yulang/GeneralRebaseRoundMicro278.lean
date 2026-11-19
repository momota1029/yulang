import Yulang.GeneralVersionRebaseCertificate259
import Yulang.GeneralDictionaryRebaseRun259

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRoundMicro278

inductive Phase where
  | enter | installed | refreshed
  deriving DecidableEq, Repr

structure Tick where
  round : Nat
  phase : Phase
  deriving DecidableEq, Repr

def next : Tick → Tick
  | ⟨n,.enter⟩ => ⟨n,.installed⟩
  | ⟨n,.installed⟩ => ⟨n,.refreshed⟩
  | ⟨n,.refreshed⟩ => ⟨n+1,.enter⟩

def initial : Tick := ⟨0,.enter⟩

def fired (t : Tick) : Bool :=
  !(t.round == 0 && t.phase == .enter)

theorem next_fired (t : Tick) : fired (next t) = true := by
 cases t with
 | mk n phase =>
   cases phase <;> cases n <;> rfl

theorem unfired (t : Tick) : fired t = false ↔ t = initial := by
 cases t with
 | mk n phase =>
   cases phase <;> cases n <;> first | decide +revert | simp [fired,initial]

def iterate : Nat → Tick
  | 0 => initial
  | n+1 => next (iterate n)

theorem iterate_succ (n : Nat) : fired (iterate (n+1)) = true :=
  next_fired (iterate n)

/-- Transport a projection through the two implications supplied by the
checked raw edges, using one boundary-preserving reconstruction. -/
theorem sandwich {Model Public : Type} (agree : Model → Public → Prop)
    (source : Public → Prop) (first middle : Model → Prop)
    (restriction : ∀ m, middle m → first m)
    (source_exact : ∀ p, (∃ m, agree m p ∧ first m) ↔ source p)
    (complete : Public → Model) (fixed : ∀ p, agree (complete p) p)
    (valid : ∀ p, source p → middle (complete p)) (p : Public) :
    (∃ m, agree m p ∧ middle m) ↔ source p := by
  constructor
  · rintro ⟨m,on,held⟩
    exact (source_exact p).mp ⟨m,on,restriction m held⟩
  · intro sourceOK
    exact ⟨complete p,fixed p,valid p sourceOK⟩

end Yulang.GeneralRebaseRoundMicro278
