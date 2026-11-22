import Yulang.GeneralDeclarativeAlternativeView333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeNeeds333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Offer Index Link Covers CoversRow exact_offer ofTable covers_alias)
open GeneralNominalCenteredHeadMatExpressions (Expr)

abbrev Need (s : State) := (n : Nat) × Offer s n

def Filled (src : Index s) (asked : List (Need s)) : Prop :=
  ∀ link ∈ asked, link.2 ∈ src link.1

/-- A finite packet of existing authority. It can be recovered by
induction from a derivation already present in the independent source
rules; it does not guess a new obligation or obtain a model. -/
def Planned (P : Index s → Prop) : Prop :=
  ∃ dependencies, ∀ src, Filled src dependencies → P src

theorem Planned.pure {P : Index s → Prop} (works : ∀ src, P src) : Planned P :=
  ⟨[],fun src _ => works src⟩

theorem Planned.map {P Q : Index s → Prop} (given : Planned P) (consumes : ∀ src, P src → Q src) : Planned Q := by
  obtain ⟨dependencies,known⟩ := given
  exact ⟨dependencies,fun src inside => consumes src (known src inside)⟩

theorem Planned.both {P Q : Index s → Prop} (one : Planned P) (two : Planned Q) :
    Planned (fun src => P src ∧ Q src) := by
  obtain ⟨a,one⟩ := one
  obtain ⟨b,two⟩ := two
  exact ⟨a++b,fun src filled => ⟨one src (fun e h => filled e (List.mem_append_left _ h)),
    two src (fun e h => filled e (List.mem_append_right _ h))⟩⟩

theorem Planned.add {s : State} {P Q : Index s → Prop} (given : Planned P) (entry : Need s)
    (consumes : ∀ src, entry.2 ∈ src entry.1 → P src → Q src) : Planned Q := by
  obtain ⟨dependencies,known⟩ := given
  refine ⟨entry::dependencies,fun src filled => ?_⟩
  exact consumes src (filled entry List.mem_cons_self)
    (known src (fun e h => filled e (List.mem_cons_of_mem _ h)))

theorem Planned.from_cover {s : State} {src : Index s} {P : Index s → Prop} (given : Planned P) (covers : Covers src) : P src := by
  obtain ⟨dependencies,known⟩ := given
  refine known src (fun e _ => ?_)
  exact exact_offer (covers _ _ _ e.2.linked e.2.stored) e.2.linked e.2.stored

def requiredAliases (asked : List (Need s)) : List (Link s) :=
  asked.map fun e => ⟨e.1,e.2.owner,e.2.linked⟩

def requiredRows (asked : List (Need s)) : List Equation :=
  asked.map fun e => ⟨e.2.owner,e.2.rhs⟩

theorem rows_supported (asked : List (Need s)) :
    requiredRows asked ⊆ s.equations := by
  intro row mem
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp mem
  exact e.2.stored

def finiteIndex (asked : List (Need s)) : Index s :=
  ofTable (requiredRows asked) (rows_supported asked) (requiredAliases asked)

theorem fulfilled (asked : List (Need s)) : Filled (finiteIndex asked) asked := by
  intro e listed
  let route : Link s := ⟨e.1,e.2.owner,e.2.linked⟩
  have routeSeen : route ∈ requiredAliases asked := List.mem_map.mpr ⟨e,listed,rfl⟩
  have rowSeen : (⟨e.2.owner,e.2.rhs⟩ : Equation) ∈ requiredRows asked :=
    List.mem_map.mpr ⟨e,listed,rfl⟩
  exact exact_offer (covers_alias (valid := rows_supported asked) routeSeen rfl rfl rowSeen)
    e.2.linked e.2.stored

theorem Planned.finite {s : State} {P : Index s → Prop} (given : Planned P) :
    ∃ dependencies, P (finiteIndex dependencies) := by
  obtain ⟨dependencies,run⟩ := given
  exact ⟨dependencies,run _ (fulfilled dependencies)⟩

def Eventually (P : Nat → Prop) : Prop :=
  ∃ least, ∀ fuel ≥ least, P fuel

theorem eventually_one {P : Nat → Prop} (h : ∀ n, P (n+1)) : Eventually P :=
  ⟨1,fun n ok => by
    cases n with
    | zero => cases ok
    | succ n => exact h n⟩

theorem eventually_step {P Q : Nat → Prop} (a : Eventually P) (h : ∀ n, P n → Q (n+1)) :
    Eventually Q := by
  obtain ⟨m,done⟩ := a
  exact ⟨m+1,fun n ok => by
    cases n with
    | zero => cases ok
    | succ n => exact h n (done n (Nat.le_of_succ_le_succ ok))⟩

theorem eventually_pair {P Q : Nat → Prop} (a : Eventually P) (b : Eventually Q) :
    Eventually (fun n => P n ∧ Q n) := by
  obtain ⟨m,hm⟩ := a
  obtain ⟨n,hn⟩ := b
  exact ⟨max m n,fun f ok => ⟨hm f (Nat.le_trans (Nat.le_max_left ..) ok),
    hn f (Nat.le_trans (Nat.le_max_right ..) ok)⟩⟩

end Yulang.GeneralDeclarativeAlternativeNeeds333
