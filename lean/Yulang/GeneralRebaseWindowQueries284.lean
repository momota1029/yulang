import Yulang.GeneralRebaseVersionPortRead284
import Yulang.GeneralRebaseLoosePortRead284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWindowQueries284
open GeneralRebaseEpochWindow284 (Window)
open GeneralRebaseWindowPorts284 (Port read)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype)
open CommonRoleOutermostResolver (All₂)

def resolve (upper : Nat) (window : Window) : List Port → Option (List Nat)
  | [] => some []
  | p :: rest => do
    let head ← read upper window p
    let tail ← resolve upper window rest
    return head :: tail

theorem aligned (u : Nat) (w : Window) (ports : List Port) (names : List Nat)
    (found : resolve u w ports = some names) :
    All₂ (fun p k => read u w p = some k) ports names := by
  induction ports generalizing names with
  | nil =>
    have same : [] = names := Option.some.inj found
    subst names; exact .nil
  | cons port tail ih =>
    cases first : read u w port with
    | none => simp [resolve,first] at found
    | some k =>
      cases later : resolve u w tail with
      | none => simp [resolve,first,later] at found
      | some ks =>
        have eq : k :: ks = names := by simpa [resolve,first,later] using found
        subst names; exact .cons first (ih _ later)

theorem collect {α β : Type} {as : List α} {bs : List β} {R : α → β → Prop}
    (linked : All₂ R as bs) (f : α → Ty) (g : β → Ty)
    (sound : ∀ a b, R a b → Equivalent (f a) (g b)) :
    All₂ Equivalent (as.map f) (bs.map g) := by
  induction linked with
  | nil => exact .nil
  | cons left rest ih => exact .cons (sound _ _ left) ih

def Invariant (goal : List Ty → Prop) : Prop :=
  ∀ a b, All₂ Equivalent a b → (goal a ↔ goal b)

theorem query_exists {Full Public : Assignment → Prop} {ports : List Port}
    {w : Window} {u : Nat} {names : List Nat} {represent : Port → Nat}
    (resolved : resolve u w ports = some names)
    (restr : ∀ a, Full a → Public a)
    (complete : ∀ base, Public base → ∃ a, Full a ∧ ∀ k ∈ names, a k = base k)
    (direct : ∀ a, Full a → ∀ p k, read u w p = some k → Equivalent (a (represent p)).1 (a k).1)
    (goal : List Ty → Prop) (safe : Invariant goal) :
    (∃ m, Full m ∧ goal (ports.map (fun p => (m (represent p)).1))) ↔
    (∃ base, Public base ∧ goal (names.map (fun k => (base k).1))) := by
  have zipped := aligned u w ports names resolved
  constructor
  · rintro ⟨m,valid,yes⟩
    exact ⟨m,restr m valid,(safe _ _ (collect zipped _ _ (direct m valid))).mp yes⟩
  · rintro ⟨base,valid,yes⟩
    obtain ⟨m,good,keeps⟩ := complete base valid
    have same : names.map (fun k => (m k).1) = names.map (fun k => (base k).1) := by
      apply List.map_congr_left
      intro k member; exact congrArg Prod.fst (keeps k member)
    rw [← same] at yes
    exact ⟨m,good,(safe _ _ (collect zipped _ _ (direct m good))).mpr yes⟩

theorem invariant_not {goal : List Ty → Prop} (safe : Invariant goal) : Invariant (fun data => ¬ goal data) :=
  fun a b same => not_congr (safe a b same)

theorem query_all {Full Public : Assignment → Prop} {ports : List Port}
    {w : Window} {u : Nat} {names : List Nat} {represent : Port → Nat}
    (resolved : resolve u w ports = some names)
    (restr : ∀ a, Full a → Public a)
    (complete : ∀ base, Public base → ∃ a, Full a ∧ ∀ k ∈ names, a k = base k)
    (direct : ∀ a, Full a → ∀ p k, read u w p = some k → Equivalent (a (represent p)).1 (a k).1)
    (goal : List Ty → Prop) (safe : Invariant goal) :
    (∀ m, Full m → goal (ports.map (fun p => (m (represent p)).1))) ↔
    (∀ base, Public base → goal (names.map (fun k => (base k).1))) := by
  have existential := query_exists resolved restr complete direct _ (invariant_not safe)
  classical
  simpa only [not_exists,not_and,Classical.not_not] using not_congr existential


theorem names_used {u : Nat} {w : Window} {ports : List Port} {names : List Nat}
    (found : resolve u w ports = some names) (name : Nat) (member : name ∈ names) :
    ∃ p ∈ ports, read u w p = some name := by
  have equiv := aligned u w ports names found
  clear found
  induction equiv with
  | nil => cases member
  | @cons p n ps ns hp rest ih =>
    rcases List.mem_cons.mp member with rfl|atTail
    · exact ⟨p,List.mem_cons_self,hp⟩
    · obtain ⟨q,qUsed,read⟩ := ih atTail
      exact ⟨q,List.mem_cons_of_mem _ qUsed,read⟩

end Yulang.GeneralRebaseWindowQueries284
