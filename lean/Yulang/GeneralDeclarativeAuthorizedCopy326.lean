import Yulang.GeneralDeclarativeCovariantSupport326
import Yulang.GeneralDeclarativeNewNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAuthorizedCopy326
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeLowerKnown321 (Knows Alias alias_mono constructorTag)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeNewNames321 (after supply old_plus_extra)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def name (s : State) (source : Nat) (keep : List Nat) :=
  after ((stateNames s ++ keep) ++ [source])

def writing (s : State) (source : Nat) (keep : List Nat) : Equation :=
  ⟨name s source keep,.variable source⟩

def extended (s : State) (source : Nat) (keep : List Nat) : State :=
  appendFacts s [writing s source keep]

/-- A projected lower alias inherits any *actual* backed constructor
origin for its source. An ordinary-only equation, a shape inferred in
one model, or a center projection alone supplies no such authority. -/
def copy {s : State} (p : Supported s complete) (source : Nat) (keep : List Nat) :
    Supported (extended s source keep) complete :=
  ⟨fun e origin => p.derivesFrom e origin ∨ e = writing s source keep ∧
    ∃ authored, p.derivesFrom authored origin ∧ Alias (restriction p) source authored.left ∧
      ∃ tag, constructorTag authored.right = some tag,by
        intro e origin provided
        rcases provided with old|⟨rfl,_⟩
        · exact List.mem_append_left _ (p.ordinary old)
        · exact List.mem_append_right _ List.mem_cons_self⟩

theorem retained {s : State} (p : Supported s complete) (source : Nat) (keep : List Nat) :
    (restriction p).equations ⊆ (restriction (copy p source keep)).equations := by
  intro e existed
  obtain ⟨origin,written,available⟩ := (backed_iff p e).mp existed
  exact (backed_iff ..).mpr ⟨origin,.inl written,available⟩

theorem authorized {s : State} (p : Supported s complete) (source : Nat) (keep : List Nat)
    (known : Knows (restriction p) source tag) :
    Knows (restriction (copy p source keep)) (name s source keep) tag := by
  obtain ⟨old,listed,alias,kind⟩ := known
  obtain ⟨origin,originYes,available⟩ := (backed_iff p old).mp listed
  have written : writing s source keep ∈ (restriction (copy p source keep)).equations :=
    (backed_iff ..).mpr ⟨origin,.inr ⟨rfl,old,originYes,alias,tag,kind⟩,available⟩
  have knownAlias := alias_mono (s := restriction p) (t := restriction (copy p source keep)) rfl
    (retained p source keep) alias
  exact ⟨old,retained p source keep listed,.trans (.forward written) knownAlias,kind⟩

/-- The new alias cannot originate from another source if its chosen
operand has no authorized head. An identically written old row would
need a separate existing origin (fresh naming rules it out in use). -/
theorem no_new_origin {s : State} (p : Supported s complete) (source : Nat) (keep : List Nat)
    (never : ∀ tag, ¬Knows (restriction p) source tag)
    (absent : writing s source keep ∉ s.equations) :
    writing s source keep ∉ (restriction (copy p source keep)).equations := by
  intro yes
  obtain ⟨origin,declared,available⟩ := (backed_iff ..).mp yes
  rcases declared with old|new
  · exact absent (p.ordinary old)
  · obtain ⟨_,own,prior,located,tag,kind⟩ := new
    have backed := (backed_iff p own).mpr ⟨origin,prior,available⟩
    exact never tag ⟨own,backed,located,kind⟩

theorem fresh {s : State} (source : Nat) (keep : List Nat) : writing s source keep ∉ s.equations := by
  intro old
  have present : name s source keep ∈ stateNames s := by
    apply List.mem_append_right _
    exact List.mem_flatMap.mpr ⟨writing s source keep,old,List.mem_cons_self⟩
  exact (Nat.lt_irrefl _) (GeneralDeclarativeNewNames321.before_after
    (List.mem_append_left _ (List.mem_append_left _ present)))

theorem conservative {s : State} (source : Nat) (keep : List Nat) (m)
    (old : Models s m) :
    ∃ later, Models (extended s source keep) later ∧
      ∀ n ∈ stateNames s ++ keep, later n = m n := by
  obtain ⟨valid,kept⟩ := old_plus_extra s keep [.variable source] m old
  exact ⟨_,valid,kept⟩

end Yulang.GeneralDeclarativeAuthorizedCopy326
