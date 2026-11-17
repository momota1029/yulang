import Yulang.GeneralNominalRebaseScheduler242
/-! Finite scheduler runs compute the same least closed fact set when discovery
is monotone. This is an order law for the explicit fact engine, not a proof that
all language operations are expressible in its finite domain. -/
namespace Yulang.GeneralNominalRebaseSchedulerOrder242
open GeneralNominalRebaseScheduler242
open GeneralNominalRebaseStore241 (Owner Block)
variable {factCount ownerCount : Nat}
variable {ownerAt : Fin ownerCount → Owner}
variable {compile : Facts factCount → Fin ownerCount → Block}
variable {discover : Facts factCount → Facts factCount}
def Included (first last : Facts factCount) : Prop := ∀ index, first index = true → last index = true
def Monotone (discover : Facts factCount → Facts factCount) : Prop :=
 ∀ first last, Included first last → Included (discover first) (discover last)
def ClosedFacts (discover : Facts factCount → Facts factCount) (facts : Facts factCount) : Prop :=
 Included (discover facts) facts
variable {before after : State factCount ownerCount}

theorem step_included (action : Step ownerAt compile discover before after) : Included before.work.facts after.work.facts := by
 cases action with
 | learn novel => intro index held; simp only [refresh,GeneralNominalRebaseMachine241.learn,held,Bool.true_or]
 | service index pending => exact fun _ held => held

theorem trace_included (path : B4Target.Steps (Step ownerAt compile discover) before after) :
 Included before.work.facts after.work.facts := by
 induction path with
 | refl => exact fun _ held => held
 | tail path action ih => exact fun index held => step_included action index (ih index held)

theorem step_below (monotone : Monotone discover) (closed : ClosedFacts discover bound)
 (below : Included before.work.facts bound) (action : Step ownerAt compile discover before after) :
 Included after.work.facts bound := by
 cases action with
 | learn novel =>
   intro index held
   change (before.work.facts index || discover before.work.facts index) = true at held
   have alternatives : before.work.facts index = true ∨ discover before.work.facts index = true := by simpa using held
   rcases alternatives with old | new
   · exact below index old
   · exact closed index (monotone _ _ below index new)
 | service index pending => exact below

theorem trace_below (monotone : Monotone discover) (closed : ClosedFacts discover bound)
 (below : Included before.work.facts bound) (path : B4Target.Steps (Step ownerAt compile discover) before after) :
 Included after.work.facts bound := by
 induction path with
 | refl => exact below
 | tail path action ih => exact step_below monotone closed ih action

theorem least (monotone : Monotone discover) (path : B4Target.Steps (Step ownerAt compile discover) before after)
 (closed : Closed discover after) :
 Included before.work.facts after.work.facts ∧ ClosedFacts discover after.work.facts ∧
 ∀ bound, Included before.work.facts bound → ClosedFacts discover bound → Included after.work.facts bound :=
 ⟨trace_included path,closed,fun _ below closed => trace_below monotone closed below path⟩

theorem facts_unique (monotone : Monotone discover)
 (one : B4Target.Steps (Step ownerAt compile discover) before first)
 (two : B4Target.Steps (Step ownerAt compile discover) before last)
 (firstClosed : Closed discover first) (lastClosed : Closed discover last) : first.work.facts = last.work.facts := by
 have forward := trace_below monotone lastClosed (trace_included two) one
 have backward := trace_below monotone firstClosed (trace_included one) two
 funext index
 cases a : first.work.facts index <;> cases b : last.work.facts index
 · rfl
 · have contradiction := backward index b; rw [a] at contradiction; cases contradiction
 · have contradiction := forward index a; rw [b] at contradiction; cases contradiction
 · rfl

theorem tables_unique (injective : Function.Injective ownerAt) (monotone : Monotone discover)
 (known : Consistent ownerAt compile before)
 (one : B4Target.Steps (Step ownerAt compile discover) before first)
 (two : B4Target.Steps (Step ownerAt compile discover) before last)
 (firstClean : Clean first) (lastClean : Clean last)
 (firstClosed : Closed discover first) (lastClosed : Closed discover last) :
 ∀ index, first.table.blocks (ownerAt index) = last.table.blocks (ownerAt index) := by
 intro index
 rw [clean_table (trace_consistent injective known one) firstClean index,
     clean_table (trace_consistent injective known two) lastClean index,
     facts_unique monotone one two firstClosed lastClosed]
end Yulang.GeneralNominalRebaseSchedulerOrder242
