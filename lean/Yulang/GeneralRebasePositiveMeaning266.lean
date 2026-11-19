import Yulang.GeneralRebasePositiveRules266

namespace Yulang.GeneralRebasePositiveMeaning266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebasePositiveRules266 (Rule observe enabled_exact membership)
open GeneralRebasePersistentObserver266 (Terminal Refines)
open GeneralRebaseSettle259 (settle)
open GeneralRebaseFactSemantics259 (Models present_iff)
variable {basis : List Fact}

def Saturated (rules : List Rule) (state : State basis) : Prop :=
 ∀ rule ∈ rules, rule.produces ∈ basis →
 (∀ fact ∈ rule.requires, fact ∈ present state) → rule.produces ∈ present state

theorem terminal_iff (rules : List Rule) (state : State basis) :
 Terminal (observe rules) state ↔ Saturated rules state := by
 constructor
 · intro terminal rule listed inside prerequisites
   by_cases pending : rule.produces ∈ state.remaining
   · have fired := (enabled_exact state rule).mpr ⟨pending, prerequisites⟩
     have admitted : [rule.produces] ∈ observe rules state :=
       (membership rules state _).mpr ⟨rule,listed,fired,rfl⟩
     exact False.elim (GeneralRebasePersistentObserver266.terminal_excludes _
       state terminal [rule.produces] admitted rule.produces pending (List.mem_singleton_self _))
   · exact (present_iff state _).mpr ⟨inside,pending⟩
 · intro saturated after step
   obtain ⟨proposed,listed,_,_⟩ := step
   obtain ⟨rule,ruleListed,fired,_⟩ := (membership rules state proposed).mp listed
   obtain ⟨pending,prerequisites⟩ := (enabled_exact state rule).mp fired
   have known := saturated rule ruleListed (state.canonical.subset pending) prerequisites
   exact ((present_iff state rule.produces).mp known).2 pending

/-- Every checked scheduler result is the least rule-closed state above the
start in the sublist refinement order, independently of rule order. -/
theorem least_saturated (rules : List Rule) (start : State basis) :
 ∃ final, settle (observe rules) start = .ok final ∧ Refines start final ∧
   Saturated rules final ∧ ∀ bound, Refines start bound → Saturated rules bound → Refines final bound := by
 obtain ⟨final,_,result,path,_,quiet⟩ := GeneralRebaseClosedObserver259.completion
   (observe rules) (GeneralRebasePositiveRules266.closed rules) start
 refine ⟨final,result,GeneralRebasePersistentObserver266.runs_refine _ path,
   (terminal_iff rules final).mp quiet,?_⟩
 intro bound increased saturated
 exact GeneralRebasePersistentObserver266.settle_minimal _ (GeneralRebasePositiveRules266.persistent rules)
   result increased ((terminal_iff rules bound).mpr saturated)

def Sound (rules : List Rule) (base : α → Prop) (holds : α → Fact → Prop) : Prop :=
 ∀ assignment, base assignment → ∀ rule ∈ rules,
   (∀ fact ∈ rule.requires, holds assignment fact) → holds assignment rule.produces

/-- This is rule-interpretation soundness, not a decision procedure for a
source model. The caller supplies the validity of every rule. -/
theorem sound_step (rules : List Rule) (base : α → Prop) (holds : α → Fact → Prop)
 (sound : Sound rules base holds) {before after : State basis}
 (step : Step (observe rules) before after) (assignment : α) :
 Models base holds after assignment ↔ Models base holds before assignment := by
 obtain ⟨proposed,listed,rfl,_⟩ := step
 obtain ⟨rule,ruleListed,fired,rfl⟩ := (membership rules before proposed).mp listed
 obtain ⟨_,prerequisites⟩ := (enabled_exact before rule).mp fired
 rw [GeneralRebaseFactSemantics259.write_exact]
 constructor
 · intro updated
   exact updated.1
 · intro valid
   refine ⟨valid,?_⟩
   intro fact _ inProposal
   cases List.mem_singleton.mp inProposal
   exact sound assignment valid.1 rule ruleListed (fun f required => valid.2 f (prerequisites f required))

theorem sound_runs (rules : List Rule) (base : α → Prop) (holds : α → Fact → Prop)
 (sound : Sound rules base holds) {before after : State basis} {n : Nat}
 (path : Runs (observe rules) n before after) (assignment : α) :
 Models base holds after assignment ↔ Models base holds before assignment := by
 induction path with
 | nil state => exact Iff.rfl
 | next step _ ih => exact ih.trans (sound_step rules base holds sound step assignment)

theorem sound_settle (rules : List Rule) (base : α → Prop) (holds : α → Fact → Prop)
 (sound : Sound rules base holds) {before after : State basis}
 (success : settle (observe rules) before = .ok after) (assignment : α) :
 Models base holds after assignment ↔ Models base holds before assignment := by
 obtain ⟨_,run⟩ := GeneralRebaseSettle259.successful_path _ _ _ success
 exact sound_runs rules base holds sound run assignment

end Yulang.GeneralRebasePositiveMeaning266
