import Yulang.GeneralRebasePersistentJoin266

namespace Yulang.GeneralRebasePositiveRules266
open GeneralRebaseStep258
open GeneralRebasePersistentObserver266 (Persistent Refines)
open GeneralRebaseSettle259 (settle)
variable {basis : List Fact}

structure Rule where
 requires : List Fact
 produces : Fact

def enabled (state : State basis) (rule : Rule) : Bool :=
 state.remaining.contains rule.produces &&
 rule.requires.all (fun fact => (present state).contains fact)

def observe (rules : List Rule) : Observer basis :=
 fun state => (rules.filter (enabled state)).map fun rule => [rule.produces]

theorem enabled_exact (state : State basis) (rule : Rule) :
 enabled state rule = true ↔ rule.produces ∈ state.remaining ∧
   ∀ fact ∈ rule.requires, fact ∈ present state := by
 simp [enabled]

theorem membership (rules : List Rule) (state : State basis) (proposal : Proposal) :
 proposal ∈ observe rules state ↔
 ∃ rule ∈ rules, enabled state rule = true ∧ [rule.produces] = proposal := by
 simp only [observe,List.mem_map,List.mem_filter]
 constructor
 · rintro ⟨rule,⟨listed,fires⟩,result⟩
   exact ⟨rule,listed,fires,result⟩
 · rintro ⟨rule,listed,fires,result⟩
   exact ⟨rule,⟨listed,fires⟩,result⟩

theorem known_monotone {before after : State basis} (sub : Refines before after)
 (fact : Fact) (known : fact ∈ present before) : fact ∈ present after := by
 obtain ⟨pool,notPending⟩ := (GeneralRebaseFactSemantics259.present_iff before fact).mp known
 exact (GeneralRebaseFactSemantics259.present_iff after fact).mpr
   ⟨pool,fun pending => notPending (sub.subset pending)⟩

theorem closed (rules : List Rule) : GeneralRebaseClosedObserver259.Closed (observe (basis := basis) rules) := by
 intro state proposed listed fact member
 obtain ⟨rule,_,fired,rfl⟩ := (membership rules state proposed).mp listed
 cases List.mem_singleton.mp member
 exact state.canonical.subset ((enabled_exact state rule).mp fired).1

theorem persistent (rules : List Rule) : Persistent (observe (basis := basis) rules) := by
 intro before after sub proposal listed fact cond pending
 obtain ⟨rule,member,fired,rfl⟩ := (membership rules before proposal).mp listed
 cases List.mem_singleton.mp cond
 have later : enabled after rule = true := (enabled_exact after rule).mpr
   ⟨pending,fun fact req => known_monotone sub fact (((enabled_exact before rule).mp fired).2 fact req)⟩
 exact ⟨[rule.produces],(membership rules after _).mpr ⟨rule,member,later,rfl⟩,List.mem_singleton_self _⟩

theorem same_steps (one two : List Rule) (same : ∀ rule, rule ∈ one ↔ rule ∈ two)
 (first last : State basis) : Step (observe one) first last ↔ Step (observe two) first last := by
 have admitted (proposal : Proposal) : proposal ∈ observe one first ↔ proposal ∈ observe two first := by
   rw [membership,membership]
   constructor
   · rintro ⟨rule,listed,fires,exactProposal⟩
     exact ⟨rule,(same rule).mp listed,fires,exactProposal⟩
   · rintro ⟨rule,listed,fires,exactProposal⟩
     exact ⟨rule,(same rule).mpr listed,fires,exactProposal⟩
 constructor
 · rintro ⟨proposal,member,square,different⟩
   exact ⟨proposal,(admitted proposal).mp member,square,different⟩
 · rintro ⟨proposal,member,square,different⟩
   exact ⟨proposal,(admitted proposal).mpr member,square,different⟩

theorem order_independent (one two : List Rule) (same : ∀ rule, rule ∈ one ↔ rule ∈ two)
 (start : State basis) : settle (observe one) start = settle (observe two) start :=
 GeneralRebasePersistentJoin266.settle_same_relation _ _ (closed one) (closed two)
   (persistent one) (same_steps one two same) start

end Yulang.GeneralRebasePositiveRules266
