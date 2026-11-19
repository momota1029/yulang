import Yulang.GeneralRebasePositiveMeaning266
import Yulang.GeneralRebaseCertifiedObserver266

namespace Yulang.GeneralRebaseEdgeRules266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebasePositiveRules266 (Rule)
open GeneralRebasePositiveMeaning266 (Saturated Sound)
open GeneralSourceState (Output)

variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

def rules (owners : List Nat) (pool : List Output) (edges : List (Edge registry root)) : List Rule :=
 edges.flatMap fun edge =>
   (present (project owners pool edge.after)).map fun fact =>
     ⟨present (project owners pool edge.before),fact⟩

theorem member (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 (rule : Rule) :
 rule ∈ rules owners pool edges ↔
 ∃ edge ∈ edges, ∃ fact ∈ present (project owners pool edge.after),
   (⟨present (project owners pool edge.before),fact⟩ : Rule) = rule := by
 simp only [rules,List.mem_flatMap,List.mem_map]

theorem follows (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 (state : State (Basis owners pool)) (saturated : Saturated (rules owners pool edges) state)
 (edge : Edge registry root) (listed : edge ∈ edges)
 (prerequisites : present (project owners pool edge.before) ⊆ present state) :
 present (project owners pool edge.after) ⊆ present state := by
 intro fact produced
 let rule : Rule := ⟨present (project owners pool edge.before),fact⟩
 have inside : rule ∈ rules owners pool edges := (member owners pool edges rule).mpr
    ⟨edge,listed,fact,produced,rfl⟩
 exact saturated rule inside ((GeneralRebaseFactSemantics259.present_iff _ fact).mp produced).1
    (fun _ required => prerequisites required)

/-- The positive rules overapproximate a certified-table run at the level of
present facts; they do not assert that the implications compose concrete
executions or that every rule deduction is a source Step. -/
theorem run_covered (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 {first last : State (Basis owners pool)} {n : Nat}
 (run : Runs (GeneralRebaseCertifiedObserver266.observe owners pool edges) n first last)
 (state : State (Basis owners pool)) (saturated : Saturated (rules owners pool edges) state)
 (start : present first ⊆ present state) :
 present last ⊆ present state := by
 induction run with
 | nil initial => exact start
 | next step _ ih =>
   obtain ⟨edge,listed,starts,ends,_⟩ := (GeneralRebaseCertifiedObserver266.step_exact owners pool edges _ _).mp step
   apply ih
   rw [←ends]
   apply follows owners pool edges state saturated edge listed
   simpa only [starts] using start

/-- Pointwise validity needed for rule-model preservation is exactly the
validity of every projected edge implication, not mere existence of a Step. -/
theorem sound_iff (owners : List Nat) (pool : List Output) (edges : List (Edge registry root))
 (base : α → Prop) (holds : α → Fact → Prop) :
 Sound (rules owners pool edges) base holds ↔
 ∀ assignment, base assignment → ∀ edge ∈ edges,
   (∀ fact ∈ present (project owners pool edge.before), holds assignment fact) →
   ∀ fact ∈ present (project owners pool edge.after), holds assignment fact := by
 constructor
 · intro sound assignment valid edge listed premise fact produced
   let rule : Rule := ⟨present (project owners pool edge.before),fact⟩
   exact sound assignment valid rule ((member owners pool edges rule).mpr ⟨edge,listed,fact,produced,rfl⟩) premise
 · intro edgeValid assignment valid rule inRules satisfies
   obtain ⟨edge,listed,fact,produced,rfl⟩ := (member owners pool edges rule).mp inRules
   exact edgeValid assignment valid edge listed satisfies fact produced

end Yulang.GeneralRebaseEdgeRules266
