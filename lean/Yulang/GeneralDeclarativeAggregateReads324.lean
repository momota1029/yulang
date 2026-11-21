import Yulang.GeneralDeclarativeAggregateFixture324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregateReads324
open GeneralDeclarativeAggregateFixture324
open GeneralDeclarativeRepeatedSource323 (state a b eqs nominalCode scalar pat goal parent child registry whereClause model fits checked)
open GeneralDeclarativeRepeatedReads323 (scanned observed parentNames place parent_reads)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeNFWhere324 (clauseFacts)
open GeneralDeclarativeNFComplete324 (ReadBack local_sound facts produces)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeRigidSource323 (ordered_results)
open GeneralDeclarativeSemanticSharing323 (exact_shared)
open GeneralDeclarativeNormalized320 (ordered_map)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)

abbrev childNames : Names := ⟨fun _ => merged,fun _ => 3⟩

theorem a_bounds : Bounds newState a := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩
theorem b_bounds : Bounds newState b := ⟨.interval (by decide +kernel),.interval (by decide +kernel)⟩

theorem old_upper_head (arg : GeneralDeclarativeWhere319.Capture) :
    fact registry.constructors interp actualNames.input arg pat =
    GeneralDeclarativeArgumentFacts320.headFact registry.constructors interp parentNames.input arg pat := rfl

theorem actual_head :
    All₂ (fun arg p => Bounds newState arg ∧ Result newState (fact registry.constructors interp actualNames.input arg p))
      goal.arguments parent.head := by
  obtain ⟨obs,read,known,shared⟩ := parent_reads.seen
  have prev := ordered_results read ((exact_shared read known).mpr shared)
  apply ordered_map prev
  rintro arg member p head ⟨rows,compiled,ordinary⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at head
  rcases head with rfl|rfl
  all_goals
    refine ⟨?_,⟨rows,(old_upper_head arg).trans compiled,fun row found m valid =>
      ordinary row found m (current_old m valid)⟩⟩
    rcases List.mem_cons.mp member with rfl|later
    · exact a_bounds
    · cases List.mem_singleton.mp later
      exact b_bounds

theorem root_reads : ReadBack newState registry interp goal parent actualNames place := by
  refine ⟨actual_head,fun _ _ => bounds,fun _ impossible => False.elim (List.not_mem_nil impossible),?_⟩
  intro clause used
  cases List.mem_singleton.mp used
  refine ⟨⟨[.variable 0],.cons rfl .nil,?_⟩,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  intro idx p expr found printed compound
  cases List.mem_singleton.mp (List.mem_of_getElem? found)
  exact False.elim (compound 0 rfl)

theorem child_reads : ReadBack newState registry interp emitted child childNames place := by
  refine ⟨.cons ⟨bounds,?_⟩ .nil,fun _ _ => bounds,
    fun _ impossible => False.elim (List.not_mem_nil impossible),fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  refine ⟨[⟨3,.variable 3⟩],rfl,?_⟩
  intro row present m valid
  cases List.mem_singleton.mp present
  exact eqv_refl _

theorem root_meaning (m : Assignment) (good : Models newState m) :
    Meaning registry interp m goal parent actualNames.input [emitted] := by
  rw [← exact_child]
  refine local_sound checked List.mem_cons_self rfl (fun _ never => False.elim (List.not_mem_nil never))
    (fun _ never => False.elim (List.not_mem_nil never)) root_reads ?_ m good
  rintro row ⟨out,never,_⟩
  cases never

theorem child_meaning (m : Assignment) (good : Models newState m) :
    Meaning registry interp m emitted child childNames.input [] := by
  refine local_sound checked (List.mem_cons_of_mem _ List.mem_cons_self) rfl
    (fun _ never => False.elim (List.not_mem_nil never))
    (fun _ never => False.elim (List.not_mem_nil never)) child_reads ?_ m good
  rintro row ⟨out,never,_⟩
  cases never

abbrev dict : Dictionary := .node parent.id [.node child.id []]

theorem every_new_model (m : Assignment) (good : Models newState m) : Evidence registry interp m goal dict :=
  .node ⟨parent,actualNames.input,rfl,root_meaning m good⟩
    (.cons (.node ⟨child,childNames.input,rfl,child_meaning m good⟩ .nil) .nil)

end Yulang.GeneralDeclarativeAggregateReads324
