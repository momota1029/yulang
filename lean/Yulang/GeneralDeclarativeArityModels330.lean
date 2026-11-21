import Yulang.GeneralDeclarativeArityResult330
import Yulang.GeneralDeclarativeStableModels329

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16500
set_option maxHeartbeats 11000000
namespace Yulang.GeneralDeclarativeArityModels330
open GeneralDeclarativeArityFixture330 (initial prepared tied final pairRow oldRows inputRows tie spans base frame child)
open GeneralDeclarativeArityProbe330 (table)
open GeneralDeclarativeArityResult330 (dict every_model declared)
open GeneralDeclarativeRepeatDecl327 (reg root impl checked)
open GeneralDeclarativeArityFixture330 (interp coverage)
open GeneralDeclarativeStableCompiler329 (read)
open GeneralDeclarativeStableTies329 (rows pairOf model_batch)
open GeneralDeclarativeRepeat320 (int)
open GeneralDeclarativeNestedModels328 (boolType payload_gt_int)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent nominal Subtype common_inter_is_meet common_union_is_join subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)

def shape (b : Ty) := nominal 5 [.inl int,.inl b]
def hidden (b : Ty) : Ty := .inter (shape b) .top
abbrev childValue := nominal 0 [.inl int]

def assignment (b : Ty) : Assignment := fun n =>
  (if n = 1 then hidden b else if n = 0 ∨ n = 2 then shape b else
    if n = 4 ∨ n = 8 then b else if n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 11 then childValue
    else int, Common.rowEmpty)

theorem hidden_same (b : Ty) : Equivalent (hidden b) (shape b) :=
  ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
    (common_inter_is_meet ..).mpr ⟨subtype_refl _,GeneralNominalTopObservation.le_top _⟩⟩

theorem old (b : Ty) : Models prepared (assignment b) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro span found
    change _ ∈ [(0,1),(1,2)] at found
    rcases List.mem_cons.mp found with rfl|tail
    · exact (hidden_same b).2
    · cases List.mem_singleton.mp tail
      exact (hidden_same b).1
  · intro eq found
    change _ ∈ oldRows ++ [pairRow] at found
    simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with h|h|h|h <;> cases h
    all_goals first | exact eqv_refl _ | exact hidden_same _

theorem stable : Models final (assignment int) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro span found
    change _ ∈ [(0,1),(1,2),(9,10),(10,11)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with h|h|h|h <;> cases h
    · exact (hidden_same _).2
    · exact (hidden_same _).1
    · exact subtype_refl _
    · exact subtype_refl _
  · intro eq found
    rw [table] at found
    simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with h|h|h|h|h|h|h|h|h|h <;> cases h
    all_goals first | exact eqv_refl _ | exact hidden_same _

theorem excluded : ¬Models tied (assignment boolType) := by
  intro yes
  have checked : Subtype boolType int :=
    (((model_batch (s := prepared) base (spans.map pairOf) _).mp yes).2 (0,4)
      (List.mem_cons_of_mem _ List.mem_cons_self)).1
  exact payload_gt_int ((common_union_is_join ..).mpr ⟨subtype_refl _,checked⟩)

theorem exact_compiler :
    GeneralDeclarativeCompileLists321.Result final
      (GeneralDeclarativeNFComplete324.facts reg interp frame.capture impl root [child]) :=
  (read checked coverage List.mem_cons_self rfl declared frame).1

/-- The raw center has no ordinary row before projection; the two
actual invariant parameters are distinct logical occurrences. I-58
writes their equality, removes a real earlier model and still admits
a concrete successful dictionary model at the fixed output target. -/
theorem nonvacuous :
    (¬∃ rhs, (⟨1,rhs⟩ : Equation) ∈ initial.equations) ∧
    Models prepared (assignment boolType) ∧ ¬Models tied (assignment boolType) ∧
    Models final (assignment int) ∧ Evidence reg interp (assignment int) root dict := by
  refine ⟨?_,old _,excluded,stable,every_model _ stable⟩
  rintro ⟨rhs,there⟩
  simp only [oldRows,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with h|h|h <;> cases congrArg Equation.left h

end Yulang.GeneralDeclarativeArityModels330
