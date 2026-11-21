import Yulang.GeneralDeclarativeSourceSelection325
import Yulang.GeneralDeclarativeHiddenStageReads324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceFixture325
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeHiddenStages324 (Stage parent_observed candidate no_recurs root_ready' leaf_ready' tested_root tested_leaf)
open GeneralDeclarativeHiddenResolve324 (root_only child_only dictionary)
open GeneralDeclarativeHiddenReads324 (declared_root)
open GeneralDeclarativeExampleSource320 (point leaf)
open GeneralDeclarationExamples (containerChild itemEquation)
open GeneralDeclarativeFrameReadback325 (Frame Recorded sourceNames)
open GeneralDeclarativeSourceSelection325 (Rule Source sound)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify All₂)

def base (_ : Nat) : GeneralDeclarativeWhere319.Capture := point 3
def placement : Placement :=
  ⟨fun _ _ => point 400,fun cl eq => if cl.id = containerChild.id ∧ eq = itemEquation.id then 5 else 401⟩

theorem exact_output : (sourceNames parent placement base).output 1 = 5 := rfl
theorem root_emits : children parent (sourceNames parent placement base) placement = [child] := rfl
theorem leaf_emits : children leaf (sourceNames leaf placement base) placement = [] := rfl

theorem root_frame (phase : Stage) (done : Nat → Prop) :
    Frame phase.ordinary registry interpretation (phase.equations done) root parent base placement := by
  refine ⟨.cons ⟨root_bounds _ _,.actual normal_compiles (parent_observed phase done .actual) ?_⟩ .nil,
    fun _ _ => root_bounds _ 3,?_⟩
  · intro item present
    cases List.mem_singleton.mp present
    exact .refl _
  · intro cl present
    cases List.mem_singleton.mp present
    constructor
    · refine ⟨[.variable 0],rfl,?_⟩
      intro i p code found _ compound
      cases List.mem_singleton.mp (List.mem_of_getElem? found)
      exact False.elim (compound 0 rfl)
    · intro eq present
      cases List.mem_singleton.mp present
      exact ⟨.variable 1,rfl,fun needed => False.elim (needed ⟨1,rfl,List.mem_cons_self⟩)⟩

theorem child_frame (phase : Stage) (done : Nat → Prop) :
    Frame phase.ordinary registry interpretation (phase.equations done) child leaf base placement := by
  refine ⟨.cons ⟨root_bounds _ _,.actual rfl .capture ?_⟩ .nil,
    fun _ _ => root_bounds _ 3,fun _ h => False.elim (List.not_mem_nil h)⟩
  intro o present
  cases List.mem_singleton.mp present
  exact .refl _

theorem parent_recorded (done : Nat → Prop) :
    Recorded final registry interpretation (support done) root parent base placement :=
  ⟨root_frame .bothWritten done,[parentRow],rfl,fun row present => by
    cases List.mem_singleton.mp present
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)⟩

theorem child_recorded (done : Nat → Prop) :
    Recorded final registry interpretation (support done) child leaf base placement :=
  ⟨child_frame .bothWritten done,[childRow],rfl,fun row present => by
    cases List.mem_singleton.mp present
    exact List.mem_append_right _ List.mem_cons_self⟩

/-- The same approved source wins provisionally before the ordinary
update. Its initial frame is not yet in this stable recorded slice. -/
theorem early_frame_but_unrecorded (done : Nat → Prop) :
    Frame initial registry interpretation (sourceSupport done) root parent base placement ∧
      ¬Recorded initial registry interpretation (sourceSupport done) root parent base placement := by
  refine ⟨root_frame .initial done,?_⟩
  intro source
  obtain ⟨rows,built,written⟩ := source.written
  have out : some [parentRow] = some rows := built
  cases (Option.some.inj out).symm
  have conflict := written (show parentRow ∈ [parentRow] from List.mem_cons_self)
  simp only [initial,s0Rows,List.mem_cons,List.not_mem_nil,or_false] at conflict
  rcases conflict with h|h|h|h <;> have bad := congrArg Equation.left h <;> cases bad

abbrev stableRule (done : Nat → Prop) := Rule final registry interpretation (support done) (candidate .bothWritten done)

theorem chooses_root (done : Nat → Prop) : stableRule done root (.selected parent.id [child]) := by
  refine .selected (root_ready' .bothWritten done) (no_recurs .bothWritten done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,tested_root .bothWritten done⟩ ?_
    ⟨base,placement,parent_recorded done,root_emits⟩
  · rintro ⟨d,⟨vis,role⟩,unknown⟩
    cases root_only d vis role
    exact unknown (tested_root .bothWritten done)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [root_only d vis role]

theorem chooses_child (done : Nat → Prop) : stableRule done child (.selected leaf.id []) := by
  refine .selected (leaf_ready' .bothWritten done) (no_recurs .bothWritten done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,tested_leaf .bothWritten done⟩ ?_
    ⟨base,placement,child_recorded done,leaf_emits⟩
  · rintro ⟨d,⟨vis,role⟩,unknown⟩
    cases child_only d vis role
    exact unknown (tested_leaf .bothWritten done)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [child_only d vis role]

theorem whole_selection (done : Nat → Prop) : Classify (stableRule done) root (.selected dictionary) :=
  ⟨.selected parent.id [.selected leaf.id []],
    .selected (chooses_root done) (.cons (.selected (chooses_child done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem whole_evidence (m) (valid : Models final m) : Evidence registry interpretation m root dictionary :=
  sound checked declared_root valid (whole_selection (fun _ => False))

theorem inhabited : ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary :=
  ⟨assignment true,fits_final,whole_evidence _ fits_final⟩

end Yulang.GeneralDeclarativeSourceFixture325
