import Yulang.GeneralDepthTwoEvidence300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralDepthTwoFinalNodes300
open GeneralGeneratedNestedSource299 (root model)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoTerminalFrame300 (final_model)
open GeneralDepthTwoTerminalPlan300 (env)
open GeneralNominalExamples (intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralNominalVersionedJournal232 (Models)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalCommonBridge (Assignment)

inductive Node where | outer | inner | leaf
  deriving DecidableEq, Repr

def source : Node → Fin 3
  | .outer => 0
  | .inner => 1
  | .leaf => 2

def demand : Node → Occurrence roles
  | .outer => root
  | .inner => middle
  | .leaf => terminal

def code : Node → Nat
  | .outer => 1
  | .inner => 1
  | .leaf => 3

def childNodes : Node → List Node
  | .outer => [.inner]
  | .inner => [.leaf]
  | .leaf => []

def family : Node → GeneralDeclarations.Declaration
  | .outer | .inner => display
  | .leaf => intDisplay

def other : Node → GeneralDeclarations.Declaration
  | .outer | .inner => intDisplay
  | .leaf => display

abbrev plan : Node → Plan roles
  | .outer => GeneralDepthTwoFinalParents300.rootNow
  | .inner => GeneralDepthTwoFinalParents300.middleNow
  | .leaf => GeneralDepthTwoTerminalPlan300.plan

theorem frame (n : Node) (m : Assignment) (valid : Models final m) :
    Frame compiled final.core (demand n) (code n) (plan n) := by
  cases n
  · exact GeneralDepthTwoFinalParents300.root_frame m valid
  · exact GeneralDepthTwoFinalParents300.middle_frame m valid
  · exact GeneralDepthTwoTerminalFrame300.frame

theorem plan_holds (n : Node) (m : Assignment) (valid : Models final m) : Holds (plan n) m := by
  cases n
  · exact GeneralDepthTwoFinalParents300.root_holds m valid
  · exact GeneralDepthTwoFinalParents300.middle_holds m valid
  · exact GeneralDepthTwoTerminalPlan300.holds m valid

theorem declaration (n : Node) : (plan n).packet.declaration = family n := by cases n <;> rfl

theorem exact_code (n : Node) : (family n).id = code n := by cases n <;> rfl

theorem role (n : Node) : (demand n).demand.role = 0 := by cases n <;> decide +kernel

theorem args (n : Node) : ∀ i, (inputs (demand n)).demand.arguments i =
    ((source n).val,(source n).val) := by
  cases n
  · intro _; rfl
  · exact GeneralDepthTwoMiddleFrame300.input_bounds
  · exact GeneralDepthTwoTerminalFrame300.point_bounds

theorem located (n : Node) : GeneralNominalRecursiveCandidates.arguments env (inputs (demand n)) =
    some [(source n,source n)] := by cases n <;> decide +kernel

theorem known_slots (n : Node) : GeneralNominalState.Known env.state (source n).val := by
  cases n
  · exact ⟨(0 : Fin 3),rfl,.inr ⟨GeneralGeneratedNestedSource299.listDescriptor 1,rfl⟩⟩
  · exact ⟨(1 : Fin 3),rfl,.inr ⟨GeneralGeneratedNestedSource299.listDescriptor 2,rfl⟩⟩
  · exact ⟨(2 : Fin 3),rfl,.inl (by intro x; cases x)⟩

theorem not_pending (n : Node) : ¬ GeneralNominalState.RootPending env.state (inputs (demand n)).demand := by
  rintro ⟨i,missing⟩
  rw [args n i] at missing
  exact missing (known_slots n)

theorem observed_inputs (n : Node) :
    (plan n).input.observed.inputs = [some (.source (source n).val)] := by
  cases n
  · exact GeneralDepthTwoSecondInstall300.root_observed
  · exact GeneralDepthTwoSecondInstall300.middle_observed
  · unfold GeneralNominalCenters.Site.observed
    change List.ofFn (fun i => some (GeneralNominalRecursiveInspection.Origin.source
      (GeneralDepthTwoSecondInstall300.leafSite.center i))) = _
    simp [GeneralDepthTwoTerminalPlan300.leaf_center,List.ofFn_succ]
    rfl

theorem center_enum : final.core.sites = [(plan .outer).input,(plan .inner).input,(plan .leaf).input] :=
  GeneralDepthTwoTerminalFrame300.center_sites

theorem center_hit (s : Site roles) (present : s ∈ final.core.sites) : ∃ n : Node, s = (plan n).input := by
  rw [center_enum] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact ⟨.outer,rfl⟩
  · exact ⟨.inner,rfl⟩
  · exact ⟨.leaf,rfl⟩

theorem centers_equal (a b : Node) (same : GeneralNominalCenters.SameInputs (Models final)
    (plan a).input (plan b).input) : a = b := by
  have actual := GeneralDepthTwoCenters300.bounded_same
    (show (source a).val ≤ 2 by have h := (source a).isLt; omega)
    (show (source b).val ≤ 2 by have h := (source b).isLt; omega)
    (GeneralDepthTwoCenters300.same_center final_model same (observed_inputs a) (observed_inputs b))
  cases a <;> cases b <;> first | rfl | cases actual

theorem administrative (n : Node) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady final (demand n) := by
  constructor
  · have atFocus := frame n model final_model
    exact ⟨(plan n).input,atFocus.center_recorded,(plan n).input_exact.trans atFocus.occurrence_eq⟩
  · intro a first _ b last same
    obtain ⟨an,rfl⟩ := center_hit a first
    obtain ⟨bn,rfl⟩ := center_hit b last
    cases centers_equal an bn same
    exact .refl _

end Yulang.GeneralDepthTwoFinalNodes300
