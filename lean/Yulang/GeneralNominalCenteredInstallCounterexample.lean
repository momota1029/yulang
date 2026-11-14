import Yulang.GeneralNominalCenteredInstallExample

/-! The frozen preservation contract quantifies over inventories that have
already forgotten an unregistered child. The actual initial installation below
exposes that child; no later elimination can recreate its missing source hole. -/
namespace Yulang.GeneralNominalCenteredInstallCounterexample
open GeneralNominalCenteredInstallExample
open GeneralNominalCenteredInstallObligations GeneralNominalCenteredSourceInvariant
open GeneralNominalCenteredSteps GeneralNominalCenters
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalCenteredOriginSeparation CommonNominalFullCarrier

abbrev rootHole : Nat := GeneralNominalIndexedHoleReadback.index
  (GeneralNominalSourceFrontier.frontier context.state) 0

theorem root_origin : origins context rootHole = .source 0 :=
  GeneralNominalIndexedHoleReadback.index_origin
    (GeneralNominalSourceFrontier.initial_inputs initial_source (0 : Fin 1)).1

theorem tests_pair : testMenu context registry = [.structural .pair,.structural .pair] := by cbv

theorem unknown_input : ¬ GeneralNominalState.Known source 2 := by
  rintro ⟨slot,equal,known⟩
  have same : slot = (2 : Fin 4) := Fin.ext equal
  subst slot
  rcases known with impossible | ⟨descriptor,recorded⟩
  · exact impossible rfl
  · cases recorded

structure Start where
  inventory : GeneralNominalHoleElimination.Inventory
  holes : inventory.holes = [rootHole]
  valid : GeneralNominalHoleElimination.Valid
    (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory
  journal : GeneralNominalCanonicalHoleJournal.Journal context root initialState.erased inventory
  coverage : Coverage registry context root initialState inventory journal

theorem start_exists : Nonempty Start := by
  obtain ⟨inventory,holes,valid,journal,⟨coverage⟩⟩ :=
    GeneralNominalCenteredInitialInventories.initialized initial_source (fun _ => rfl)
      [rootHole] (by simp) (fun _ => List.mem_singleton_self _)
  exact ⟨⟨inventory,holes,valid,journal,coverage⟩⟩

noncomputable def start : Start := Classical.choice start_exists

noncomputable def job : Installation registry context root where
  state := initialState
  reachable := .refl
  inventory := start.inventory
  valid := start.valid
  journal := start.journal
  coverage := start.coverage
  plan := planP
  support := []
  generated := .root
  enabled := enabledP
  novel := novelP
  guard := guardP
  children := by decide +kernel

theorem witness_initial : Models initialState witness :=
  (point_initial_models context root (fun _ => rfl) witness).mpr witness_source

theorem missing_leaf (hole : Nat) (member : hole ∈ job.inventory.holes) :
    ¬ Same witness (.source 2) (origins context hole) := by
  change hole ∈ start.inventory.holes at member
  rw [start.holes] at member
  cases List.mem_singleton.mp member
  rw [root_origin]
  intro same
  have bad := (same.2.2 _ _ (.source 2) (.source 0)).1
  exact GeneralNominalBranchingReadback.scalar_not_pair _ _ _ bad

theorem missing_head (test : Test) (member : test ∈ testMenu context registry) :
    ¬ GeneralNominalOriginTerms.Head witness (.source 2) test := by
  rw [tests_pair] at member
  have equal : test = .structural .pair := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
  subst test
  intro known
  obtain ⟨values,length,equal⟩ := known.2 _ (.source 2)
  exact GeneralNominalBranchingReadback.scalar_not_pair _ _ _ equal.1

theorem input_relevant : Origin.source 2 ∈ planInputs planP := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨1,?_,?_⟩
  · decide +kernel
  · rw [binderP_one]

theorem no_origin_frame : ¬ Nonempty (OriginFrame job job.inventory job.journal) :=
  no_frame_of_input job witness witness_initial planP_holds input_relevant missing_leaf missing_head

theorem not_newly_relevant_origins : ¬ NewlyRelevantOrigins registry context root :=
  fun produce => no_origin_frame (produce job)

theorem child_member : emittedChild ∈ planP.emitted :=
  List.mem_map.mpr ⟨⟨childR,List.mem_singleton_self _⟩,List.mem_attach _ _,rfl⟩

theorem not_nonterminal_install_preservation :
    ¬ GeneralNominalCenteredSourceConstruction.NonterminalInstallPreservation registry context root := by
  apply no_preservation_of_child job witness witness_initial planP_holds emittedChild child_member (0 : Fin 1)
  · intro hole member
    rw [show emittedChild.center (0 : Fin 1) = 2 from childP_center childSignature (0 : Fin 1)]
    exact missing_leaf hole member
  · intro test member
    rw [show emittedChild.center (0 : Fin 1) = 2 from childP_center childSignature (0 : Fin 1)]
    exact missing_head test member

theorem not_class_p_install_preservation :
    ¬ GeneralNominalCenteredSourceConstruction.ClassPInstallPreservation roles :=
  fun produce => not_nonterminal_install_preservation
    (produce registry checked context root initial_source point)

theorem counterexample :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalSourceFormation.InitialSource registry context root ∧
    GeneralNominalActualBudget.PointSource context root ∧
    Step registry root initialState afterP ∧
    ¬ GeneralNominalCenteredSourceConstruction.NonterminalInstallPreservation registry context root :=
  ⟨checked,initial_source,point,stepP,not_nonterminal_install_preservation⟩

end Yulang.GeneralNominalCenteredInstallCounterexample
