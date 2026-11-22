import Yulang.GeneralDeclarativeExactSupport337
import Yulang.GeneralDeclarativeEndpointChildModels336

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeExactRegression337
open GeneralDeclarativeEndpointChildren336
open GeneralDeclarativeEndpointChildModels336 (shared_root shared_child footprint_root footprint_child)
open GeneralDeclarativeRecordDecl326 (decl registry checked)
open GeneralDeclarativeRecordReplay330 (covered)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeEndpointProgram336 (Projection)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointSupport336 (Certified)
open GeneralDeclarativeExactOverlay337 (ModelsExact values patch_checked list_sound)
open GeneralDeclarativeExactSupport337 (ready_after_ties endpointRows endpoints_sound)
open GeneralDeclarativeEndpointBatch336 (patch)
open GeneralDeclarativeExactDictionary337 (Rule Evidence dictionary_sound)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (exactEmpty Equivalent)
open CommonRoleOutermostResolver (Classify)

def sourceModel : Assignment := fun n =>
  if n = 6 then (exactEmpty,(GeneralDeclarativeEndpointChildModels336.sourceModel n).2)
  else GeneralDeclarativeEndpointChildModels336.sourceModel n

theorem source_valid : Models initial sourceModel := by
  have absent : 6 ∉ stateNames initial := by decide +kernel
  apply (preserves_models initial (first := sourceModel)
    (last := GeneralDeclarativeEndpointChildModels336.sourceModel) ?_).mpr
    GeneralDeclarativeEndpointChildModels336.source_valid
  intro n active
  have different : n ≠ 6 := fun h => absent (h ▸ active)
  simp [sourceModel,different]

def seed : Assignment := patch initial keep (values sourceModel jobs) sourceModel

theorem seed_valid : ModelsExact named sidecar seed :=
  patch_checked sourceModel source_valid
    (list_sound GeneralDeclarativeEndpointChildren336.read program sourceModel source_valid) protect

theorem old_rows {e : Entry} : GeneralDeclarativeEndpointSupport336.writes e ⊆ endpointRows e := by
  obtain ⟨route,cap⟩ := e
  cases route with
  | field a k lo hi => exact fun _ h => h
  | rest a keys lo hi => intro row impossible; cases impossible

theorem inhabited : ∃ m, ModelsExact final sidecar m ∧ (m 6).1 = exactEmpty := by
  obtain ⟨first,valid,kept⟩ := ready_after_ties (keep := protect) (fallback := fallback)
    seed_valid (shared_root seed) (fun _ found => GeneralDeclarativeEndpointOverlay336.spans_ready found) footprint_root
  have first_valid : ModelsExact rootFinal sidecar first := by
    refine ⟨(model_append _).mpr ⟨valid.1,?_⟩,valid.2⟩
    intro e used
    cases List.mem_singleton.mp used
    change Equivalent (first 6).1 (first 11).1
    rw [kept 6 (by decide +kernel),kept 11 (by decide +kernel)]
    exact eqv_refl _
  obtain ⟨last,validLast,keptLast⟩ := ready_after_ties (keep := protect) (fallback := fallback)
    first_valid (shared_child first) (fun _ found => by cases List.mem_singleton.mp found; exact child_bounds) footprint_child
  have childModel : ModelsExact childFinal sidecar last := by
    refine ⟨(model_append _).mpr ⟨validLast.1,?_⟩,validLast.2⟩
    intro e used
    cases List.mem_singleton.mp used
    change Equivalent (last 5).1 (last 8).1
    rw [keptLast 5 (by decide +kernel),keptLast 8 (by decide +kernel),
      kept 5 (by decide +kernel),kept 8 (by decide +kernel)]
    exact eqv_refl _
  refine ⟨last,⟨(model_append _).mpr ⟨childModel.1,?_⟩,childModel.2⟩,?_⟩
  · intro row used
    obtain ⟨piece,part,written⟩ := List.mem_flatMap.mp used
    exact endpoints_sound (childModel.2 piece part) row (old_rows written)
  · rw [keptLast 6 (by decide +kernel),kept 6 (by decide +kernel)]
    rfl

theorem selected :
    Classify (Rule authorized sidecar registry interpretation wait) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (.selected choiceRoot) (.cons (.selected (.selected choiceChild) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem exact_dictionary :
    ∃ m, ModelsExact final sidecar m ∧ (m 6).1 = exactEmpty ∧
      Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit,closed⟩ := inhabited
  exact ⟨m,fit,closed,dictionary_sound checked covered declared selected m fit⟩

/-- The exact lower residual row is in an ordinary, backed endpoint
table. No matching of the original actual center RHS is involved. -/
theorem backed_residual :
    (⟨10,endL⟩ : Equation) ∈
      (restriction (GeneralDeclarativeExactSupport337.authorize authorized sidecar)).equations := by
  have current : Read authorized arg [7] payload payload payload payload endL endU :=
    ⟨GeneralDeclarativeGrowth327.fits initial_final GeneralDeclarativeEndpointChildren336.read.valid,by decide,
      .inline (GeneralDeclarativeLowerKnown321.alias_refl _) .exactEnd (supported initial_lo),
      .inline (GeneralDeclarativeLowerKnown321.alias_refl _) .width (supported initial_hi),rfl,rfl⟩
  let e : Entry := ⟨.rest arg [7] endL endU,⟨10,11,12⟩⟩
  have there : e ∈ sidecar := List.mem_cons_of_mem _ List.mem_cons_self
  have certified : Certified authorized e :=
    ⟨arg,[(7,0)],1,payload,payload,payload,payload,endL,endU,jobs,initial,protect,current,program,there⟩
  exact GeneralDeclarativeExactSupport337.from_projection there certified List.mem_cons_self

end Yulang.GeneralDeclarativeExactRegression337
