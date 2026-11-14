import Yulang.GeneralDictionaryNominalPair178
import Yulang.GeneralNominalNonpointInspectionExamples

/-! A finite nonpoint endpoint regression. This is not a counterexample to the
centered ground boundary: no centered Candidate is asserted here. -/
namespace Yulang.GeneralDictionaryNominalPairExample178
open GeneralDeclarations GeneralDeclarationPatterns CommonNominalFullCarrier
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionaryNominalPair178
open GeneralDeclarationExamples (roles constructors)

abbrev base : GeneralSourceState.State where
  slots := 4
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ h; cases h
  intervals_sound := by intro _ _ _ h; cases h
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ h; cases h
abbrev descriptor : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (2,3)],rfl⟩
abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun i => if i.val < 2 then some descriptor else none
  catalogue := by intro i d h; split at h; cases Option.some.inj h; rfl; cases h
  bodies_opaque := by intro _ _ _; rfl
abbrev context : Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev declaration : Declaration := ⟨1,0,[.app 0 [.var 0]],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev root := GeneralNominalExamples.displayRoot
abbrev captures : GeneralNominalAllocation.Bindings := [(0,2,3),(0,2,3)]
abbrev lo := GeneralNominalAllocation.source state registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 0 0 0)
abbrev hi := GeneralNominalAllocation.source state registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 1 0 0)

theorem lo_fresh (i : Nat) (bounded : i ≤ 3) : lo ≠ i :=
  GeneralNominalAllocation.source_initial_fresh state registry root.identity _ i (by exact bounded)
theorem hi_fresh (i : Nat) (bounded : i ≤ 3) : hi ≠ i :=
  GeneralNominalAllocation.source_initial_fresh state registry root.identity _ i (by exact bounded)
theorem endpoints_ne : lo ≠ hi := by
  intro h
  have h := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp h
  cases h

 def assignment (good : Bool) : GeneralNominalCommonBridge.Assignment := fun i =>
  (if i < 2 then nominal 0 [.inl (.base .int)] else if i = 2 then .bottom
   else if good = true ∧ i = lo then .bottom else .top,Common.rowEmpty)

 theorem lower_value (good : Bool) : (assignment good 2).1 = .bottom := rfl
 theorem upper_value (good : Bool) : (assignment good 3).1 = .top := by
  simp [assignment,Ne.symm (lo_fresh 3 (by decide +kernel))]; rfl
 theorem fresh_lower_good : (assignment true lo).1 = .bottom := by
  have above : ¬ lo < 2 := by intro h; have := lo_fresh lo (by omega); exact this rfl
  simp [assignment,above,lo_fresh 2 (by decide +kernel)]; rfl
 theorem fresh_upper_good : (assignment true hi).1 = .top := by
  have above : ¬ hi < 2 := by intro h; have := hi_fresh hi (by omega); exact this rfl
  simp [assignment,above,hi_fresh 2 (by decide +kernel),Ne.symm endpoints_ne]; rfl
 theorem fresh_lower_bad : (assignment false lo).1 = .top := by
  have above : ¬ lo < 2 := by intro h; have := lo_fresh lo (by omega); exact this rfl
  simp [assignment,above,lo_fresh 2 (by decide +kernel)]; rfl

 theorem source_models (good : Bool) : GeneralNominalState.Models state (assignment good) := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ h; cases h
  · intro _ _ h; cases h
  · intro _ h; cases h
  · intro slot d recorded
    change (if slot.val < 2 then some descriptor else none) = some d at recorded
    split at recorded
    next small =>
      cases Option.some.inj recorded
      refine ⟨[.inl (.base .int)],.cons ?_ .nil,?_,?_⟩
      · change Subtype .bottom (.base .int) ∧ Subtype (.base .int) (assignment good 3).1
        rw [upper_value]
        exact ⟨(CommonNominalFullModelMap.subtype_exact .bottom (.base .int)).mpr (CommonBoundCoalescing.bottom_le _),
          GeneralNominalNonpointInspectionExamples.int_top⟩
      all_goals simpa [assignment,small] using subtype_refl (nominal 0 [.inl (.base .int)])
    next => cases recorded

 def shape : Shape context declaration where
  lower := 0
  upper := 1
  different := by decide +kernel
  left := descriptor
  right := descriptor
  recorded := rfl
  recordedRight := rfl
  same := rfl
  n := 1
  names := fun _ => 0
  distinct := fun i j _ => Subsingleton.elim i j
  low := fun _ => (2,3)
  high := fun _ => (2,3)
  parameters := rfl
  parametersRight := rfl
  query := by simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,List.ofFn_succ]

 theorem report_captures : bindings state (report context declaration [(0,1)]) = captures := by
  rw [report_exact context declaration 0 1 (by decide +kernel) descriptor descriptor rfl rfl rfl
    (fun _ : Fin 1 => 0) (fun _ => (2,3)) (fun _ => (2,3)) rfl rfl shape.query]
  rfl

 theorem merges_exact : GeneralNominalAllocation.merges state registry root.identity declaration captures =
   GeneralNominalAllocation.equations lo (.union (.var 2) (.var 2)) ++
   GeneralNominalAllocation.equations hi (.inter (.var 3) (.var 3)) := rfl

 theorem merge_good : PresenceNormalForm.All CommonNominalFullCarrier.model (assignment true)
    (GeneralNominalAllocation.merges state registry root.identity declaration captures) := by
  rw [merges_exact,PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
    GeneralNominalCaptureMerges.equations_exact]
  change Equivalent (assignment true lo).1 (.union .bottom .bottom) ∧
    Equivalent (assignment true hi).1 (.inter (assignment true 3).1 (assignment true 3).1)
  rw [fresh_lower_good,fresh_upper_good,upper_value]
  exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _ ) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
    ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩

 theorem merge_bad : ¬ PresenceNormalForm.All CommonNominalFullCarrier.model (assignment false)
    (GeneralNominalAllocation.merges state registry root.identity declaration captures) := by
  intro merged
  rw [merges_exact,PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact] at merged
  have upper : Subtype (.union .bottom .bottom) .bottom :=
    (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩
  have badLower := merged.1.1
  change Subtype (assignment false lo).1 (.union .bottom .bottom) at badLower
  rw [fresh_lower_bad] at badLower
  have impossible : Subtype .top .bottom := subtype_trans badLower upper
  have old := (CommonNominalFullModelMap.subtype_exact (.top : Common.Ty) (.bottom : Common.Ty)).mp impossible
  let environment : CommonFinite.Environment Common.Row := ⟨fun _ => .bottom, fun _ => []⟩
  have witness := (CommonFinite.producerLe_iff_probe _ _).mp (old 0)
    0 environment .impossible (by simp [Common.observeTy, CommonSyntax.Layer.evalAt])
  simp [Common.observeTy, CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt,
    CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep] at witness

 theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

 theorem endpoint_order (good : Bool) : Subtype (assignment good 0).1 (assignment good 1).1 :=
  subtype_refl _

 theorem source_unchanged (i : Nat) (bounded : i ≤ 3) : assignment true i = assignment false i := by
  simp [assignment,Ne.symm (lo_fresh i bounded)]

 theorem branch_good : BranchModels registry context root declaration declaration_checked [(0,1)] (assignment true) := by
  apply (branch_models_iff_merges context registry root declaration declaration_checked shape rfl rfl
    (assignment true) (source_models true) (endpoint_order true)).mpr
  change PresenceNormalForm.All model (assignment true) (GeneralNominalAllocation.merges state registry root.identity declaration
    (bindings state (report context declaration [(0,1)])))
  rw [report_captures]
  exact merge_good

 theorem branch_bad : ¬ BranchModels registry context root declaration declaration_checked [(0,1)] (assignment false) := by
  intro branch
  have merged := (branch_models_iff_merges context registry root declaration declaration_checked shape rfl rfl
    (assignment false) (source_models false) (endpoint_order false)).mp branch
  change PresenceNormalForm.All model (assignment false) (GeneralNominalAllocation.merges state registry root.identity declaration
    (bindings state (report context declaration [(0,1)]))) at merged
  rw [report_captures] at merged
  exact merge_bad merged

/-- The source model and endpoint inequality do not suffice for validity in the
same fixed assignment, even though the branch has a corrected model. -/
 theorem fixed_model_obstruction :
    GeneralNominalState.Models state (assignment false) ∧
    Subtype (assignment false 0).1 (assignment false 1).1 ∧
    (∃ model, BranchModels registry context root declaration declaration_checked [(0,1)] model) ∧
    ¬ BranchModels registry context root declaration declaration_checked [(0,1)] (assignment false) :=
  ⟨source_models false,endpoint_order false,⟨assignment true,branch_good⟩,branch_bad⟩
end Yulang.GeneralDictionaryNominalPairExample178
