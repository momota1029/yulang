import Yulang.GeneralObservedMetadataRequests290

/-! Replay the original compiler at both metadata-read sites. The proposed
tables do not change the actual source registry, allocation or snapshot. -/
namespace Yulang.GeneralObservedMetadataBranch290
open GeneralDeclarations (Registry Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Constructors)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalInspection (Interpretation Bounds)
open GeneralNominalCandidates (Context)
open GeneralNominalRecursiveInspection (Report bindings)
open GeneralNominalMaterialization (Request Schema requests)
open GeneralObservedMetadataReport290 (reportFrom report_actual report_eq)
open GeneralObservedMetadataRequests290 (requestKeys schemaFrom schema_eq)
open GeneralObservedMetadataKeys290 (headKeys)
open GeneralObservedMetadataEntry290 (LocalEqual)
open GeneralObservedMetadataScope290 (coverage certify good_exact)

def requestsFrom (r : Registry) (s : GeneralNominalState.State) (root : Occurrence roles)
    (d : Declaration) (checked : DeclarationChecked r.constructors roles d) (report : Report s) : List Request :=
  requests s r root d checked (bindings s report)

def referenceRequests (r : Registry) (ctx : Context) (root : Occurrence roles)
    (d : Declaration) (checked : DeclarationChecked r.constructors roles d) (bounds : List (Bounds ctx.state)) :
    List Request :=
  requestsFrom r ctx.state root d checked (GeneralNominalRecursiveCandidates.report ctx d bounds)

def branchFootprint (r : Registry) (ctx : Context) (root : Occurrence roles)
    (d : Declaration) (checked : DeclarationChecked r.constructors roles d) (bounds : List (Bounds ctx.state)) :
    List Nat :=
  coverage ctx.state [d] ++ requestKeys (referenceRequests r ctx root d checked bounds)

def branchFrom (r : Registry) (s : GeneralNominalState.State) (c : Constructors) (i : Interpretation)
    (root : Occurrence roles) (d : Declaration) (checked : DeclarationChecked r.constructors roles d)
    (bounds : List (Bounds s)) : Report s × (List Request × Schema) :=
  let row := reportFrom s c i d bounds
  let emitted := requestsFrom r s root d checked row
  ⟨row,emitted,schemaFrom c i emitted⟩

theorem branch_actual (r : Registry) (ctx : Context) (root : Occurrence roles)
    (d : Declaration) (checked : DeclarationChecked r.constructors roles d) (bounds : List (Bounds ctx.state)) :
    branchFrom r ctx.state ctx.state.constructors ctx.interpretation root d checked bounds =
      ⟨GeneralNominalRecursiveCandidates.report ctx d bounds,
        referenceRequests r ctx root d checked bounds,
        GeneralNominalRecursiveCandidates.generated r ctx root d checked bounds⟩ := rfl

theorem branch_eq (r : Registry) (ctx : Context) (c : Constructors) (i : Interpretation)
    (root : Occurrence roles) (d : Declaration) (checked : DeclarationChecked r.constructors roles d)
    (bounds : List (Bounds ctx.state))
    (h : LocalEqual (branchFootprint r ctx root d checked bounds) ctx.state.constructors ctx.interpretation c i) :
    branchFrom r ctx.state c i root d checked bounds =
      ⟨GeneralNominalRecursiveCandidates.report ctx d bounds,
       referenceRequests r ctx root d checked bounds,
       GeneralNominalRecursiveCandidates.generated r ctx root d checked bounds⟩ := by
  have head := report_eq ctx.state ctx.state.constructors ctx.interpretation c i d bounds
    (h.restrict (fun k hk => List.mem_append_left _
      (GeneralObservedMetadataScope290.covers_head ctx.state [d] (List.mem_singleton_self _) hk)))
  have tail := schema_eq ctx.state.constructors ctx.interpretation c i
    (referenceRequests r ctx root d checked bounds)
    (h.restrict (fun k hk => List.mem_append_right _ hk))
  rw [← branch_actual]
  unfold branchFrom
  rw [← head,report_actual]
  exact congrArg (fun result =>
    (GeneralNominalRecursiveCandidates.report ctx d bounds,referenceRequests r ctx root d checked bounds,result))
    tail.symm

theorem accepted_branch (r : Registry) (ctx : Context) (c : Constructors) (i : Interpretation)
    (root : Occurrence roles) (d : Declaration) (checked : DeclarationChecked r.constructors roles d)
    (bounds : List (Bounds ctx.state))
    (same : certify (branchFootprint r ctx root d checked bounds) ctx.state.constructors ctx.interpretation c i = .good) :
    branchFrom r ctx.state c i root d checked bounds =
      ⟨GeneralNominalRecursiveCandidates.report ctx d bounds,referenceRequests r ctx root d checked bounds,
        GeneralNominalRecursiveCandidates.generated r ctx root d checked bounds⟩ :=
  branch_eq r ctx c i root d checked bounds ((good_exact ..).mp same).1

end Yulang.GeneralObservedMetadataBranch290
