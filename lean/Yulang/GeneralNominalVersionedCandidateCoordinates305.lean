import Yulang.GeneralNominalCandidateReplayModels305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedCandidateCoordinates305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (Context report arguments Metadata)
open GeneralNominalRecursiveInspection (Finished bindings)
open GeneralNominalInspection (Bounds)
open GeneralNominalVersionedCandidates231 (Prepared Failed Survivor Unique InspectionPending HeadModels inputs children)
open GeneralNominalVersionedAllocation231 (Fresh)
open GeneralNominalReportContext305 (EquivalentContexts arguments_exact report_exact)
open GeneralNominalReportSourceTransport (moveBounds moveReport)
open GeneralNominalCandidateReplayModels305
variable {old next : Context}

theorem at_prepared (l : arguments c (inputs root) = some bs) :
    Prepared r c root d ↔
      Metadata r c ∧ GeneralNominalState.Linked c.state (inputs root).demand ∧
      Fresh c.state r root.identity (bindings c.state (report c d bs)) ∧
      Finished (report c d bs) ∧ ∃ model, HeadModels r c root d bs model := by
  constructor
  · rintro ⟨m,linked,b,loc,f,closed,existsModel⟩
    cases Option.some.inj (loc.symm.trans l)
    exact ⟨m,linked,f,closed,existsModel⟩
  · rintro ⟨m,linked,f,closed,existsModel⟩
    exact ⟨m,linked,bs,l,f,closed,existsModel⟩

theorem at_failed (l : arguments c (inputs root) = some bs) :
    Failed r c root d ↔ Metadata r c ∧
      Fresh c.state r root.identity (bindings c.state (report c d bs)) ∧
      (report c d bs).blocked = [] ∧ (report c d bs).arity = [] ∧
      ((report c d bs).conflicts ≠ [] ∨ ¬ ∃ model, HeadModels r c root d bs model) := by
  constructor
  · rintro ⟨m,b,loc,f,noBlock,arity,bad⟩
    cases Option.some.inj (loc.symm.trans l)
    exact ⟨m,f,noBlock,arity,bad⟩
  · rintro ⟨m,f,noBlock,arity,bad⟩
    exact ⟨m,bs,l,f,noBlock,arity,bad⟩

theorem prepared_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (d : Declaration) : Prepared r old root d ↔ Prepared r next root d := by
  cases prev : arguments old (inputs root) with
  | none =>
    have absent : arguments next (inputs root) = none := by rw [arguments_exact eq,prev]; rfl
    constructor
    · rintro ⟨_,_,_,loc,_⟩; rw [prev] at loc; cases loc
    · rintro ⟨_,_,_,loc,_⟩; rw [absent] at loc; cases loc
  | some bs =>
    have after : arguments next (inputs root) = some (bs.map (moveBounds eq.geometry.slot)) := by
      rw [arguments_exact eq,prev]; rfl
    rw [at_prepared prev,at_prepared after,bindings_eq eq,report_exact eq]
    exact and_congr (metadata_iff eq r) (and_congr (linked_iff eq (inputs root))
      (and_congr (fresh_iff eq ..)
        (and_congr (GeneralNominalReportSourceTransport.finished_iff ..).symm
          (exists_congr (head_model_iff eq r root d bs)))))

theorem failed_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (d : Declaration) : Failed r old root d ↔ Failed r next root d := by
  cases prev : arguments old (inputs root) with
  | none =>
    have absent : arguments next (inputs root) = none := by rw [arguments_exact eq,prev]; rfl
    constructor
    · rintro ⟨_,_,loc,_⟩; rw [prev] at loc; cases loc
    · rintro ⟨_,_,loc,_⟩; rw [absent] at loc; cases loc
  | some bs =>
    have after : arguments next (inputs root) = some (bs.map (moveBounds eq.geometry.slot)) := by
      rw [arguments_exact eq,prev]; rfl
    rw [at_failed prev,at_failed after,bindings_eq eq,report_exact eq]
    refine and_congr (metadata_iff eq r) (and_congr (fresh_iff eq ..) ?_)
    simp [moveReport,head_model_iff eq r root d bs]

theorem children_exact (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (d : Declaration) (checked : DeclarationChecked r.constructors roles d) (bs : List (Bounds old.state)) :
    children r old root d checked bs =
      children r next root d checked (bs.map (moveBounds eq.geometry.slot)) := by
  let p : GeneralNominalCenters.Plan roles :=
    ⟨⟨r,old,GeneralNominalDemandMerging.pointSite (inputs root),d,checked,bs⟩,
     GeneralNominalCenters.rootSite old.state.seed (inputs root),rfl⟩
  exact GeneralDeferredLadderTransport302.children_eq (GeneralNominalReportContext305.same_plan p eq)

theorem survivor_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (key : Nat) (cs : List (Occurrence roles)) : Survivor r old root key cs ↔ Survivor r next root key cs := by
  constructor
  · rintro ⟨known,d,visible,check,ident,role,bs,loc,ok,kids⟩
    have newFound : arguments next (inputs root) = some (bs.map (moveBounds eq.geometry.slot)) := by
      rw [arguments_exact eq,loc]; rfl
    exact ⟨(not_congr (pending_iff eq (inputs root))).mp known,d,visible,check,ident,role,_,newFound,
      (prepared_iff eq r root d).mp ok,kids.trans (children_exact eq r root d check bs)⟩
  · rintro ⟨known,d,visible,check,ident,role,bs,loc,ok,kids⟩
    rw [arguments_exact eq] at loc
    cases before : arguments old (inputs root) with
    | none => rw [before] at loc; cases loc
    | some oldBounds =>
      rw [before] at loc
      have exactBound : oldBounds.map (moveBounds eq.geometry.slot) = bs := Option.some.inj loc
      subst bs
      exact ⟨(not_congr (pending_iff eq (inputs root))).mpr known,d,visible,check,ident,role,_,before,
        (prepared_iff eq r root d).mpr ok,kids.trans (children_exact eq r root d check oldBounds).symm⟩

theorem unique_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles)
    (key : Nat) (cs : List (Occurrence roles)) : Unique r old root key cs ↔ Unique r next root key cs := by
  simp only [Unique,survivor_iff eq]

theorem inspection_pending_iff (eq : EquivalentContexts old next) (r : Registry) (root : Occurrence roles) :
    InspectionPending r old root ↔ InspectionPending r next root := by
  simp only [InspectionPending,pending_iff eq,prepared_iff eq,failed_iff eq]

end Yulang.GeneralNominalVersionedCandidateCoordinates305
