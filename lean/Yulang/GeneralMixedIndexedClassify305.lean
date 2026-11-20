import Yulang.GeneralMixedIndexedEvidenceAt305

namespace Yulang.GeneralMixedIndexedClassify305
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedIndexedFrame305 (IndexedView reverse)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralMixedIndexedEvidenceAt305 (local_iff)

variable {v : B4Target.Vocabulary} {base : B4TargetV8.SourceBoundary v}
  {reg : v.Registry} {a₀ b₀ : v.State}

mutual
  theorem selected_forward
      (move : ∀ o f, B4TargetV8.Local base reg a₀ o f → B4TargetV8.Local base reg b₀ o f)
      (o : v.Demand) (d : CommonRoleOutermostResolver.Dictionary)
      (old : B4TargetV8.Classify base reg a₀ o (.selected d)) :
      B4TargetV8.Classify base reg b₀ o (.selected d) := by
    cases d with
    | node key dicts =>
      cases old with
      | selected yes next =>
        exact .selected (move o _ yes) (children_forward move _ dicts next)
  termination_by sizeOf d

  theorem children_forward
      (move : ∀ o f, B4TargetV8.Local base reg a₀ o f → B4TargetV8.Local base reg b₀ o f)
      (children : List v.Demand) (dicts : List CommonRoleOutermostResolver.Dictionary)
      (old : All₂ (fun o d => B4TargetV8.Classify base reg a₀ o (.selected d)) children dicts) :
      All₂ (fun o d => B4TargetV8.Classify base reg b₀ o (.selected d)) children dicts := by
    cases old with
    | nil => exact .nil
    | cons first rest =>
      exact All₂.cons (relation := fun o d => B4TargetV8.Classify base reg b₀ o (.selected d))
        (selected_forward move _ _ first) (children_forward move _ _ rest)
  termination_by sizeOf dicts
end

theorem classify_forward
    (move : ∀ o f, B4TargetV8.Local base reg a₀ o f → B4TargetV8.Local base reg b₀ o f)
    (o : v.Demand) (result : Result)
    (old : B4TargetV8.Classify base reg a₀ o result) :
    B4TargetV8.Classify base reg b₀ o result := by
  cases result with
  | selected d => exact selected_forward move o d old
  | pending => cases old with | pending check => exact .pending (move o _ check)
  | rejected => cases old with | rejected check => exact .rejected (move o _ check)
  | ambiguous => cases old with | ambiguous check => exact .ambiguous (move o _ check)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem classify_iff (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (o : Occurrence roles) (result : Result) :
    B4TargetV8.Classify (boundary roles) r a o result ↔
      B4TargetV8.Classify (boundary roles) r b o result :=
  ⟨classify_forward (base := boundary roles) (reg := r) (a₀ := a) (b₀ := b) (fun o f => (local_iff rel slices r o f).mp) o result,
    classify_forward (base := boundary roles) (reg := r) (a₀ := b) (b₀ := a) (fun o f => (local_iff rel slices r o f).mpr) o result⟩

end Yulang.GeneralMixedIndexedClassify305
