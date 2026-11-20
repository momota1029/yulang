import Yulang.GeneralMixedIndexedDiagnosticOutputs305
import Yulang.GeneralMixedDiagnosticCompiler304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedDiagnosticLocal305
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedIndexedFrame305 (IndexedView reverse)
open GeneralMixedIndexedDiagnosticHeads305
open GeneralMixedIndexedDiagnosticOutputs305 (output_iff sharing_iff merged_iff)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralMixedDiagnosticLocal304 (boundary6 boundary7)
variable {roles : Roles.RoleDecls} {a b : State roles}

theorem reject_forward (rel : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (given : B4TargetV6.RejectReason (boundary6 roles) r a root) :
    B4TargetV6.RejectReason (boundary6 roles) r b root := by
  obtain ⟨known,rootBad|candidateBad|⟨done,absent|⟨k,cs,choice,output⟩⟩⟩ := given
  · exact ⟨(not_congr (pending_iff rel r root)).mp known,Or.inl ((root_k2_iff rel r root).mp rootBad)⟩
  · exact ⟨(not_congr (pending_iff rel r root)).mp known,
      Or.inr (Or.inl ((candidate_k2_iff rel r root).mp candidateBad))⟩
  · exact ⟨(not_congr (pending_iff rel r root)).mp known,Or.inr (Or.inr
      ⟨(not_congr (inspection_iff rel r root)).mp done,
        Or.inl (fun k cs yes => absent k cs ((survivor_iff rel r root k cs).mpr yes))⟩)⟩
  · exact ⟨(not_congr (pending_iff rel r root)).mp known,Or.inr (Or.inr
      ⟨(not_congr (inspection_iff rel r root)).mp done,Or.inr
        ⟨k,cs,(unique_iff rel r root k cs).mp choice,(output_iff rel r root k).mp output⟩⟩)⟩

theorem local6_forward (rel : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (given : B4TargetV6.Local (boundary6 roles) r a root f) :
    B4TargetV6.Local (boundary6 roles) r b root f := by
  cases given with
  | pending reason => exact .pending ((pending_iff rel r root).mp reason)
  | inspectionPending known seen noRoot noCandidate =>
    exact .inspectionPending ((not_congr (pending_iff rel r root)).mp known)
      ((inspection_iff rel r root).mp seen) ((not_congr (root_k2_iff rel r root)).mp noRoot)
      ((not_congr (candidate_k2_iff rel r root)).mp noCandidate)
  | rejected reason => exact .rejected (reject_forward rel r root reason)
  | ambiguous safe first second distinct =>
    exact .ambiguous ((safe_iff rel r root).mp safe)
      ((survivor_iff rel r root ..).mp first) ((survivor_iff rel r root ..).mp second) distinct
  | selected safe unique noConflict =>
    exact .selected ((safe_iff rel r root).mp safe) ((unique_iff rel r root ..).mp unique)
      ((not_congr (output_iff rel r root _)).mp noConflict)

theorem priority_forward (rel : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (given : B4TargetV8.PriorityAmbiguity (boundary8 roles) r a root) :
    B4TargetV8.PriorityAmbiguity (boundary8 roles) r b root := by
  obtain ⟨okay,x,xs,y,ys,first,last,distinct⟩ := given
  refine ⟨?_,x,xs,y,ys,(survivor_iff rel r root x xs).mp first,
    (survivor_iff rel r root y ys).mp last,distinct⟩
  intro bad
  exact okay ((and_congr (not_congr (pending_iff rel r root))
    (or_congr (root_k2_iff rel r root) (candidate_k2_iff rel r root))).mpr bad)

theorem local_iff (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (root : Occurrence roles) (front : Frontier (Occurrence roles)) :
    B4TargetV8.Local (boundary8 roles) r a root front ↔
      B4TargetV8.Local (boundary8 roles) r b root front := by
  have priority : B4TargetV8.PriorityAmbiguity (boundary8 roles) r a root ↔
      B4TargetV8.PriorityAmbiguity (boundary8 roles) r b root :=
    ⟨priority_forward rel r root,priority_forward (reverse rel) r root⟩
  have v7 (f : Frontier (Occurrence roles)) :
      B4TargetV7.Local (boundary7 roles) r a root f ↔ B4TargetV7.Local (boundary7 roles) r b root f :=
    B4TargetV7.local_transport (fun _ => ⟨local6_forward rel r root,local6_forward (reverse rel) r root⟩)
      (merged_iff rel slices root) priority f
  exact B4TargetV8.local_transport v7 (sharing_iff rel r root) priority front

theorem recursive_iff (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV8.Local (boundary8 roles) r a) root tree ↔
      Resolves (B4TargetV8.Local (boundary8 roles) r b) root tree :=
  ⟨B4Skeleton.resolves_transport (fun o f => (local_iff rel slices r o f).mp),
    B4Skeleton.resolves_transport (fun o f => (local_iff rel slices r o f).mpr)⟩

theorem compiler_exact (rel : IndexedView a b) (slices : Semantics a b)
    (r : Registry) (root : Occurrence roles) (x : GeneralRebaseDiagnosticData268.Inputs (Occurrence roles))
    (valid : GeneralRebaseDiagnosticData268.Valid (boundary8 roles) r a root x)
    (complete : GeneralRebaseDiagnosticV8268.Complete x) (f : Frontier (Occurrence roles)) :
    GeneralRebaseDiagnosticV8268.run x = some f ↔ B4TargetV8.Local (boundary8 roles) r b root f :=
  (GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) r a root x valid complete f).trans
    (local_iff rel slices r root f)

end Yulang.GeneralMixedIndexedDiagnosticLocal305
