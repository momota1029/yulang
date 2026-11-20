import Yulang.GeneralMixedDiagnosticLocal304
import Yulang.GeneralRebaseDiagnosticV8268
import Yulang.B4Skeleton

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticCompiler304
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralMixedDiagnosticHead304
open GeneralMixedDiagnosticLocal304 (local_iff)
open GeneralRebaseDiagnosticData268 (Inputs Valid SurvivorSound)
open GeneralRebaseDiagnosticV8268 (Complete)
open GeneralRebasePartialBool268 (Reflect Answer)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem reflect_map {p q : Prop} (same : p ↔ q) (answer : Answer) :
    Reflect p answer → Reflect q answer := by
  cases answer with
  | none => exact fun _ => trivial
  | some found =>
    cases found
    · exact fun no yes => no (same.mpr yes)
    · exact same.mp

theorem survivor_forward (head : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (v : GeneralRebasePartialClassification267.Verdict (Nat × List (Occurrence roles)))
    (given : SurvivorSound (boundary8 roles) reg a root v) :
    SurvivorSound (boundary8 roles) reg b root v := by
  cases v with
  | none => exact fun k cs seen => given k cs ((survivor_iff head reg root k cs).mpr seen)
  | unique entry =>
    obtain ⟨key,children⟩ := entry
    exact unique_forward head given
  | ambiguous x y =>
    obtain ⟨ak,ac⟩ := x
    obtain ⟨bk,bc⟩ := y
    exact ⟨given.1,(survivor_iff head reg root ak ac).mp given.2.1,
      (survivor_iff head reg root bk bc).mp given.2.2⟩
  | deferred => exact trivial

/-- One set of actual executable diagnostic inputs can be reused after
changing the archive representation. Missing answers remain missing. -/
theorem inputs_forward (head : HeadView a b) (slices : Semantics a b)
    (reg : Registry) (root : Occurrence roles) (x : Inputs (Occurrence roles))
    (given : Valid (boundary8 roles) reg a root x) :
    Valid (boundary8 roles) reg b root x :=
  ⟨reflect_map (pending_iff head reg root) _ given.rootPending,
    reflect_map (root_k2_iff head reg root) _ given.rootK2,
    reflect_map (candidate_k2_iff head reg root) _ given.candidateK2,
    reflect_map (inspection_iff head reg root) _ given.inspection,
    survivor_forward head reg root _ given.survivors,
    fun k => reflect_map (output_iff head reg root k) _ (given.outputConflict k),
    reflect_map (GeneralMixedDiagnosticSlice304.conflict_iff head slices root) _ given.mergedConflict,
    reflect_map (sharing_iff head reg root) _ given.sharingConflict⟩

theorem compiler_exact (head : HeadView a b) (slices : Semantics a b)
    (reg : Registry) (root : Occurrence roles) (x : Inputs (Occurrence roles))
    (given : Valid (boundary8 roles) reg a root x) (complete : Complete x) (f : Frontier (Occurrence roles)) :
    GeneralRebaseDiagnosticV8268.run x = some f ↔ B4TargetV8.Local (boundary8 roles) reg b root f :=
  GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) reg b root x
    (inputs_forward head slices reg root x given) complete f

theorem recursive_iff (head : HeadView a b) (slices : Semantics a b)
    (reg : Registry) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV8.Local (boundary8 roles) reg a) root tree ↔
      Resolves (B4TargetV8.Local (boundary8 roles) reg b) root tree :=
  ⟨B4Skeleton.resolves_transport (fun o f => (local_iff head slices reg o f).mp),
    B4Skeleton.resolves_transport (fun o f => (local_iff head slices reg o f).mpr)⟩

end Yulang.GeneralMixedDiagnosticCompiler304
