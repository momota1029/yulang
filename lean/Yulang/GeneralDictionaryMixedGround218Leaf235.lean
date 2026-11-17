import Yulang.GeneralDictionaryMixedGround218Install234
import Yulang.GeneralDictionaryGroundCopy218Stability
import Yulang.GeneralNominalCenteredModelExtension

set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryGroundCopy218Source GeneralDictionaryGroundCopy218Reobserve
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev childId := fresh 7 0 0 6 0 0
abbrev oldChild : Occurrence roles := ⟨childId,⟨1,fun _ => (2,3),[],by intro _ h; cases h⟩⟩
abbrev leafDecl := GeneralNominalCenteredHeadAllocEncoding.declaration leaf
abbrev leafCheck := GeneralNominalCenteredHeadAllocEncoding.declaration_checked leaf_checked
abbrev parentPacket := GeneralDictionaryGroundCopy218Install.packet
noncomputable abbrev ctx : Context := ⟨{ snapshot with
  allocated := snapshot.allocated ++ GeneralNominalVersionedInstallation231.allocated parentPacket
  reserved := snapshot.reserved ++ GeneralNominalVersionedInstallation231.reserved parentPacket
  ordinary := snapshot.ordinary ++ GeneralNominalVersionedInstallation231.atoms parentPacket }, interpretation⟩
abbrev lo := GeneralNominalAggregateVersion231.slot 7 childId 1 0 0 [(0,2,3),(0,2,3)]
abbrev hi := GeneralNominalAggregateVersion231.slot 7 childId 1 1 0 [(0,2,3),(0,2,3)]

theorem query :
    GeneralNominalInspection.queries ctx.state interpretation leafDecl =
      [.variables [0],.variables [0]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,leafDecl,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem report_exact : report ctx leafDecl [(2,3),(2,3)] =
    { captures := [⟨0,(2,3),none⟩,⟨0,(2,3),none⟩], checked := [(2,3),(2,3),(2,3),(2,3)] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.append]

theorem distinct : lo ≠ hi := by
  intro equal
  have bad := (GeneralNominalIdentities.source_identity 7 _ _).mp equal
  have purpose := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) bad
  cases purpose

def patch (model : Assignment) : Assignment := fun identity =>
  if identity = lo then (.union (model 2).1 (model 2).1,(model identity).2)
  else if identity = hi then (.inter (model 3).1 (model 3).1,(model identity).2)
  else model identity

theorem patch_outside (model : Assignment) (one : identity ≠ lo) (two : identity ≠ hi) :
    patch model identity = model identity := by simp [patch,one,two]

theorem head_model (model : Assignment)
    (valid : GeneralNominalState.Models ctx.state model)
    (below : Subtype (model 2).1 (model 3).1)
    (missing : ∀ identity ∈ GeneralNominalState.sources ctx.state, identity ≠ lo ∧ identity ≠ hi) :
    GeneralNominalVersionedCandidates231.HeadModels registry ctx oldChild leafDecl [(2,3),(2,3)] (patch model) := by
  have kept (identity) (member : identity ∈ GeneralNominalState.sources ctx.state) :
      patch model identity = model identity := patch_outside model (missing identity member).1 (missing identity member).2
  have small (identity : Fin 8) : patch model identity.val = model identity.val := by
    apply kept
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨identity,rfl⟩
  have small2 : patch model 2 = model 2 := small 2
  have small3 : patch model 3 = model 3 := small 3
  have current := GeneralNominalCenteredModelExtension.source_models_same
    ctx.state (fun n h => (kept n h).symm) valid
  constructor
  · unfold GeneralNominalVersionedCandidates231.privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalVersionedAllocation231.propagate_models ..).mpr ⟨current,?_,?_⟩,?_⟩
    · intro one oneMem two twoMem _
      simp only [bindings,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at oneMem twoMem
      rcases oneMem with rfl | rfl <;> rcases twoMem with rfl | rfl
      all_goals change Subtype (patch model 2).1 (patch model 3).1
      all_goals rw [small2,small3]; exact below
    · have names : leafDecl.inputNames = [0,0] := by
        simp [Declaration.inputNames,leafDecl,GeneralNominalCenteredHeadAllocEncoding.declaration,
          normalizeArgs,normalize,variablesArgs,Pattern.variables]
      have merged : PresenceNormalForm.All CommonNominalFullCarrier.model (patch model)
          (GeneralNominalAllocation.equations lo (.union (.var 2) (.var 2)) ++
           GeneralNominalAllocation.equations hi (.inter (.var 3) (.var 3))) := by
        apply (PresenceNormalForm.all_append ..).mpr
        constructor
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          change Equivalent (patch model lo).1 (.union (patch model 2).1 (patch model 2).1)
          rw [small2]
          simp only [patch,ite_true]
          exact ⟨subtype_refl _,subtype_refl _⟩
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          change Equivalent (patch model hi).1 (.inter (patch model 3).1 (patch model 3).1)
          rw [small3]
          simp only [patch,Ne.symm distinct,ite_false,ite_true]
          exact ⟨subtype_refl _,subtype_refl _⟩
      unfold GeneralNominalVersionedAllocation231.merges
      rw [names]
      change PresenceNormalForm.All _ _ ((_ ++ _) ++ ((_ ++ _) ++ []))
      exact (PresenceNormalForm.all_append ..).mpr ⟨merged,
        (PresenceNormalForm.all_append ..).mpr ⟨merged,PresenceNormalForm.all_nil _ _⟩⟩
    · intro atom member
      simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals change Subtype (patch model 2).1 (patch model 3).1
      all_goals rw [small2,small3]; exact below
  · rw [report_exact]
    simp [ProjectionModels]

theorem linked :
    GeneralNominalState.Linked ctx.state oldChild.demand := by
  refine ⟨fun _ => ⟨?_,?_⟩,by intro _ h; cases h⟩
  all_goals
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
  · exact List.mem_ofFn.mpr ⟨(2 : Fin 8),rfl⟩
  · exact List.mem_ofFn.mpr ⟨(3 : Fin 8),rfl⟩

theorem located : arguments ctx
    (GeneralNominalCenteredHeadCandidates.inputs oldChild) = some [(2,3),(2,3)] := rfl

theorem known :
    ¬ GeneralNominalState.RootPending ctx.state oldChild.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(2 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩

theorem prepared (model : Assignment)
    (valid : GeneralNominalState.Models ctx.state model)
    (below : Subtype (model 2).1 (model 3).1)
    (missing : ∀ identity ∈ GeneralNominalState.sources ctx.state, identity ≠ lo ∧ identity ≠ hi)
    (fresh : GeneralNominalVersionedAllocation231.Fresh ctx.state registry childId [(0,2,3),(0,2,3)]) :
    GeneralNominalVersionedCandidates231.Prepared registry ctx oldChild leafDecl := by
  refine ⟨source.metadata,linked,[(2,3),(2,3)],located,(by rw [report_exact]; exact fresh),?_,
    patch model,head_model model valid below missing⟩
  rw [report_exact]
  exact ⟨rfl,rfl,rfl⟩

theorem leaf_only (visible : d ∈ registry.declarations) (role : d.role = 1) : d = leafDecl := by
  rcases List.mem_cons.mp visible with rfl | member
  · cases role
  · exact List.mem_singleton.mp member

theorem unique (model : Assignment)
    (valid : GeneralNominalState.Models ctx.state model)
    (below : Subtype (model 2).1 (model 3).1)
    (missing : ∀ identity ∈ GeneralNominalState.sources ctx.state, identity ≠ lo ∧ identity ≠ hi)
    (fresh : GeneralNominalVersionedAllocation231.Fresh ctx.state registry childId [(0,2,3),(0,2,3)]) :
    GeneralNominalVersionedCandidates231.Unique registry ctx oldChild 1 [] := by
  have survivor : GeneralNominalVersionedCandidates231.Survivor registry ctx oldChild 1 [] :=
    ⟨known,leafDecl,List.mem_cons_of_mem _ (List.mem_singleton_self _),leafCheck,rfl,rfl,
      [(2,3),(2,3)],located ..,prepared model valid below missing fresh,by
        simp [GeneralNominalVersionedCandidates231.children,GeneralNominalVersionedFrame231.children,GeneralDictionaryEmissionPlans.children,
          GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
          GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll,leafDecl,GeneralNominalCenteredHeadAllocEncoding.declaration]⟩
  refine ⟨survivor,?_⟩
  intro key children found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases leaf_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

end Yulang.GeneralDictionaryMixedGround218Leaf235
