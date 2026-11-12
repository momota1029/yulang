import Yulang.GeneralNominalSaturationExamples

/-! A source-formation obligation exposed by pure nominal-argument recurrence.
The full carrier and frozen context permit this state, while the existing K2
predicate checks structural reached roots. No nominal body is unfolded here.
This is not asserted to be a reachable Yulang program state. -/
namespace Yulang.GeneralNominalProgressObstruction

open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationExamples
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open CommonNominalFullCarrier

abbrev base : GeneralSourceState.State where
  slots := 1
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := [(0,0)]
  heads_sound := by intro _ _ _ _ recorded; cases recorded
  intervals_sound := by
    intro assignment _ pair member
    have same := List.mem_singleton.mp member; subst pair; exact Common.subtype_refl _

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ recorded; cases recorded

abbrev descriptor : GeneralNominalState.Descriptor 1 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun _ => some descriptor
  catalogue := by intro _ d recorded; have same := Option.some.inj recorded; subst d; rfl
  bodies_opaque := by intros; rfl

abbrev body : CommonNominalFullGuardedClosure.Body 1 0 := fun _ => .nominal 0 [.inl (.inl 0)]
abbrev value := CommonNominalFullGuardedClosure.instantiate body Fin.elim0 0
abbrev model : GeneralNominalCommonBridge.Assignment := fun _ => (value,Common.rowEmpty)

theorem equation : Equivalent value (nominal 0 [.inl value]) := by
  have proof := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 1)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,nominal] using proof

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ member; cases member
  · intro _ _ recorded; cases recorded
  · intro pair member
    have same := List.mem_singleton.mp member; subst pair; exact subtype_refl _
  · intro slot d recorded
    have same := Option.some.inj recorded; subst d
    exact ⟨[.inl value],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,equation⟩

theorem actual_self_edge : GeneralNominalMixedRecurrence.ActualArgument state 0 0 :=
  GeneralNominalMixedRecurrence.point_argument_edge state 0 0 descriptor rfl 0 rfl

theorem root_not_recursive : ¬ GeneralNominalMixedRecurrence.RecursAt state 0 :=
  GeneralNominalMixedRecurrence.nominal_not_recursive state 0 descriptor rfl

abbrev registry : Registry := ⟨constructors,roles,[display]⟩
abbrev context : Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root (invocation : Nat) : GeneralSourceDictionaries.Occurrence roles :=
  ⟨invocation,⟨0,fun _ => (0,0),[],by intro _ member; cases member⟩⟩
abbrev next (invocation : Nat) : Nat :=
  GeneralNominalAllocation.source state registry invocation (GeneralNominalAllocation.origin invocation 1 6 10 0)

theorem registry_checked : Checked registry :=
  ⟨by decide +kernel,by intro declaration member; have same := List.mem_singleton.mp member; subst declaration; exact display_checked⟩

private theorem query : GeneralNominalInspection.queries state context.interpretation display =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

private theorem located (invocation : Nat) : arguments context (root invocation) = some [(0,0)] := by
  change arguments context (root 0) = some [(0,0)]
  decide +kernel

private theorem calculated : report context display [(0,0)] = captured state 0 0 0 (0,0) :=
  report_exact context display 0 descriptor rfl 0 (0,0) rfl query

theorem exact_children (invocation : Nat) : GeneralNominalAllocation.children state registry (root invocation)
    display display_checked [(0,(0,0))] = [root (next invocation)] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,normalize,root,next]

private theorem ready (invocation : Nat) : ¬ GeneralNominalState.RootPending state (root invocation).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨descriptor,rfl⟩⟩

private theorem prepared (invocation : Nat) : Prepared registry context (root invocation) display display_checked := by
  have schema := GeneralNominalRecursiveExamples.display_schema registry context (root invocation) rfl display_checked [(0,0)]
  have branch := private_models context registry (root invocation) display 0 descriptor rfl 0 rfl (0,0) rfl query model state_models
  refine ⟨?_,?_,initial_fresh state registry invocation (by decide +kernel),[(0,0)],located invocation,?_,?_,model,branch.1,branch.2,?_⟩
  · refine ⟨rfl,?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive; exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · rw [calculated]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨(by intro output member; cases member),(by rw [schema])⟩
  · rw [schema]; exact GeneralNominalMaterialization.empty_models ..

theorem survivor (invocation : Nat) : Survivor registry context (root invocation) 1 [root (next invocation)] := by
  refine ⟨ready invocation,display,by simp,display_checked,rfl,rfl,[(0,0)],located invocation,prepared invocation,?_⟩
  rw [calculated]
  exact (exact_children invocation).symm

theorem selected (invocation : Nat) : GeneralNominalLocalBoundary.Local
    (GeneralNominalLocalBoundary.recursiveFields roles) registry context (root invocation)
    (.selected 1 [root (next invocation)]) := by
  refine .selected ⟨ready invocation,?_,?_,?_⟩ ⟨survivor invocation,?_⟩
  · rintro ⟨_,_,index,slot,_,cycle⟩
    have same : slot = 0 := Subsingleton.elim _ _; subst slot
    exact root_not_recursive cycle
  · rintro ⟨_,declaration,visible,_,_,_,bounds,found,visited,member,cycle⟩
    have same := List.mem_singleton.mp visible; subst declaration
    have same := Option.some.inj ((located invocation).symm.trans found); subst bounds
    rw [calculated] at member
    have same := List.mem_singleton.mp member; subst visited
    exact root_not_recursive cycle
  · rintro ⟨_,declaration,visible,_,_,_,unprepared⟩
    have same := List.mem_singleton.mp visible; subst declaration
    exact unprepared (prepared invocation)
  · intro key children surviving
    have original := surviving
    obtain ⟨_,declaration,visible,_,identity,_⟩ := surviving
    have same := List.mem_singleton.mp visible; subst declaration
    have same : key = 1 := identity.symm; subst key
    exact ⟨rfl,survivor_children_functional _ registry_checked _ _ _ _ _ original (survivor invocation)⟩

theorem child_not_accessible (invocation : Nat) :
    ¬ Acc (CommonRoleOutermostResolver.Child
      (GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles) registry context)) (root invocation) := by
  intro accessible
  have impossible : ∀ request, Acc (CommonRoleOutermostResolver.Child
      (GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles) registry context)) request →
      ∀ n, request = root n → False := by
    intro request h
    induction h with
    | intro request below ih =>
      intro n equal
      subst request
      exact ih (root (next n)) ⟨1,[root (next n)],selected n,List.mem_singleton_self _⟩ (next n) rfl
  exact impossible _ accessible invocation rfl

end Yulang.GeneralNominalProgressObstruction
