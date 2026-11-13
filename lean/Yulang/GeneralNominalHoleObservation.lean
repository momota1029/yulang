import Yulang.GeneralNominalHoleReadback
import Yulang.GeneralSourceK2Examples
import Yulang.GeneralNominalStructuralProjectionLaws

/-! An actual shared-Step refresh exposes a recursive source observation.
It preserves all models and the opaque source leaf. No hole is eliminated. -/
namespace Yulang.GeneralNominalHoleObservation
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralSourceStateExamples (roles loopState loopDemand loopModel)
open GeneralNormalizedObservation

abbrev unknownView : Snapshot loopState where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro index; exact Fin.elim0 index
  canonical := by intro index; exact Fin.elim0 index
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev constructors : GeneralDeclarationPatterns.Constructors := fun _ => none
abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun _ => false,by intro _ impossible; cases impossible⟩
abbrev registry : GeneralDeclarations.Registry := ⟨constructors,roles,[]⟩
abbrev snapshot (known : Bool) : GeneralNominalState.State :=
  GeneralNominalState.embed loopState (if known then GeneralSourceK2Examples.loopView else unknownView) constructors
abbrev context (known : Bool) : GeneralNominalCandidates.Context := ⟨snapshot known,interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨0,loopDemand⟩
abbrev start := GeneralNominalSupport.initial (context false) root
abbrev finish : Tracked roles := {start with current := regenerate start.current (context true)}

theorem checked : GeneralDeclarations.Checked registry := ⟨by simp,by intro _ impossible; cases impossible⟩

theorem source : GeneralNominalSourceFormation.InitialSource registry (context false) root := by
  refine ⟨rfl,⟨rfl,by intro _ _ impossible; cases impossible⟩,?_,?_,?_,rfl⟩
  · exact GeneralNominalState.linked_embed loopState unknownView constructors loopDemand
      GeneralSourceStateExamples.recursive_example.1
  · intro model valid index
    exact CommonNominalFullCarrier.subtype_refl _
  · intro identity member
    have zero : identity = 0 := by
      simpa [GeneralNominalState.sources,snapshot,GeneralNominalState.embed,loopState,List.ofFn_succ] using member
    subst identity
    exact Nat.zero_le _

theorem inhabited (known : Bool) : GeneralNominalState.Models (snapshot known)
    (GeneralNominalCommonBridge.lift loopModel) :=
  (GeneralNominalState.embed_models ..).mpr GeneralSourceStateExamples.recursive_example.2.1

theorem unknown : ¬ GeneralNominalState.Known (snapshot false) 0 := by
  rintro ⟨slot,same,head | ⟨descriptor,recorded⟩⟩
  · exact head rfl
  · cases recorded

theorem known : GeneralNominalState.Known (snapshot true) 0 :=
  ⟨0,rfl,Or.inl (by simp [Snapshot.graph,Head.node])⟩

def refines : GeneralNominalRefinements.Refines (snapshot false) (snapshot true) where
  base := (GeneralNominalRefinements.refl (snapshot false)).base
  heads := (GeneralNominalRefinements.refl (snapshot false)).heads
  nominals := by intro _ _ impossible; cases impossible
  ordinary := fun _ member => member
  known := by
    rintro identity ⟨slot,same,head | ⟨descriptor,recorded⟩⟩
    · exact False.elim (head rfl)
    · cases recorded
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

def refresh : GeneralNominalFeedbackSteps.Refresh start.current (context true) where
  refines := refines
  interpretation := rfl
  exact := fun _ valid => valid.1
  support := fun _ member => member

theorem actual_step : GeneralNominalSharedSteps.Step registry root start finish := by
  refine ⟨root,.root,.administrative root _ (.refresh root (context true) refresh 0 ?_ unknown known)⟩
  change 0 ∈ GeneralNominalState.sources (snapshot false)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨0,rfl⟩)))

theorem source_formed : GeneralNominalSharedSteps.SourceFormed registry root finish :=
  .update (.initial (context false) source) actual_step

theorem self_edge : GeneralSourceK2.Child (snapshot true).view 0 0 := by
  change GeneralSourceK2.Child GeneralSourceK2Examples.loopView 0 0
  exact ⟨0,(fun _ => 0),rfl,⟨0,by decide +kernel⟩,rfl⟩

theorem cycle : GeneralNominalCycleK2.RecursAt (snapshot true) 0 :=
  Or.inl ⟨0,Or.inl self_edge,.nil _⟩

/-- The exposed graph substitution still uses the original hole. It cannot
be an elimination into the empty set of remaining holes. -/
abbrev exposed : GeneralNominalOriginTerms.Expr Nat :=
  .node (.structural (.record [7])) (fun _ => .leaf 0)

theorem still_uses_hole : 0 ∈ exposed.leaves := by
  simp [GeneralNominalOriginTerms.Expr.leaves,GeneralNominalOriginTerms.arity,
    Shape.arity,List.ofFn_succ]

theorem not_elimination : ¬ (∀ name ∈ exposed.leaves, name ∈ ([] : List Nat)) :=
  fun closed => List.not_mem_nil (closed 0 still_uses_hole)

theorem exposed_readback : GeneralNominalHoleReadback.Over (Models finish.current) [.source 0] (.source 0)
    (exposed.bind (fun name => .leaf (.source name))) := by
  constructor
  · intro model valid
    have baseValid : GeneralNominalCommonBridge.Models loopState model := valid.1.1
    have equation : CommonNominalFullCarrier.Equivalent (model 0).1
        (CommonNominalFullCarrier.required 7 (model 0).1) :=
      baseValid.2.1 0 (.required 7 (.var 0)) rfl
    have shape : CommonNominalFullCarrier.Equivalent (model 0).1
        (GeneralNominalRecursiveInspection.shapeValue (.record [7]) [(model 0).1]) := by
      exact (GeneralNominalStructuralProjectionLaws.singleton_shape 7 (model 0).1).symm ▸ equation
    refine ⟨⟨⟨_,.source 0⟩,?_⟩,?_⟩
    · intro value seen
      cases seen
      exact ⟨[(model 0).1],rfl,shape⟩
    · intro index
      have zero : index.val = 0 := by have small := index.isLt; change index.val < 1 at small; omega
      change GeneralNominalOriginTerms.Same model
        (.structural (.source 0) (.record [7]) index.val) (.source 0)
      rw [zero]
      refine ⟨⟨_,.structural (.source 0) rfl shape rfl⟩,⟨_,.source 0⟩,?_⟩
      intro value other seen source
      cases source
      exact GeneralNominalStructuralProjectionLaws.record_observation model (.source 0) 7 value _
        (by intro value seen; cases seen; exact equation) seen
  · intro origin member
    simpa [GeneralNominalOriginTerms.Expr.bind,GeneralNominalOriginTerms.Expr.leaves,
      GeneralNominalOriginTerms.arity,Shape.arity,List.ofFn_succ] using member

theorem opaque_leaf_preserved :
    GeneralNominalHoleReadback.Over (Models finish.current) [.source 0] (.source 0) (.leaf (.source 0)) :=
  GeneralNominalHoleReadback.step_preserves actual_step
    (GeneralNominalHoleReadback.identity_leaf (List.mem_singleton_self _))

theorem empty_registry_accessible {roles : Roles.RoleDecls} {registry : GeneralDeclarations.Registry}
    {root : GeneralSourceDictionaries.Occurrence roles} {state : Tracked roles}
    (empty : registry.declarations = []) (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    Acc (fun next current => GeneralNominalSharedSteps.Step registry root current next) state := by
  apply GeneralNominalSharedBudget.accessible_of_signature_cover (formed := formed)
  refine ⟨[],?_⟩
  intro current path packet support generated enabled novel guard
  have member := enabled.1.2.2.2.1
  rw [empty] at member
  cases member

theorem accessible : Acc (fun next current => GeneralNominalSharedSteps.Step registry root current next) start :=
  empty_registry_accessible rfl (.initial (context false) source)

end Yulang.GeneralNominalHoleObservation
