import Yulang.GeneralVersionedSelectedJointWrites312
import Yulang.GeneralDictionaryMatInputVariables201

set_option backward.isDefEq.respectTransparency false
/-! Forwarded where inputs and output-only target binders contribute
tautological rows, even for arbitrarily many ordered, nonleaf requirements.
Compound templates and newly computed outputs are intentionally distinct. -/
namespace Yulang.GeneralVersionedForwardedWrites312
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalVersionedFrame231 (binder capture frame clauseChild)
open GeneralNominalCenteredHeadMatSchemas (generated materialize Equation)
open GeneralNominalMaterialization (Request)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedRootWrites312 (whereRequests inner from_request)
open GeneralVersionedSelectedJointWrites312 (InternalReady)
open GeneralDictionaryMatTerminalAssembly200 (generated_holds)
open GeneralFiniteTypedWrites312 (reflexive symmetric transitive)
variable {roles : Roles.RoleDecls}

def Forwarded (d : Declaration) : Prop :=
  ∀ clause ∈ d.requirements,
    (∀ pattern ∈ clause.arguments, ∃ name, pattern = .var name ∧ name ∉ d.outputNames) ∧
    ∀ eq ∈ clause.outputs, ∃ name, eq.rhs = .var name ∧ name ∈ d.outputNames

theorem variable_request (p : Plan roles) (m : Assignment) (name : Nat) (mode)
    (target : Nat) (same : variables p m mode name = (m target).1) :
    (materialize p.packet.registry.constructors p.packet.context.interpretation
      ⟨.var name,target,mode⟩).Holds (variables p m) m := by
  intro eq inside
  change eq ∈ [⟨target,mode,.variable name⟩] at inside
  cases List.mem_singleton.mp inside
  change CommonNominalFullCarrier.Equivalent (m target).1 (variables p m mode name)
  rw [same]
  exact reflexive _

theorem child_redundant (p : Plan roles) (forwarded : Forwarded p.packet.declaration)
    (m : Assignment) (clause : Clause) (member : clause ∈ p.packet.declaration.requirements)
    (signature : clause.Signature roles) :
    (childSchema p clause signature).Holds (variables p m) m := by
  unfold childSchema
  apply generated_holds
  intro rq source
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp source
  let pat := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
  obtain ⟨name,bare,_⟩ := (forwarded clause member).1 pat (List.getElem_mem ..)
  change (materialize p.packet.registry.constructors p.packet.context.interpretation
    ⟨pat,(GeneralNominalVersionedFrame231.childSite p clause signature).center index,.actual⟩).Holds _ _
  have center : (GeneralNominalVersionedFrame231.childSite p clause signature).center index = binder p name := by
    change GeneralNominalVersionedFrame231.emittedCenter p clause.id index.val pat = _
    rw [bare]
    rfl
  rw [bare,center]
  apply variable_request
  unfold variables
  split <;> rfl

theorem emitted_redundant (p : Plan roles) (forwarded : Forwarded p.packet.declaration)
    (m : Assignment) :
    (generated p.packet.registry.constructors p.packet.context.interpretation (whereRequests p)).Holds
      (variables p m) m := by
  apply generated_holds
  intro rq found
  obtain ⟨emit,emitted,inside⟩ := List.mem_flatMap.mp found
  have posted := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity p.packet.declaration
    p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mpr emitted
  unfold GeneralDeclarationDemands.emitAll at posted
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp posted
  let clause := item.val
  have facts := forwarded clause item.property
  unfold GeneralNominalCenteredHeadMatSchemas.emissionRequests at inside
  rcases List.mem_append.mp inside with input|output
  · obtain ⟨arg,args,byArg⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp args
    let pat := clause.arguments[index.val]'(by
      rw [(p.packet.checked.signature.2.2.2 clause item.property).1]; exact index.isLt)
    obtain ⟨name,bare,notOutput⟩ := facts.1 pat (List.getElem_mem ..)
    let ends := GeneralDeclarationDemands.inputInterval (capture p.packet)
      (((frame p.packet).allocation p.packet.declaration.id clause).arguments index) pat
    change rq ∈ [⟨pat,ends.1,.lower⟩,⟨pat,ends.2,.upper⟩] at byArg
    have pair : ends = (capture p.packet).inputs name := by
      unfold ends
      rw [bare]
      rfl
    rw [bare,pair] at byArg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at byArg
    rcases byArg with rfl|rfl
    · apply variable_request
      simp only [variables,notOutput,ite_false]
    · apply variable_request
      simp only [variables,notOutput,ite_false]
  · obtain ⟨request,requestMember,rfl⟩ := List.mem_map.mp output
    obtain ⟨eq,eqMember,rfl⟩ := List.mem_map.mp requestMember
    obtain ⟨name,bare,named⟩ := facts.2 eq eqMember
    change (materialize p.packet.registry.constructors p.packet.context.interpretation
      ⟨eq.rhs,GeneralDeclarationDemands.outputTarget p.packet.declaration (capture p.packet)
        ((frame p.packet).allocation p.packet.declaration.id clause).outputs eq,.actual⟩).Holds _ _
    have target := GeneralDeclarationDemands.generated_output_target p.packet.declaration (capture p.packet)
      ((frame p.packet).allocation p.packet.declaration.id clause).outputs eq name named bare
    rw [target,bare]
    apply variable_request
    simp only [variables,binder,named,ite_true]

theorem internal (s : State roles) (effect : Effect roles) (forwarded : Forwarded effect.plan.packet.declaration) :
    InternalReady s effect names := by
  intro m _ _ _ _
  have fixed : ∀ row ∈ GeneralVersionedRootWrites312.internalRows effect.plan m,
      GeneralFiniteTypedWrites312.Holds m row := by
    intro row member
    obtain ⟨eq,eqMember,rfl⟩ := List.mem_map.mp member
    change eq.Holds (variables effect.plan m) m
    rcases List.mem_append.mp eqMember with whereEq|child
    · exact emitted_redundant effect.plan forwarded m eq whereEq
    · obtain ⟨clause,_,prior⟩ := List.mem_flatMap.mp child
      exact child_redundant effect.plan forwarded m clause.val clause.property _ eq prior
  refine ⟨?_,fun row present _ => fixed row present⟩
  intro a first b last same _
  have x := fixed a first
  have y := fixed b last
  unfold GeneralFiniteTypedWrites312.Holds at x y
  rw [same] at x
  exact transitive (symmetric x) y

end Yulang.GeneralVersionedForwardedWrites312
