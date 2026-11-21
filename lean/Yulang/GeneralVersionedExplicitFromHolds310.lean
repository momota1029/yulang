import Yulang.GeneralVersionedOutputHandoff310

set_option backward.isDefEq.respectTransparency false
/-! An explicit equation in a current packet is already checked by Outputs.
Do not re-assume its live class equation at the packet's own request. For
alias-only requests, an output with the same name and class equality are
separate obligations; defaults are not in this explicit-emission argument. -/
namespace Yulang.GeneralVersionedExplicitFromHolds310
open GeneralDeclarations GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalCenteredHeadMatEffects (compileBody bodyVariables BodyHolds)
open GeneralDictionaryAssociatedProvenance (Supplies lookup lookup_exact)
open GeneralDictionaryDefaultEvidence204 (OutputWitness)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalVersionedPlans231 (Outputs Holds emittedRequests)
open GeneralNominalMaterialization (rootRequests)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {m : Assignment} {plan : Plan roles} {o : GeneralSourceState.Output}

theorem emits {e : Equation}
    (requested : o ∈ plan.packet.site.occurrence.demand.outputs)
    (provided : e ∈ plan.packet.declaration.associated) (named : e.name = o.name) :
    (⟨e.rhs,o.target,.actual⟩ : GeneralNominalMaterialization.Request) ∈ emittedRequests plan.packet := by
  have found := (lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 o.name
    (.explicit e)).mpr (.explicit e provided named)
  unfold lookup at found
  generalize eq : plan.packet.declaration.associated.find? (fun rhs => rhs.name == o.name) = result at found
  cases result with
  | none => simp at found
  | some rhs =>
    have same : rhs = e := by simpa only [Option.some.injEq,GeneralDictionaryAssociatedProvenance.Body.explicit.injEq] using found
    subst rhs
    apply List.mem_append_left _
    unfold rootRequests
    apply List.mem_flatMap.mpr
    refine ⟨o,requested,?_⟩
    rw [eq]
    exact List.mem_singleton_self _

theorem evaluated {e : Equation}
    (requested : o ∈ plan.packet.site.occurrence.demand.outputs)
    (provided : e ∈ plan.packet.declaration.associated) (named : e.name = o.name)
    {expression : Expr} (translated : compileBody plan (.explicit e) = some expression)
    (out : Outputs plan m) :
    Equivalent (m o.target).1 (value (bodyVariables plan m (.explicit e)) .actual expression) := by
  have computed := GeneralNominalCenteredHeadMatSchemas.generated_equation out
    (emits requested provided named) translated
  exact (GeneralNominalVersionedEffects231.actual_expression plan m expression) ▸ computed

theorem output {e : Equation}
    (requested : o ∈ plan.packet.site.occurrence.demand.outputs)
    (provided : e ∈ plan.packet.declaration.associated) (named : e.name = o.name)
    {expression : Expr} (translated : compileBody plan (.explicit e) = some expression)
    (held : Holds plan m) : OutputWitness plan m o := by
  refine ⟨.explicit e,.explicit e provided named,⟨expression,translated⟩,?_⟩
  intro equation member
  unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
  rw [translated] at member
  cases List.mem_singleton.mp member
  exact evaluated requested provided named translated held.2.2

def Explicit (plan : Plan roles) (outputs : List GeneralSourceState.Output) : Prop :=
  ∀ o ∈ outputs, ∃ e ∈ plan.packet.declaration.associated, e.name = o.name ∧
    ∃ expression, compileBody plan (.explicit e) = some expression

theorem certificate (current : Frame registry state root key plan)
    (ordered : children = GeneralNominalVersionedFrame231.children plan.packet)
    (held : Holds plan m) (explicit : Explicit plan root.demand.outputs) :
    Certificate registry state m root key children plan := by
  refine ⟨current,ordered,held,?_⟩
  intro out requested
  obtain ⟨e,provided,named,expression,translated⟩ := explicit out requested
  exact output (current.occurrence_eq.symm ▸ requested) provided named translated held

theorem recursive (current : Frame registry state root key plan)
    (ordered : children = GeneralNominalVersionedFrame231.children plan.packet)
    (held : Holds plan m) (explicit : Explicit plan root.demand.outputs)
    (kids : All₂ (Evidence registry state m) children dictionaries) :
    Evidence registry state m root (.node key dictionaries) :=
  GeneralNominalVersionedEvidence231.evidence_node ⟨_,certificate current ordered held explicit⟩ kids

/-- Requests inherited via alias are certified only when rooted by a same-name
    explicit local representative and actual same-model class equality. -/
theorem live_from_represented (current : Frame registry state root key plan)
    (held : Holds plan m) (explicit : Explicit plan root.demand.outputs)
    (sameName : ∀ target ∈ requests state root, ∃ localReq ∈ root.demand.outputs, localReq.name = target.name)
    (equal : EqualOutputs state root m) :
    GeneralNominalVersionedEffects231.ClassEffects state root plan m := by
  refine ⟨?_,equal⟩
  intro target found body unique
  obtain ⟨localReq,requested,name⟩ := sameName target found
  obtain ⟨e,provided,named,expression,translated⟩ := explicit localReq requested
  have actual := (lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1
    target.name (.explicit e)).mpr (.explicit e provided (named.trans name))
  have eq := Option.some.inj (unique.symm.trans actual)
  subst body
  have listed := GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site current.raw_recorded
    (by rw [current.occurrence_eq]; exact .refl _) (current.occurrence_eq.symm ▸ requested)
  have transport := equal target found localReq listed name.symm
  have localValue := evaluated (current.occurrence_eq.symm ▸ requested) provided named translated held.2.2
  apply (GeneralNominalVersionedEffects231.body_holds_iff ..).mpr
  intro equation member
  unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
  rw [translated] at member
  cases List.mem_singleton.mp member
  exact ⟨subtype_trans transport.1 localValue.1,subtype_trans localValue.2 transport.2⟩

end Yulang.GeneralVersionedExplicitFromHolds310
