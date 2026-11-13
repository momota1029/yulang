import Yulang.GeneralNominalActualAgreedBoundary

/-! Explicit names for actual interval arguments. Endpoint matching is unchanged.
The extra equations constrain names in the general carrier, without choosing a
closed type or changing an interval to a point. -/
namespace Yulang.GeneralNominalCenters
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes Test)
open GeneralNominalMaterialization (Schema Mode)
open CommonNominalFullCarrier

/-- This record can decorate a role argument or an invariant nominal slot at
any depth. The bound pair remains available to the endpoint inspector. -/
structure Argument where
  endpoints : GeneralSourceState.Interval
  center : Nat

def Argument.Holds (argument : Argument) (model : Assignment) : Prop :=
  GeneralNominalCaptureMerges.Fits model argument.endpoints (model argument.center).1

structure NominalArgument where
  argument : Argument
  origin : Origin

def NominalArgument.Holds (argument : NominalArgument) (model : Assignment) : Prop :=
  argument.argument.Holds model ∧
    GeneralNominalOriginTerms.Same model argument.origin (.source argument.argument.center)

structure Site (roles : Roles.RoleDecls) where
  occurrence : Occurrence roles
  center : Fin (roles occurrence.demand.role).arity → Nat

def Site.Holds (site : Site roles) (model : Assignment) : Prop :=
  ∀ index, GeneralNominalCaptureMerges.Fits model
    (site.occurrence.demand.arguments index) (model (site.center index)).1

def Site.PointNames (site : Site roles) : Prop :=
  ∀ index, (site.occurrence.demand.arguments index).1 = (site.occurrence.demand.arguments index).2 →
    site.center index = (site.occurrence.demand.arguments index).1

def Site.observed (site : Site roles) : GeneralNominalDemandMerging.Site roles where
  occurrence := site.occurrence
  inputs := List.ofFn fun index => some (.source (site.center index))
  arity := List.length_ofFn

def fresh (seed invocation declaration purpose owner position : Nat) : Nat :=
  GeneralNominalIdentities.source seed (invocation,declaration,purpose,owner,position)

def rootSite (seed : Nat) (root : Occurrence roles) : Site roles where
  occurrence := root
  center := fun index => let bounds := root.demand.arguments index
    if bounds.1 = bounds.2 then bounds.1 else fresh seed root.identity 0 7 index.val 0

theorem point_center (seed : Nat) (root : Occurrence roles)
    (index : Fin (roles root.demand.role).arity)
    (point : (root.demand.arguments index).1 = (root.demand.arguments index).2) :
    (rootSite seed root).center index = (root.demand.arguments index).1 := by
  simp [rootSite,point]

theorem nonpoint_center_fresh (seed : Nat) (root : Occurrence roles)
    (index : Fin (roles root.demand.role).arity)
    (nonpoint : (root.demand.arguments index).1 ≠ (root.demand.arguments index).2) :
    seed < (rootSite seed root).center index := by
  simpa [rootSite,nonpoint,fresh] using GeneralNominalIdentities.source_above_seed seed
    (root.identity,0,7,index.val,0)

theorem point_root_holds (seed : Nat) (root : Occurrence roles)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (model : Assignment) : (rootSite seed root).Holds model := by
  intro index
  rw [point_center seed root index (point index)]
  change Subtype _ _ ∧ Subtype _ (model (root.demand.arguments index).2).1
  exact ⟨subtype_refl _,by rw [← point index]; exact subtype_refl _⟩

theorem observed_total (site : Site roles) : none ∉ site.observed.inputs := by
  simp [Site.observed]

theorem observed_holds (site : Site roles) (model : Assignment) (valid : site.Holds model) :
    GeneralNominalSaturationState.SiteHolds site.observed model := by
  intro index origin recorded
  have equal : origin = .source (site.center index) := by
    change (List.ofFn (fun index => some (Origin.source (site.center index))))[index.val]? = some (some origin) at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact (Option.some.inj (Option.some.inj recorded)).symm
    · contradiction
  subst origin
  exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact valid index⟩

/-- Refresh and recovery change observations, never the stored actual name. -/
def recover (_state : GeneralNominalSaturationState.State roles) (site : Site roles) : Site roles := site

theorem recover_center (state : GeneralNominalSaturationState.State roles) (site : Site roles) :
    (recover state site).center = site.center := rfl

def SameInputs (models : Assignment → Prop) (first last : Site roles) : Prop :=
  GeneralNominalDemandMerging.SameInputs models first.observed last.observed

theorem same_name (models : Assignment → Prop) (identity : Nat) :
    GeneralNominalDemandMerging.SameOrigin models (.source identity) (.source identity) :=
  GeneralNominalDemandMerging.source_same models identity

structure Plan (roles : Roles.RoleDecls) where
  packet : Packet roles
  input : Site roles
  input_exact : input.occurrence = packet.site.occurrence

def Plan.binder (plan : Plan roles) (name : Nat) : Nat :=
  let packet := plan.packet
  let capture := GeneralNominalPacketSupport.capture packet
  if name ∈ packet.declaration.outputNames then capture.outputs name
  else if (capture.inputs name).1 = (capture.inputs name).2 then (capture.inputs name).1
  else fresh packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 8 name 0

def Plan.schema (plan : Plan roles) (requests : List GeneralNominalMaterialization.Request) : Schema :=
  GeneralNominalMaterialization.generated plan.packet.context.state plan.packet.context.interpretation requests

/-- Actual occurrences all refer to the same binder name; endpoint occurrences
retain the old lower/upper interpretation. -/
def Plan.SchemaHolds (plan : Plan roles) (schema : Schema) (model : Assignment) : Prop :=
  (∀ test ∈ schema.tests, GeneralNominalOriginTerms.Head model test.1 test.2) ∧
  (∀ entry ∈ schema.variables,
    if entry.mode = .actual then
      GeneralNominalOriginTerms.Same model entry.origin (.source (plan.binder entry.name))
    else (∃ actual, Observes model entry.origin actual) ∧
      ∀ actual, Observes model entry.origin actual → GeneralNominalMaterialization.VariableHolds
        plan.packet.declaration (GeneralNominalPacketSupport.capture plan.packet) model entry.name entry.mode actual)

def Plan.headSchema (plan : Plan roles) : Schema :=
  GeneralNominalMaterialization.schemas
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
    (fun index => .source ((List.ofFn plan.input.center)[index]?.getD 0)) .actual 0

/-- Bare uses forward the binder name. Compounds get a separate name and an
actual-mode equation connecting that name to the whole compound. -/
def Plan.emittedCenter (plan : Plan roles) (clause position : Nat)
    (pattern : GeneralDeclarationPatterns.Pattern) : Nat :=
  match GeneralDeclarationPatterns.normalize pattern with
  | .var name => plan.binder name
  | _ => fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id 9 clause position

def Plan.childSite (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) : Site roles where
  occurrence := GeneralNominalFeedbackSites.clauseChild plan.packet clause valid
  center := fun index => plan.emittedCenter clause.id index.val
    (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt))

def Plan.childRequests (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    List GeneralNominalMaterialization.Request :=
  List.ofFn fun index : Fin (roles clause.role).arity =>
    ⟨clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt),
      (plan.childSite clause valid).center index,.actual⟩

def Plan.emitted (plan : Plan roles) : List (Site roles) :=
  plan.packet.declaration.requirements.attach.map fun clause =>
    plan.childSite clause.val (plan.packet.checked.signature.2.2.2 clause.val clause.property)

def Plan.Equations (plan : Plan roles) (model : Assignment) : Prop :=
  plan.input.Holds model ∧
  (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (plan.binder name)).1) ∧
  plan.SchemaHolds plan.headSchema model ∧
  plan.SchemaHolds (GeneralNominalPacketSupport.inputSchema plan.packet) model ∧
  plan.SchemaHolds (GeneralNominalPacketSupport.namedSchema plan.packet) model ∧
  (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
    (plan.childSite clause valid).Holds model ∧ plan.SchemaHolds (plan.schema (plan.childRequests clause valid)) model)

def Plan.Holds (plan : Plan roles) (model : Assignment) : Prop :=
  plan.packet.Holds model ∧ plan.Equations model

/-- The centered certificate is relative to the centered packet semantics. It
is deliberately distinct from the old certificate over raw packet models. -/
def Usable (plan : Plan roles) (name : Nat) (origin : Origin) : Prop :=
  origin = .source (plan.binder name) ∧ ∀ model, plan.Holds model →
    (∃ actual, Observes model origin actual) ∧ ∀ actual, Observes model origin actual →
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name) actual

def CaptureAgreement (plan : Plan roles) (name : Nat) (origin : Origin) : Prop :=
  ∀ model, plan.Holds model → ∀ entry ∈ plan.headSchema.variables,
    entry.name = name → entry.mode = .actual → GeneralNominalOriginTerms.Same model entry.origin origin

theorem capture_agreement (plan : Plan roles) (name : Nat) :
    CaptureAgreement plan name (.source (plan.binder name)) := by
  intro model valid entry member same actual
  have agreement := valid.2.2.2.1.2 entry member
  simpa only [actual,ite_true,same] using agreement

def InputCoherence (plan : Plan roles) : Prop :=
  ∀ model, plan.Holds model → ∀ entry ∈ (GeneralNominalPacketSupport.inputSchema plan.packet).variables,
    entry.mode = .actual → GeneralNominalOriginTerms.Same model entry.origin (.source (plan.binder entry.name))

theorem input_coherence (plan : Plan roles) : InputCoherence plan := by
  intro model valid entry member actual
  have agreement := valid.2.2.2.2.1.2 entry member
  simpa only [actual,ite_true] using agreement

def GenerationGuard (plan : Plan roles) : Prop :=
  ∀ name, GeneralNominalSharedCaptures.Needed plan.packet name → ∃ origin, Usable plan name origin ∧ CaptureAgreement plan name origin

theorem generation_guard (plan : Plan roles) : GenerationGuard plan := by
  intro name needed
  refine ⟨.source (plan.binder name),⟨rfl,?_⟩,capture_agreement plan name⟩
  intro model valid
  exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact valid.2.2.1 name (Or.inr needed)⟩

def ProvenanceGap (plan : Plan roles) : Prop := ¬ GenerationGuard plan

theorem no_provenance_gap (plan : Plan roles) : ¬ ProvenanceGap plan :=
  fun missing => missing (generation_guard plan)

theorem repeated_use (plan : Plan roles) (schema : Schema) (model : Assignment)
    (valid : plan.SchemaHolds schema model)
    (first last : GeneralNominalMaterialization.Use)
    (one : first ∈ schema.variables) (two : last ∈ schema.variables)
    (same : first.name = last.name) (a : first.mode = .actual) (b : last.mode = .actual) :
    GeneralNominalOriginTerms.Same model first.origin last.origin := by
  have left := valid.2 first one
  have right := valid.2 last two
  simp only [a,ite_true] at left
  simp only [b,ite_true] at right
  rw [same] at left
  exact GeneralNominalOriginTerms.same_trans left (GeneralNominalOriginTerms.same_symm right)

theorem emitted_variable (plan : Plan roles) (clause position name : Nat) :
    plan.emittedCenter clause position (.var name) = plan.binder name := rfl

theorem repeated_emission (plan : Plan roles) (first last one two name : Nat) :
    plan.emittedCenter first one (.var name) = plan.emittedCenter last two (.var name) := rfl

theorem emitted_holds (plan : Plan roles) (model : Assignment) (valid : plan.Holds model)
    (site : Site roles) (member : site ∈ plan.emitted) : site.Holds model := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  exact (valid.2.2.2.2.2.2 clause.val clause.property _).1

theorem endpoints_unchanged (plan : Plan roles) :
    plan.input.occurrence.demand = plan.packet.site.occurrence.demand :=
  congrArg Occurrence.demand plan.input_exact

end Yulang.GeneralNominalCenters
