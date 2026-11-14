import Yulang.GeneralNominalCenteredModelExtension

/-! Finite syntactic frames for centered equations. Agreement is required only
on listed origin roots, endpoint names and centers, not the whole assignment. -/
namespace Yulang.GeneralNominalCenteredFrame179
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource observes_same)

variable {first last : Assignment}

def Agree (names : List Nat) (first last : Assignment) : Prop :=
  ∀ name ∈ names, first name = last name

 theorem observes_iff (origin : Origin) (same : first (originSource origin) = last (originSource origin)) (value) :
    Observes first origin value ↔ Observes last origin value :=
  ⟨fun h => observes_same h same,fun h => observes_same h same.symm⟩

 theorem head_iff (origin : Origin) (test : Test)
    (same : first (originSource origin) = last (originSource origin)) :
    GeneralNominalOriginTerms.Head first origin test ↔ GeneralNominalOriginTerms.Head last origin test := by
  unfold GeneralNominalOriginTerms.Head
  simp only [observes_iff origin same]

 theorem same_iff (a b : Origin)
    (one : first (originSource a) = last (originSource a))
    (two : first (originSource b) = last (originSource b)) :
    GeneralNominalOriginTerms.Same first a b ↔ GeneralNominalOriginTerms.Same last a b := by
  unfold GeneralNominalOriginTerms.Same
  simp only [observes_iff a one,observes_iff b two]

 def siteSources (site : Site roles) : List Nat :=
  (List.ofFn fun index => [ (site.occurrence.demand.arguments index).1,
    (site.occurrence.demand.arguments index).2,site.center index]).flatten

 theorem site_iff (site : Site roles) (same : Agree (siteSources site) first last) :
    site.Holds first ↔ site.Holds last := by
  have one index := same _ (by exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩ :
    (site.occurrence.demand.arguments index).1 ∈ siteSources site)
  have two index := same _ (by exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩ :
    (site.occurrence.demand.arguments index).2 ∈ siteSources site)
  have center index := same _ (by exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩ : site.center index ∈ siteSources site)
  simp only [Site.Holds,GeneralNominalCaptureMerges.Fits,one,two,center]

 def variableSources (plan : Plan roles) (entry : Use) : List Nat :=
  [originSource entry.origin,plan.binder entry.name,
    (GeneralNominalPacketSupport.capture plan.packet).outputs entry.name,
    ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1,
    ((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2]

 def schemaSources (plan : Plan roles) (schema : Schema) : List Nat :=
  schema.tests.map (fun test => originSource test.1) ++ schema.variables.flatMap (variableSources plan)

 theorem schema_iff (plan : Plan roles) (schema : Schema)
    (same : Agree (schemaSources plan schema) first last) :
    plan.SchemaHolds schema first ↔ plan.SchemaHolds schema last := by
  have tests entry (member : entry ∈ schema.tests) :
      GeneralNominalOriginTerms.Head first entry.1 entry.2 ↔ GeneralNominalOriginTerms.Head last entry.1 entry.2 :=
    head_iff _ _ (same _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)))
  have variables entry (member : entry ∈ schema.variables) :
      Agree (variableSources plan entry) first last := by
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,member,present⟩))
  unfold Plan.SchemaHolds
  apply and_congr
  · exact forall_congr' fun entry => forall_congr' fun member => tests entry member
  · apply forall_congr'; intro entry
    apply forall_congr'; intro member
    have root := variables entry member (originSource entry.origin) (by simp [variableSources])
    have binder := variables entry member (plan.binder entry.name) (by simp [variableSources])
    have output := variables entry member ((GeneralNominalPacketSupport.capture plan.packet).outputs entry.name) (by simp [variableSources])
    have lower := variables entry member (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1) (by simp [variableSources])
    have upper := variables entry member (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2) (by simp [variableSources])
    split
    · exact same_iff _ _ root binder
    · simp only [observes_iff entry.origin root,VariableHolds,GeneralNominalCaptureMerges.Fits,output,lower,upper]

 def captureNames (plan : Plan roles) : List Nat :=
  plan.packet.declaration.inputNames ++ plan.packet.declaration.requirements.flatMap
    (fun clause => GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs clause.arguments))

 theorem capture_mem (plan : Plan roles) (name : Nat) :
    name ∈ captureNames plan ↔ name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name := by
  simp [captureNames,GeneralNominalSharedCaptures.Needed]

 def captureSources (plan : Plan roles) : List Nat :=
  (captureNames plan).flatMap fun name =>
    [((GeneralNominalPacketSupport.capture plan.packet).inputs name).1,
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2,plan.binder name]

 def childSources (plan : Plan roles) : List Nat :=
  plan.packet.declaration.requirements.attach.flatMap fun clause =>
    let valid := plan.packet.checked.signature.2.2.2 clause.val clause.property
    siteSources (plan.childSite clause.val valid) ++ schemaSources plan (plan.schema (plan.childRequests clause.val valid))

 def equationSources (plan : Plan roles) : List Nat :=
  siteSources plan.input ++ captureSources plan ++ schemaSources plan plan.headSchema ++
    schemaSources plan (GeneralNominalPacketSupport.inputSchema plan.packet) ++
    schemaSources plan (GeneralNominalPacketSupport.namedSchema plan.packet) ++ childSources plan

 theorem equations_iff (plan : Plan roles) (same : Agree (equationSources plan) first last) :
    plan.Equations first ↔ plan.Equations last := by
  have input := site_iff plan.input (fun name member => same name (by simp [equationSources,member]))
  have head := schema_iff plan plan.headSchema (fun name member => same name (by simp [equationSources,member]))
  have ins := schema_iff plan (GeneralNominalPacketSupport.inputSchema plan.packet)
    (fun name member => same name (by simp [equationSources,member]))
  have named := schema_iff plan (GeneralNominalPacketSupport.namedSchema plan.packet)
    (fun name member => same name (by simp [equationSources,member]))
  have captures : Agree (captureSources plan) first last :=
    fun name member => same name (by simp [equationSources,member])
  unfold Plan.Equations
  apply and_congr input
  apply and_congr
  · apply forall_congr'; intro name
    apply forall_congr'; intro needed
    have mem := (capture_mem plan name).mpr needed
    have one := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).1)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    have two := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).2)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    have center := captures (plan.binder name)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    simp only [GeneralNominalCaptureMerges.Fits,one,two,center]
  apply and_congr head
  apply and_congr ins
  apply and_congr named
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have children : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources plan (plan.schema (plan.childRequests clause valid))) first last := by
    intro name present
    apply same
    have item : name ∈ childSources plan := List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [equationSources,item]
  exact and_congr (site_iff _ (fun name member => children name (List.mem_append_left _ member)))
    (schema_iff _ _ (fun name member => children name (List.mem_append_right _ member)))

/-- Actual finite ledger footprint, excluding the independent raw journal. -/
def ledgerSources (state : GeneralNominalCenteredSteps.State roles) : List Nat :=
  state.sites.flatMap siteSources ++ state.plans.flatMap equationSources

 theorem ledger_frame (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (ledgerSources state) first last)
    (valid : GeneralNominalCenteredSteps.Models state first)
    (raw : GeneralNominalSaturationState.Models state.erased.current last) :
    GeneralNominalCenteredSteps.Models state last := by
  refine ⟨raw,?_,?_⟩
  · intro site member
    apply (site_iff site ?_).mp (valid.2.1 site member)
    intro name present
    exact same name (List.mem_append_left _ (List.mem_flatMap.mpr ⟨site,member,present⟩))
  · intro plan member
    apply (equations_iff plan ?_).mp (valid.2.2 plan member)
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨plan,member,present⟩))

 theorem assign_agree (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (footprint : List Nat) (outside : ∀ index, names index ∉ footprint) :
    Agree footprint first (GeneralNominalCenteredModelExtension.assign first names values) := by
  intro name member
  exact (GeneralNominalCenteredModelExtension.assign_outside first names values
    (fun index equal => outside index (equal.symm ▸ member))).symm

 theorem equations_assign (plan : Plan roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ equationSources plan)
    (valid : plan.Equations first) :
    plan.Equations (GeneralNominalCenteredModelExtension.assign first names values) :=
  (equations_iff plan (assign_agree names values _ outside)).mp valid

/-- Fresh updates preserve the centered ledger when they avoid its finite
footprint. Raw-journal preservation remains an explicit separate obligation. -/
 theorem ledger_assign (state : GeneralNominalCenteredSteps.State roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ ledgerSources state)
    (valid : GeneralNominalCenteredSteps.Models state first)
    (raw : GeneralNominalSaturationState.Models state.erased.current
      (GeneralNominalCenteredModelExtension.assign first names values)) :
    GeneralNominalCenteredSteps.Models state
      (GeneralNominalCenteredModelExtension.assign first names values) :=
  ledger_frame state (assign_agree names values _ outside) valid raw

end Yulang.GeneralNominalCenteredFrame179
