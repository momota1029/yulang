import Yulang.GeneralNominalRegisteredReadback182
import Yulang.GeneralNominalModeLedger181

/-! Typed origins of every full-frame name. Raw historical support is retained
as its own case. An actual binder gives readback; a capture gives only Fits. -/
namespace Yulang.GeneralNominalSupportProvenance182
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalRegisteredReadback182 (SchemaLocation)
open GeneralNominalCommonBridge (Assignment)

inductive VariableSource (plan : Plan roles) (entry : Use) : Nat → Prop where
  | origin : VariableSource plan entry (originSource entry.origin)
  | binder (actual : entry.mode = .actual) : VariableSource plan entry (plan.binder entry.name)
  | output (nonactual : entry.mode ≠ .actual) :
      VariableSource plan entry ((GeneralNominalPacketSupport.capture plan.packet).outputs entry.name)
  | lower (nonactual : entry.mode ≠ .actual) :
      VariableSource plan entry (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).1)
  | upper (nonactual : entry.mode ≠ .actual) :
      VariableSource plan entry (((GeneralNominalPacketSupport.capture plan.packet).inputs entry.name).2)

theorem variable_iff (plan : Plan roles) (entry : Use) (name : Nat) :
    name ∈ GeneralNominalModeFrame181.variableSources plan entry ↔ VariableSource plan entry name := by
  constructor
  · intro member
    by_cases actual : entry.mode = .actual
    · simp only [GeneralNominalModeFrame181.variableSources,actual,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .origin
      · exact .binder actual
    · simp only [GeneralNominalModeFrame181.variableSources,actual,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact .origin
      · exact .output actual
      · exact .lower actual
      · exact .upper actual
  · intro source
    cases source with
    | origin => unfold GeneralNominalModeFrame181.variableSources; split <;> simp
    | binder actual => simp [GeneralNominalModeFrame181.variableSources,actual]
    | output nonactual | lower nonactual | upper nonactual =>
      simp [GeneralNominalModeFrame181.variableSources,nonactual]

inductive SchemaSource (plan : Plan roles) (schema : Schema) : Nat → Prop where
  | test (entry : Origin × Test) (member : entry ∈ schema.tests) :
      SchemaSource plan schema (originSource entry.1)
  | useSource (entry : Use) (member : entry ∈ schema.variables)
      (source : VariableSource plan entry name) : SchemaSource plan schema name

theorem schema_iff (plan : Plan roles) (schema : Schema) (name : Nat) :
    name ∈ GeneralNominalModeFrame181.schemaSources plan schema ↔ SchemaSource plan schema name := by
  constructor
  · intro member
    rcases List.mem_append.mp member with test | used
    · obtain ⟨entry,present,rfl⟩ := List.mem_map.mp test
      exact .test entry present
    · obtain ⟨entry,present,source⟩ := List.mem_flatMap.mp used
      exact .useSource entry present ((variable_iff plan entry name).mp source)
  · intro source
    cases source with
    | test entry present => exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,present,rfl⟩)
    | useSource entry present source =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,present,(variable_iff plan entry name).mpr source⟩)

inductive SiteSource (site : Site roles) : Nat → Prop where
  | lower (index : Fin (roles site.occurrence.demand.role).arity) :
      SiteSource site (site.occurrence.demand.arguments index).1
  | upper (index : Fin (roles site.occurrence.demand.role).arity) :
      SiteSource site (site.occurrence.demand.arguments index).2
  | center (index : Fin (roles site.occurrence.demand.role).arity) : SiteSource site (site.center index)

theorem site_iff (site : Site roles) (name : Nat) :
    name ∈ GeneralNominalCenteredFrame179.siteSources site ↔ SiteSource site name := by
  constructor
  · intro member
    obtain ⟨xs,present,within⟩ := List.mem_flatten.mp member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at within
    rcases within with rfl | rfl | rfl
    · exact .lower index
    · exact .upper index
    · exact .center index
  · intro source
    cases source with
    | lower index | upper index | center index =>
      exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

inductive CaptureSource (plan : Plan roles) : Nat → Prop where
  | lower (binder : Nat) (needed : binder ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet binder) :
      CaptureSource plan ((GeneralNominalPacketSupport.capture plan.packet).inputs binder).1
  | upper (binder : Nat) (needed : binder ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet binder) :
      CaptureSource plan ((GeneralNominalPacketSupport.capture plan.packet).inputs binder).2
  | binder (binder : Nat) (needed : binder ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet binder) :
      CaptureSource plan (plan.binder binder)

theorem capture_iff (plan : Plan roles) (name : Nat) :
    name ∈ GeneralNominalCenteredFrame179.captureSources plan ↔ CaptureSource plan name := by
  constructor
  · intro member
    obtain ⟨binder,present,within⟩ := List.mem_flatMap.mp member
    have needed := (GeneralNominalCenteredFrame179.capture_mem plan binder).mp present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at within
    rcases within with rfl | rfl | rfl
    · exact .lower binder needed
    · exact .upper binder needed
    · exact .binder binder needed
  · intro source
    cases source with
    | lower binder needed | upper binder needed | binder binder needed =>
      exact List.mem_flatMap.mpr ⟨binder,(GeneralNominalCenteredFrame179.capture_mem plan binder).mpr needed,by simp⟩

inductive PlanSource (plan : Plan roles) : Nat → Prop where
  | input (source : SiteSource plan.input name) : PlanSource plan name
  | capture (source : CaptureSource plan name) : PlanSource plan name
  | schema {schema : Schema} (location : SchemaLocation plan schema) (source : SchemaSource plan schema name) : PlanSource plan name
  | child (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
      (signature : clause.Signature roles) (source : SiteSource (plan.childSite clause signature) name) :
      PlanSource plan name

theorem plan_iff (plan : Plan roles) (name : Nat) :
    name ∈ GeneralNominalModeLedger181.equationSources plan ↔ PlanSource plan name := by
  constructor
  · intro member
    simp only [GeneralNominalModeLedger181.equationSources,List.mem_append] at member
    rcases member with ((((input | capture) | head) | ins) | named) | child
    · exact .input ((site_iff plan.input name).mp input)
    · exact .capture ((capture_iff plan name).mp capture)
    · exact .schema .head ((schema_iff plan _ name).mp head)
    · exact .schema .input ((schema_iff plan _ name).mp ins)
    · exact .schema .named ((schema_iff plan _ name).mp named)
    · obtain ⟨clause,_,member⟩ := List.mem_flatMap.mp child
      rcases List.mem_append.mp member with site | schema
      · exact .child clause.val clause.property _ ((site_iff _ name).mp site)
      · exact .schema (.child clause.val clause.property _) ((schema_iff plan _ name).mp schema)
  · intro source
    cases source with
    | input source => simp [GeneralNominalModeLedger181.equationSources,(site_iff _ name).mpr source]
    | capture source => simp [GeneralNominalModeLedger181.equationSources,(capture_iff _ name).mpr source]
    | schema location source =>
      have present := (schema_iff _ _ name).mpr source
      cases location with
      | head | input | named => simp [GeneralNominalModeLedger181.equationSources,present]
      | child clause member signature =>
        have child : name ∈ GeneralNominalModeLedger181.childSources plan :=
          List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,List.mem_append_right _ present⟩
        simp [GeneralNominalModeLedger181.equationSources,child]
    | child clause member signature source =>
      have child : name ∈ GeneralNominalModeLedger181.childSources plan :=
        List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,List.mem_append_left _ ((site_iff _ name).mpr source)⟩
      simp [GeneralNominalModeLedger181.equationSources,child]

inductive StateSource (state : State roles) : Nat → Prop where
  | raw (member : name ∈ GeneralNominalRawFrame179.rawSources state.erased.current) : StateSource state name
  | site (site : Site roles) (member : site ∈ state.sites) (source : SiteSource site name) : StateSource state name
  | plan (plan : Plan roles) (member : plan ∈ state.plans) (source : PlanSource plan name) : StateSource state name

theorem full_iff (state : State roles) (name : Nat) :
    name ∈ GeneralNominalModeLedger181.fullSources state ↔ StateSource state name := by
  constructor
  · intro member
    rcases List.mem_append.mp member with raw | ledger
    · exact .raw raw
    · rcases List.mem_append.mp ledger with site | plan
      · obtain ⟨site,present,within⟩ := List.mem_flatMap.mp site
        exact .site site present ((site_iff site name).mp within)
      · obtain ⟨plan,present,within⟩ := List.mem_flatMap.mp plan
        exact .plan plan present ((plan_iff plan name).mp within)
  · intro source
    cases source with
    | raw member => exact List.mem_append_left _ member
    | site site member source =>
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨site,member,(site_iff site name).mpr source⟩))
    | plan plan member source =>
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨plan,member,(plan_iff plan name).mpr source⟩))

/-- This specific provenance carries an actual-origin equation, not only bounds. -/
def ActualBinder (state : State roles) (name : Nat) (origin : Origin) : Prop :=
  ∃ plan ∈ state.plans, ∃ schema, SchemaLocation plan schema ∧
    ∃ entry ∈ schema.variables, entry.mode = .actual ∧ plan.binder entry.name = name ∧ entry.origin = origin

theorem actual_member (source : ActualBinder state name origin) :
    name ∈ GeneralNominalModeLedger181.fullSources state := by
  obtain ⟨plan,member,schema,location,entry,present,actual,rfl,rfl⟩ := source
  exact (full_iff state _).mpr (.plan plan member (.schema location (.useSource entry present (.binder actual))))

theorem actual_same (valid : Models state model) (source : ActualBinder state name origin) :
    GeneralNominalOriginTerms.Same model origin (.source name) := by
  obtain ⟨plan,member,schema,location,entry,present,actual,rfl,rfl⟩ := source
  exact GeneralNominalRegisteredReadback182.registered_actual plan member valid location entry present actual

theorem actual_readback (valid : Models state model) (source : ActualBinder state name origin)
    (value : CommonNominalFullCarrier.Ty) (seen : Observes model origin value) :
    CommonNominalFullCarrier.Equivalent value (model name).1 :=
  (actual_same valid source).2.2 value (model name).1 seen (.source _)

end Yulang.GeneralNominalSupportProvenance182
