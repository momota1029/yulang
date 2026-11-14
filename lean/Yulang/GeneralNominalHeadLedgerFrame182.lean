import Yulang.GeneralNominalCenteredHeadStepEffects
import Yulang.GeneralNominalModeLedger181

set_option backward.isDefEq.respectTransparency false

/-! Finite assignment support for historical and live class effects. The core
journal alone is not a frame for the successor model predicate: every recorded
snapshot and every current class request contributes additional support. -/
namespace Yulang.GeneralNominalHeadLedgerFrame182
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralNominalModeFrame181 (schemaSources schema_iff)
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects (Effect State Models)
variable {roles : Roles.RoleDecls} {first last : Assignment}

def headCaptureSources (plan : Plan roles) : List Nat :=
  plan.packet.declaration.inputNames.flatMap fun name =>
    [((GeneralNominalPacketSupport.capture plan.packet).inputs name).1,
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2,plan.binder name]

def headSources (plan : Plan roles) : List Nat :=
  siteSources plan.input ++ headCaptureSources plan ++ schemaSources plan plan.headSchema

noncomputable def outputSources (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) : List Nat :=
  schemaSources plan (outputSchema state root plan) ++ (requests state root).map (·.target)

noncomputable def heldSources (effect : Effect roles) : List Nat :=
  headSources effect.plan ++ outputSources effect.snapshot effect.plan.packet.site.occurrence effect.plan

noncomputable def effectSources (state : GeneralNominalCenteredSteps.State roles)
    (effect : Effect roles) : List Nat :=
  heldSources effect ++ outputSources state effect.plan.packet.site.occurrence effect.plan

noncomputable def ledgerSources (state : State roles) : List Nat :=
  state.effects.flatMap (effectSources state.core)

noncomputable def fullSources (state : State roles) : List Nat :=
  GeneralNominalModeLedger181.fullSources state.core ++ ledgerSources state

theorem head_iff (plan : Plan roles) (same : Agree (headSources plan) first last) :
    HeadEquations plan first ↔ HeadEquations plan last := by
  have input := site_iff plan.input (fun name member => same name (by simp [headSources,member]))
  have head := schema_iff plan plan.headSchema (fun name member => same name (by simp [headSources,member]))
  have captures : Agree (headCaptureSources plan) first last :=
    fun name member => same name (by simp [headSources,member])
  unfold HeadEquations
  apply and_congr input
  apply and_congr
  · apply forall_congr'; intro name
    apply forall_congr'; intro member
    have lower := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).1)
      (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
    have upper := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).2)
      (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
    have center := captures (plan.binder name)
      (List.mem_flatMap.mpr ⟨name,member,by simp⟩)
    simp only [GeneralNominalCaptureMerges.Fits,lower,upper,center]
  · exact head

theorem equal_outputs_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (same : Agree ((requests state root).map (·.target)) first last) :
    EqualOutputs state root first ↔ EqualOutputs state root last := by
  have target output (member : output ∈ requests state root) : first output.target = last output.target :=
    same _ (List.mem_map.mpr ⟨output,member,rfl⟩)
  unfold EqualOutputs
  apply forall_congr'; intro one
  apply forall_congr'; intro oneMember
  apply forall_congr'; intro two
  apply forall_congr'; intro twoMember
  rw [target one oneMember,target two twoMember]

theorem output_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (same : Agree (outputSources state root plan) first last) :
    OutputEquations state root plan first ↔ OutputEquations state root plan last :=
  and_congr
    (schema_iff plan _ (fun name member => same name (List.mem_append_left _ member)))
    (equal_outputs_iff state root (fun name member => same name (List.mem_append_right _ member)))

theorem holds_iff (effect : Effect roles) (same : Agree (heldSources effect) first last) :
    effect.Holds first ↔ effect.Holds last :=
  and_congr
    (head_iff effect.plan (fun name member => same name (List.mem_append_left _ member)))
    (output_iff effect.snapshot effect.plan.packet.site.occurrence effect.plan
      (fun name member => same name (List.mem_append_right _ member)))

theorem live_iff (state : GeneralNominalCenteredSteps.State roles) (effect : Effect roles)
    (same : Agree (outputSources state effect.plan.packet.site.occurrence effect.plan) first last) :
    effect.Live state first ↔ effect.Live state last := output_iff state _ effect.plan same

theorem effect_iff (state : GeneralNominalCenteredSteps.State roles) (effect : Effect roles)
    (same : Agree (effectSources state effect) first last) :
    (effect.Holds first ∧ effect.Live state first) ↔ (effect.Holds last ∧ effect.Live state last) :=
  and_congr
    (holds_iff effect (fun name member => same name (List.mem_append_left _ member)))
    (live_iff state effect (fun name member => same name (List.mem_append_right _ member)))

theorem models_iff (state : State roles) (same : Agree (fullSources state) first last) :
    Models state first ↔ Models state last := by
  apply and_congr
  · exact GeneralNominalModeLedger181.centered_models_iff state.core
      (fun name member => same name (List.mem_append_left _ member))
  · apply forall_congr'; intro effect
    apply forall_congr'; intro member
    apply effect_iff state.core effect
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨effect,member,present⟩))

theorem models_assign (state : State roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ fullSources state) (valid : Models state first) :
    Models state (GeneralNominalCenteredModelExtension.assign first names values) :=
  (models_iff state (GeneralNominalCenteredFrame179.assign_agree names values _ outside)).mp valid

end Yulang.GeneralNominalHeadLedgerFrame182
