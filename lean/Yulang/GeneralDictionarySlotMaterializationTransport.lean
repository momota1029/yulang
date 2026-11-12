import Yulang.GeneralDictionarySlotLocalizationTransport
import Yulang.GeneralDictionaryHeadlessPlans

/-!
# Exact successful head and output packages under slot transport

Reindex existing local packages while retaining the source capture, declaration,
root, key and canonical child occurrences. Success is preserved, not failure.
These results do not compare computed frames of different candidate contexts.
-/
namespace Yulang.GeneralDictionarySlotMaterializationTransport
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralSourceState (Demand)
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralDictionarySlotLocalizationTransport (headlessInputs head_denotesAt)
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryVariableHeads (HeadlessInputs HeadDenotes)
open GeneralDictionaryStateEquations (Located)
open Core.PresenceGeneration (TyTerm)
variable {before after : GeneralNominalState.State} {roles : Roles.RoleDecls}

def inputs (transport : Transport before after) (value : Inputs before.base demand) : Inputs after.base demand where
  lower := fun index => transport.embed (value.lower index)
  upper := fun index => transport.embed (value.upper index)
  head := fun index => (value.head index).rename transport.embed
  target := fun index => transport.embed (value.target index)
  arguments := by intro index; simpa only [transport.source] using value.arguments index
  targets := by intro index; simpa only [transport.source] using value.targets index

def located (transport : Transport before after) (value : Located before.base demand) : Located after.base demand where
  lower := fun index => transport.embed (value.lower index)
  upper := fun index => transport.embed (value.upper index)
  head := fun index => (value.head index).rename transport.embed
  target := fun index => transport.embed (value.target index)
  output := fun index => (value.output index).rename transport.embed
  arguments := by intro index; simpa only [transport.source] using value.arguments index
  targets := by intro index; simpa only [transport.source] using value.targets index

theorem head_denotes (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (demand : Demand roles)
    (head : Fin (roles demand.role).arity → TyTerm (Fin before.base.slots))
    (denoted : HeadDenotes declaration capture demand head) :
    HeadDenotes declaration capture demand (fun index => (head index).rename transport.embed) :=
  ⟨denoted.1, denoted.2.1, fun index => head_denotesAt transport declaration capture _ _ (denoted.2.2 index)⟩

theorem head_build_success (transport : Transport before after) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (demand : Demand roles) (sameRole : declaration.role = demand.role) (capture : Capture)
    (old : HeadlessInputs before.base demand) (result : Inputs before.base demand)
    (built : GeneralDictionaryVariableHeads.build declaration checked sameRole capture old = some result) :
    GeneralDictionaryVariableHeads.build declaration checked sameRole capture (headlessInputs transport old) =
      some (inputs transport result) := by
  obtain ⟨lower, upper, target, head⟩ :=
    (GeneralDictionaryVariableHeads.build_exact declaration checked sameRole capture old result).mp built
  apply (GeneralDictionaryVariableHeads.build_exact declaration checked sameRole capture _ _).mpr
  exact ⟨congrArg (fun f index => transport.embed (f index)) lower,
    congrArg (fun f index => transport.embed (f index)) upper,
    congrArg (fun f index => transport.embed (f index)) target,
    head_denotes transport declaration capture demand result.head head⟩

/-- Every repeated output occurrence retains its own explicit variable witness. -/
theorem materializes (transport : Transport before after) (declaration : Declaration) (capture : Capture)
    (old : Inputs before.base demand) (result : Located before.base demand)
    (built : GeneralDictionaryVariableMaterialization.Materializes declaration capture old result) :
    GeneralDictionaryVariableMaterialization.Materializes declaration capture
      (inputs transport old) (located transport result) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨lower, upper, head, target⟩ := built.1
    exact ⟨congrArg (fun f index => transport.embed (f index)) lower,
      congrArg (fun f index => transport.embed (f index)) upper,
      congrArg (fun f index => (f index).rename transport.embed) head,
      congrArg (fun f index => transport.embed (f index)) target⟩
  · intro index
    obtain ⟨slot, equal, denoted⟩ := built.2 index
    refine ⟨transport.embed slot, ?_, ?_⟩
    · change (result.output index).rename transport.embed = _
      rw [equal]; rfl
    · simpa only [transport.source] using denoted

theorem variable_build_success (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (unique : (declaration.associated.map Equation.name).Nodup)
    (old : Inputs before.base demand) (result : Located before.base demand)
    (built : GeneralDictionaryVariableTerms.build declaration capture old = some result) :
    GeneralDictionaryVariableTerms.build declaration capture (inputs transport old) = some (located transport result) :=
  (GeneralDictionaryVariableMaterialization.build_exact declaration capture unique _ _).mpr
    (materializes transport declaration capture old result
      ((GeneralDictionaryVariableMaterialization.build_exact declaration capture unique old result).mp built))

def planResult (transport : Transport before after) (result : GeneralDictionaryVariablePlans.Result before.base root) :
    GeneralDictionaryVariablePlans.Result after.base root := ⟨result.children, located transport result.located⟩

theorem plan_lookup_success (transport : Transport before after) (registry : Registry) (checked : Checked registry)
    (frame : GeneralDictionaryEmissionPlans.Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (old : Inputs before.base root.demand) (result : GeneralDictionaryVariablePlans.Result before.base root)
    (found : GeneralDictionaryVariablePlans.lookup registry checked frame root key old = some result) :
    GeneralDictionaryVariablePlans.lookup registry checked frame root key (inputs transport old) =
      some (planResult transport result) := by
  obtain ⟨declaration, member, identity, role, built, children⟩ :=
    (GeneralDictionaryVariableMaterialization.plan_lookup_exact registry checked frame root key old result).mp found
  exact (GeneralDictionaryVariableMaterialization.plan_lookup_exact registry checked frame root key _ _).mpr
    ⟨declaration, member, identity, role, materializes transport declaration _ old result.located built, children⟩

def headlessResult (transport : Transport before after) (result : GeneralDictionaryHeadlessPlans.Result before.base root) :
    GeneralDictionaryHeadlessPlans.Result after.base root :=
  ⟨inputs transport result.inputs, planResult transport result.plan⟩

/-- The same checked key produces the same canonical source children and the
exact renamed local head/output package at the target snapshot. -/
theorem headless_lookup_success (transport : Transport before after) (registry : Registry) (checked : Checked registry)
    (frame : GeneralDictionaryEmissionPlans.Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (old : HeadlessInputs before.base root.demand) (result : GeneralDictionaryHeadlessPlans.Result before.base root)
    (found : GeneralDictionaryHeadlessPlans.lookup registry checked frame root key old = some result) :
    GeneralDictionaryHeadlessPlans.lookup registry checked frame root key (headlessInputs transport old) =
      some (headlessResult transport result) := by
  obtain ⟨declaration, member, role, identity, built, planned⟩ :=
    (GeneralDictionaryHeadlessPlans.lookup_build_exact registry checked frame root key old result).mp found
  exact (GeneralDictionaryHeadlessPlans.lookup_build_exact registry checked frame root key _ _).mpr
    ⟨declaration, member, role, identity,
      head_build_success transport declaration (checked.2 declaration member) root.demand role _ old result.inputs built,
      plan_lookup_success transport registry checked frame root key result.inputs result.plan planned⟩

end Yulang.GeneralDictionarySlotMaterializationTransport
