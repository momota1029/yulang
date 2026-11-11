import Yulang.GeneralDictionaryVariableHeads
import Yulang.GeneralDictionaryVariableMaterialization
import Yulang.GeneralDictionaryVariableOrder

/-!
# Checked visible plans without a supplied head vector

One checked visible declaration supplies the positional head, associated RHSs
and complete canonical children. Only endpoint/target locations, source frames
and the selected key remain inputs. Unsupported heads or RHSs defer the whole
package; this operation neither selects candidates nor proves applicability.
-/
namespace Yulang.GeneralDictionaryHeadlessPlans
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralDictionaryEmissionPlans GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryVariableHeads (HeadlessInputs HeadDenotes)
open GeneralDictionaryVariableMaterialization (Materializes)
open GeneralSourceState (State)
variable {roles : Roles.RoleDecls} {state : State}

/-- Both packages are indexed by the same actual source demand. -/
structure Result (state : State) (root : Occurrence roles) where
  inputs : Inputs state root.demand
  plan : GeneralDictionaryVariablePlans.Result state root

def lookup (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) : Option (Result state root) :=
  (registry.declarations.attach.find? (fun declaration =>
    declaration.val.id == key && declaration.val.role == root.demand.role)).bind fun declaration =>
      if role : declaration.val.role = root.demand.role then
        (GeneralDictionaryVariableHeads.build declaration.val
          (checked.2 declaration.val declaration.property) role
          (frame.capture declaration.val.id) inputs).bind fun built =>
            (GeneralDictionaryVariablePlans.lookup registry checked frame root key built).map
              fun plan => ⟨built, plan⟩
      else none

/-- Operational decomposition, with the head built from the same visible key.
The independent semantic characterization is `lookup_exact` below. -/
theorem lookup_build_exact (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root) :
    lookup registry checked frame root key inputs = some result ↔
      ∃ declaration, ∃ present : declaration ∈ registry.declarations,
        ∃ role : declaration.role = root.demand.role,
        declaration.id = key ∧
        GeneralDictionaryVariableHeads.build declaration (checked.2 declaration present) role
          (frame.capture declaration.id) inputs = some result.inputs ∧
        GeneralDictionaryVariablePlans.lookup registry checked frame root key result.inputs = some result.plan := by
  unfold lookup
  cases found : registry.declarations.attach.find? (fun declaration =>
      declaration.val.id == key && declaration.val.role == root.demand.role) with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨declaration, present, role, identity, _, _⟩
        have absent := List.find?_eq_none.mp found ⟨declaration, present⟩ (by simp)
        simp only [identity, role, beq_self_eq_true, Bool.and_self, not_true_eq_false] at absent
  | some declaration =>
      have keys : declaration.val.id = key ∧ declaration.val.role = root.demand.role := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some found
      simp only [Option.bind_some, dite_eq_left keys.2]
      constructor
      · intro success
        obtain ⟨built, headBuilt, rest⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨plan, planBuilt, equal⟩ := Option.map_eq_some_iff.mp rest
        cases equal
        exact ⟨declaration.val, declaration.property, keys.2, keys.1, headBuilt, planBuilt⟩
      · rintro ⟨other, present, role, identity, headBuilt, planBuilt⟩
        have equal := declaration_key_unique registry checked declaration.val other
          declaration.property present (keys.1.trans identity.symm)
        subst other
        rw [headBuilt]
        simp only [Option.bind_some, planBuilt, Option.map_some]

/-- The existing whole-tree output builder accepts the computed Inputs. -/
theorem lookup_plan (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root)
    (found : lookup registry checked frame root key inputs = some result) :
    GeneralDictionaryVariablePlans.lookup registry checked frame root key result.inputs = some result.plan := by
  obtain ⟨_, _, _, _, _, plan⟩ := (lookup_build_exact registry checked frame root key inputs result).mp found
  exact plan

/-- Checked key uniqueness supplies precisely the universal visible-head premise
of `GeneralDictionaryVariableTransactions.Built.node`, without caller evidence. -/
theorem lookup_heads (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root)
    (found : lookup registry checked frame root key inputs = some result) :
    ∀ declaration ∈ registry.declarations,
      declaration.id = key → declaration.role = root.demand.role →
        GeneralDictionaryVariableHeads.heads registry.roles state root declaration
          (frame.capture declaration.id) result.inputs.head := by
  obtain ⟨original, present, role, identity, built, _⟩ :=
    (lookup_build_exact registry checked frame root key inputs result).mp found
  intro declaration member sameKey _
  have equal := declaration_key_unique registry checked original declaration present member
    (identity.trans sameKey.symm)
  subst declaration
  exact GeneralDictionaryVariableHeads.build_head_denotes original (checked.2 original present)
    role (frame.capture original.id) inputs result.inputs built

/-- Independent same-declaration semantics: no lookup/build success occurs here. -/
def MaterializesPlan (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root) : Prop :=
  ∃ declaration, ∃ present : declaration ∈ registry.declarations,
    declaration.id = key ∧ declaration.role = root.demand.role ∧
    result.inputs.lower = inputs.lower ∧ result.inputs.upper = inputs.upper ∧
    result.inputs.target = inputs.target ∧
    HeadDenotes declaration (frame.capture declaration.id) root.demand result.inputs.head ∧
    Materializes declaration (frame.capture declaration.id) result.inputs result.plan.located ∧
    result.plan.children = children frame root declaration (checked.2 declaration present)

/-- Exactness joins positional provenance and every associated output denotation
for one actual checked visible declaration, retaining all source locations. -/
theorem lookup_exact (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root) :
    lookup registry checked frame root key inputs = some result ↔
      MaterializesPlan registry checked frame root key inputs result := by
  rw [lookup_build_exact]
  constructor
  · rintro ⟨declaration, present, role, identity, built, plan⟩
    obtain ⟨lower, upper, target, head⟩ :=
      (GeneralDictionaryVariableHeads.build_exact declaration (checked.2 declaration present)
        role (frame.capture declaration.id) inputs result.inputs).mp built
    obtain ⟨other, member, sameKey, _, materialized, generated⟩ :=
      (GeneralDictionaryVariableMaterialization.plan_lookup_exact registry checked frame root key
        result.inputs result.plan).mp plan
    have equal := declaration_key_unique registry checked declaration other present member
      (identity.trans sameKey.symm)
    subst other
    exact ⟨declaration, present, identity, role, lower, upper, target, head, materialized, generated⟩
  · rintro ⟨declaration, present, identity, role, lower, upper, target, head, materialized, generated⟩
    refine ⟨declaration, present, role, identity, ?_, ?_⟩
    · exact (GeneralDictionaryVariableHeads.build_exact declaration (checked.2 declaration present)
        role (frame.capture declaration.id) inputs result.inputs).mpr ⟨lower, upper, target, head⟩
    · exact (GeneralDictionaryVariableMaterialization.plan_lookup_exact registry checked frame root key
        result.inputs result.plan).mpr ⟨declaration, present, identity, role, materialized, generated⟩

open GeneralRegistryReordering

/-- Reordering where clauses cannot affect positional head compilation. -/
theorem head_compile_reorders (order : DeclarationReorders first last)
    (capture : Capture) (index : Nat) :
    GeneralDictionaryVariableHeads.compileAt state first capture index =
      GeneralDictionaryVariableHeads.compileAt state last capture index := by
  rw [declarationReorders_update order]
  rfl

theorem head_build_reorders (order : DeclarationReorders first last)
    (one : DeclarationChecked constructors roles first)
    (two : DeclarationChecked constructors roles last)
    (firstRole : first.role = demand.role) (lastRole : last.role = demand.role)
    (capture : Capture) (inputs : HeadlessInputs state demand) :
    GeneralDictionaryVariableHeads.build first one firstRole capture inputs =
      GeneralDictionaryVariableHeads.build last two lastRole capture inputs := by
  unfold GeneralDictionaryVariableHeads.build
  simp only [head_compile_reorders order capture]

/-- The whole computed package transports unchanged across visible and where
reordering at fixed source identities, frame, selected key and locations. -/
theorem lookup_reorders_forward (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) (result : Result state root)
    (found : lookup ⟨constructors, roles, first⟩ one frame root key inputs = some result) :
    lookup ⟨constructors, roles, last⟩ two frame root key inputs = some result := by
  obtain ⟨declaration, present, role, identity, built, plan⟩ :=
    (lookup_build_exact _ one frame root key inputs result).mp found
  obtain ⟨other, member, reordered⟩ := reorders_visible order declaration present
  have otherRole := reordered.role.symm.trans role
  apply (lookup_build_exact _ two frame root key inputs result).mpr
  refine ⟨other, member, otherRole, reordered.id.symm.trans identity, ?_, ?_⟩
  · rw [← reordered.id,
      ← head_build_reorders reordered (one.2 declaration present) (two.2 other member)
        role otherRole]
    exact built
  · exact GeneralDictionaryVariableOrder.lookup_reorders_forward constructors roles first last
      one two order frame root key result.inputs result.plan plan

/-- Executable equality includes both success and deferred failure. This is not
candidate-order or final-state invariance. -/
theorem lookup_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) :
    lookup ⟨constructors, roles, first⟩ one frame root key inputs =
      lookup ⟨constructors, roles, last⟩ two frame root key inputs := by
  cases found : lookup ⟨constructors, roles, first⟩ one frame root key inputs with
  | some result =>
      exact (lookup_reorders_forward constructors roles first last one two order frame root key inputs result found).symm
  | none =>
      cases other : lookup ⟨constructors, roles, last⟩ two frame root key inputs with
      | none => rfl
      | some result =>
          have backward := lookup_reorders_forward constructors roles last first two one
            (GeneralRegistryChildOrder.reorders_symm order) frame root key inputs result other
          rw [found] at backward
          cases backward

/-- Failure means that this independently specified partial materialization has
no result, not that the role demand is semantically rejected. -/
theorem lookup_none_exact (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand) :
    lookup registry checked frame root key inputs = none ↔
      ∀ result, ¬ MaterializesPlan registry checked frame root key inputs result := by
  constructor
  · intro absent result materialized
    have found := (lookup_exact registry checked frame root key inputs result).mpr materialized
    rw [absent] at found
    cases found
  · intro absent
    cases found : lookup registry checked frame root key inputs with
    | none => rfl
    | some result => exact False.elim (absent result
        ((lookup_exact registry checked frame root key inputs result).mp found))

end Yulang.GeneralDictionaryHeadlessPlans
