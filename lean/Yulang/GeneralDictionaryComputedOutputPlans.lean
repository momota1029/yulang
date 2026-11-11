import Yulang.GeneralDictionaryBinderLocations
import Yulang.GeneralDictionaryPlannedOutputs
import Yulang.GeneralDictionaryTransactions

/-!
# Checked visible declarations supply computed dictionary output terms

One key/role lookup supplies both the complete canonical child plan and all
localized explicit output-binder RHSs. No caller supplies an output vector or
an arbitrary output interpretation. The remaining head predicate cannot inspect
outputs. Resolved frames, head terms, locations and selected keys remain inputs.
Failure means deferred materialization, never semantic role rejection.
-/
namespace Yulang.GeneralDictionaryComputedOutputPlans
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralDictionaryEmissionPlans GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs build)
open GeneralDictionaryOutputBinderTerms (Interpreted)
open GeneralDictionaryPlannedEvidence (TermInstances)
open GeneralDictionaryTransactions (Frames)
open GeneralSourceState (State)
open Core.PresenceGeneration (TyTerm)

variable {roles : Roles.RoleDecls} {state : State}

/-- Only the unfinished head interpretation remains externally supplied. -/
abbrev HeadInstances (roles : Roles.RoleDecls) (state : State) :=
  (root : Occurrence roles) → Declaration → Capture →
    (Fin (roles root.demand.role).arity → TyTerm (Fin state.slots)) → Prop

structure Result (state : State) (root : Occurrence roles) where
  children : List (Occurrence roles)
  located : Located state root.demand

/-- The same actual declaration supplies key, role, head and output meaning. -/
def Terms (registry : Registry) (frames : Frames registry.roles)
    (heads : HeadInstances registry.roles state) : TermInstances registry.roles state :=
  fun root key located => ∃ declaration, declaration ∈ registry.declarations ∧
    declaration.id = key ∧ declaration.role = root.demand.role ∧
    heads root declaration ((frames root).capture declaration.id) located.head ∧
    Interpreted declaration ((frames root).capture declaration.id) located

def lookup (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) : Option (Result state root) :=
  (registry.declarations.attach.find? (fun declaration =>
    declaration.val.id == key && declaration.val.role == root.demand.role)).bind
      (fun declaration =>
        (build declaration.val (frame.capture declaration.val.id) inputs).map fun located =>
          ⟨children frame root declaration.val (checked.2 declaration.val declaration.property), located⟩)

/-- The lookup succeeds precisely when the matching actual declaration builds
the package. This characterization keeps partial build success explicit. -/
theorem lookup_exact (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) (result : Result state root) :
    lookup registry checked frame root key inputs = some result ↔
      ∃ declaration, ∃ present : declaration ∈ registry.declarations,
        declaration.id = key ∧ declaration.role = root.demand.role ∧
        build declaration (frame.capture declaration.id) inputs = some result.located ∧
        result.children = children frame root declaration (checked.2 declaration present) := by
  unfold lookup
  cases found : registry.declarations.attach.find? (fun declaration =>
      declaration.val.id == key && declaration.val.role == root.demand.role) with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨declaration, present, identity, role, _, _⟩
        have absent := List.find?_eq_none.mp found ⟨declaration, present⟩ (by simp)
        simp only [identity, role, beq_self_eq_true, Bool.and_self, not_true_eq_false] at absent
  | some declaration =>
      have keys : declaration.val.id = key ∧ declaration.val.role = root.demand.role := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some found
      constructor
      · intro success
        obtain ⟨located, built, equal⟩ := Option.map_eq_some_iff.mp success
        cases equal
        exact ⟨declaration.val, declaration.property, keys.1, keys.2, built, rfl⟩
      · rintro ⟨other, present, identity, role, built, generated⟩
        have equal := declaration_key_unique registry checked declaration.val other
          declaration.property present (keys.1.trans identity.symm)
        subst other
        simp only [Option.bind_some, built, Option.map_some]
        cases result
        simp only at generated
        cases generated
        rfl

/-- All non-output inputs, in particular the supplied head, are preserved. -/
theorem build_head (declaration : Declaration) (capture : Capture)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located) : located.head = inputs.head := by
  unfold build at built
  split at built
  · cases built; rfl
  · cases built

theorem lookup_plan (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) (result : Result state root)
    (found : lookup registry checked frame root key inputs = some result) :
    Plan registry checked frame root key result.children := by
  obtain ⟨declaration, present, identity, role, _, generated⟩ :=
    (lookup_exact registry checked frame root key inputs result).mp found
  exact ⟨declaration, present, identity, role, generated⟩

/-- The head premise is quantified only over the checked visible declaration
matching this key and role; outputs are generated by the successful lookup. -/
theorem lookup_terms (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (root : Occurrence registry.roles) (key : Nat) (inputs : Inputs state root.demand)
    (result : Result state root)
    (found : lookup registry checked (frames root) root key inputs = some result)
    (head : ∀ declaration ∈ registry.declarations,
      declaration.id = key → declaration.role = root.demand.role →
        heads root declaration ((frames root).capture declaration.id) inputs.head) :
    Terms registry frames heads root key result.located := by
  obtain ⟨declaration, present, identity, role, built, _⟩ :=
    (lookup_exact registry checked (frames root) root key inputs result).mp found
  refine ⟨declaration, present, identity, role, ?_, ?_⟩
  · rw [build_head declaration _ inputs result.located built]
    exact head declaration present identity role
  · exact GeneralDictionaryBinderLocations.build_interpreted declaration _ inputs result.located built

/-- Full associated provenance and the complete child plan refer to this very
same visible declaration. This is stronger than unrelated successful lookups. -/
theorem lookup_output_plan (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) (result : Result state root)
    (found : lookup registry checked frame root key inputs = some result) :
    ∃ declaration, ∃ _present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key
        (result.children, GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration root.demand) ∧
      Interpreted declaration (frame.capture declaration.id) result.located := by
  obtain ⟨declaration, present, identity, role, built, generated⟩ :=
    (lookup_exact registry checked frame root key inputs result).mp found
  refine ⟨declaration, present, identity, role, ?_, ?_⟩
  · exact ⟨declaration, present, identity, role, by rw [generated]⟩
  · exact GeneralDictionaryBinderLocations.build_interpreted declaration _ inputs result.located built

end Yulang.GeneralDictionaryComputedOutputPlans
