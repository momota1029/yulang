import Yulang.CommonRoleCaptureBatchModels
import Yulang.CommonRoleIntervalCandidates

/-! Original where-template models survive actual interval capture and expansion.
This is the existing finite candidate grammar, not general role resolution.
Source identities remain supplied by the caller. Child interval membership does
not assert a child dictionary, nor a final selected classification. -/
namespace Yulang.CommonRoleWhereSourceModels
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalCapture (Bindings variables argumentVariables lookup total)
open CommonRoleIntervalPaterson (Argument Goal instantiate child expand)
open CommonRoleIntervalCandidates (Accepts inspect normalizeArguments normalizeGoal)
open CommonRoleCaptureBatchModels (HeadFits BindingFits SharedFits Job demands)
open CommonRoleIntervals (Fits evaluate)
open Common (Subtype)
open Core.PresenceGeneration (Comp)
open CommonRoleSourceIntervalBatches (Demand State)
open PresenceNormalForm (All)

/-- Monotonicity is needed only at names occurring in the original template. -/
theorem form_mono (form : Form) (first last : Nat → Common.Ty)
    (below : ∀ name ∈ variables form, Subtype (first name) (last name)) :
    Subtype (form.eval first) (form.eval last) := by
  induction form with
  | var name => exact below name (by simp [variables])
  | int => exact Common.subtype_refl _
  | pair a b ia ib =>
    exact (Common.common_pair_iff ..).mpr
      ⟨ia (fun n h => below n (List.mem_append_left _ h)),
       ib (fun n h => below n (List.mem_append_right _ h))⟩
  | join a b ia ib =>
    exact Common.common_union_mono
      (ia (fun n h => below n (List.mem_append_left _ h)))
      (ib (fun n h => below n (List.mem_append_right _ h)))
  | tick a ia => exact (Common.common_variant_iff ..).mpr (ia below)

/-- Normalizing original endpoints changes no interval-membership judgment. -/
theorem normalized_fits (ambient : Nat → Common.Ty) (argument : Argument) (value : Common.Ty) :
    Fits (evaluate (Form.eval ambient) (argument.1.normalize, argument.2.normalize)) value ↔
      Fits (evaluate (Form.eval ambient) argument) value := by
  have low := CommonRoleCaptureNormalization.normalize_meaning argument.1 ambient
  have up := CommonRoleCaptureNormalization.normalize_meaning argument.2 ambient
  exact ⟨fun ⟨a,b⟩ => ⟨Common.subtype_trans low.2 a, Common.subtype_trans b up.1⟩,
    fun ⟨a,b⟩ => ⟨Common.subtype_trans low.1 a, Common.subtype_trans b up.2⟩⟩

theorem normalized_heads (ambient locals : Nat → Common.Ty) (forms : List Form)
    (arguments : List Argument) :
    HeadFits ambient locals forms (normalizeArguments arguments) ↔
      HeadFits ambient locals forms arguments := by
  induction forms generalizing arguments with
  | nil => cases arguments <;> simp [HeadFits, normalizeArguments]
  | cons form forms ih =>
    cases arguments with
    | nil => simp [HeadFits, normalizeArguments]
    | cons argument arguments =>
      exact and_congr (normalized_fits ambient argument _) (ih arguments)

/-- Finite lookup returns an original captured binding, including duplicates. -/
theorem lookup_member (bindings : Bindings) (name : Nat) (argument : Argument)
    (found : lookup bindings name = some argument) : (name, argument) ∈ bindings := by
  induction bindings with
  | nil => cases found
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases same : key = name
    · subst key
      have eq : value = argument := by simpa [lookup] using found
      subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

/-- Template instantiation retains the same model, using both endpoints.
The bound-name premise is explicit and is discharged by the actual inspector. -/
theorem instantiated_fits (ambient locals : Nat → Common.Ty) (bindings : Bindings)
    (models : BindingFits ambient locals bindings) (form : Form)
    (bound : ∀ name ∈ variables form, ∃ argument, lookup bindings name = some argument) :
    Fits (evaluate (Form.eval ambient)
      ((form.subst (fun name => (total bindings name).1)).normalize,
       (form.subst (fun name => (total bindings name).2)).normalize))
      (form.eval locals) := by
  apply (normalized_fits ambient
    (form.subst (fun name => (total bindings name).1),
     form.subst (fun name => (total bindings name).2)) _).mpr
  change Subtype _ _ ∧ Subtype _ _
  dsimp [evaluate]
  rw [CommonRoleCaptureNormalization.subst_eval, CommonRoleCaptureNormalization.subst_eval]
  have atName : ∀ name ∈ variables form,
      Fits (evaluate (Form.eval ambient) (total bindings name)) (locals name) := by
    intro name used
    obtain ⟨argument, found⟩ := bound name used
    simpa [total, found] using models (name, argument) (lookup_member bindings name argument found)
  exact ⟨form_mono form _ _ (fun name used => (atName name used).1),
    form_mono form _ _ (fun name used => (atName name used).2)⟩

theorem instantiated_heads (ambient locals : Nat → Common.Ty) (bindings : Bindings)
    (models : BindingFits ambient locals bindings) (forms : List Form)
    (bound : ∀ name ∈ argumentVariables forms, ∃ argument, lookup bindings name = some argument) :
    HeadFits ambient locals forms (instantiate (total bindings) forms) := by
  induction forms with
  | nil => trivial
  | cons form forms ih =>
    constructor
    · exact instantiated_fits ambient locals bindings models form
        (fun name used => bound name (List.mem_append_left _ used))
    · exact ih (fun name used => bound name (List.mem_append_right _ used))

/-- Every actual child is interpreted by the parent's original local valuation. -/
def WhereFits (ambient locals : Nat → Common.Ty) (declaration : Declaration)
    (bindings : Bindings) : Prop :=
  ∀ requirement ∈ declaration.requirements,
    HeadFits ambient locals requirement.2 (child requirement (total bindings)).arguments

/-- No semantic child-success assumption: the real capture and bound-name
checks transfer a parent's original head model to all of its where templates. -/
theorem accepted_where_fits (ambient locals : Nat → Common.Ty)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings)
    (parent : HeadFits ambient locals declaration.head goal.arguments) :
    WhereFits ambient locals declaration bindings := by
  have captured := (CommonRoleCaptureBatchModels.capture_arguments_fits ambient locals
    accepted.2.2.2.1).mp ((normalized_heads ambient locals _ _).mpr parent)
  intro requirement member
  apply instantiated_heads ambient locals bindings captured
  intro name used
  obtain ⟨argument, found, _⟩ :=
    CommonRoleIntervalCandidates.all_where_bindings_exist declaration goal bindings
      accepted requirement member name used
  exact ⟨argument, found⟩

/-- Actual endpoint expansion carries all where children in source order. -/
theorem expanded_member_fits (ambient locals : Nat → Common.Ty)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings)
    (parent : HeadFits ambient locals declaration.head goal.arguments)
    (generated : Goal) (member : generated ∈ expand declaration (total bindings)) :
    ∃ requirement ∈ declaration.requirements,
      generated.role = requirement.1 ∧
      HeadFits ambient locals requirement.2 generated.arguments := by
  obtain ⟨requirement, included, rfl⟩ := List.mem_map.mp member
  exact ⟨requirement, included, rfl,
    accepted_where_fits ambient locals declaration goal bindings accepted parent requirement included⟩

/-- Ambient endpoint names are distinct from declaration-local binder names. -/
def sources (argument : Argument) : List Nat := variables argument.1 ++ variables argument.2

def goalSources (arguments : List Argument) : List Nat := arguments.flatMap sources

theorem normalize_sources (form : Form) : ∀ name ∈ variables form.normalize,
    name ∈ variables form := by
  induction form with
  | var name => exact fun _ h => h
  | int => exact fun _ h => h
  | pair a b ia ib =>
    intro name used
    rcases List.mem_append.mp used with left | right
    · exact List.mem_append_left _ (ia name left)
    · exact List.mem_append_right _ (ib name right)
  | tick a ia => exact ia
  | join a b ia ib =>
    simp only [Form.normalize]
    split
    · exact fun name used => List.mem_append_left _ (ia name used)
    · intro name used
      rcases List.mem_append.mp used with left | right
      · exact List.mem_append_left _ (ia name left)
      · exact List.mem_append_right _ (ib name right)

theorem subst_sources (form : Form) (image : Nat → Form) :
    ∀ name ∈ variables (form.subst image),
      ∃ binder ∈ variables form, name ∈ variables (image binder) := by
  induction form with
  | var binder => exact fun name used => ⟨binder, List.mem_singleton_self _, used⟩
  | int => simp [Form.subst, variables]
  | pair a b ia ib | join a b ia ib =>
    intro name used
    rcases List.mem_append.mp used with left | right
    · obtain ⟨binder, present, used⟩ := ia name left
      exact ⟨binder, List.mem_append_left _ present, used⟩
    · obtain ⟨binder, present, used⟩ := ib name right
      exact ⟨binder, List.mem_append_right _ present, used⟩
  | tick a ia => exact ia

/-- Capture preserves actual endpoint origin even when a binder is repeated. -/
theorem capture_sources (captured : CommonRoleIntervalCapture.Capture form argument bindings) :
    ∀ binding ∈ bindings, ∀ name ∈ sources binding.2, name ∈ sources argument := by
  induction captured with
  | var binder argument =>
    intro binding member name used
    have same : binding = (binder, argument) := List.mem_singleton.mp member
    subst binding
    exact used
  | int => simp
  | pair before after ia ib =>
    intro binding member name used
    rcases List.mem_append.mp member with left | right
    · have original := ia binding left name used
      simp only [sources, variables, List.mem_append] at original ⊢
      rcases original with lo | hi
      · exact Or.inl (Or.inl lo)
      · exact Or.inr (Or.inl hi)
    · have original := ib binding right name used
      simp only [sources, variables, List.mem_append] at original ⊢
      rcases original with lo | hi
      · exact Or.inl (Or.inr lo)
      · exact Or.inr (Or.inr hi)
  | tick inner ih => exact ih

theorem capture_arguments_sources
    (captured : CommonRoleIntervalCapture.CaptureArguments forms arguments bindings) :
    ∀ binding ∈ bindings, ∀ name ∈ sources binding.2, name ∈ goalSources arguments := by
  induction captured with
  | nil => simp
  | cons first rest ih =>
    intro binding member name used
    rcases List.mem_append.mp member with left | right
    · exact List.mem_append_left _ (capture_sources first binding left name used)
    · exact List.mem_append_right _ (ih binding right name used)

theorem normalized_goal_sources (arguments : List Argument) :
    ∀ name ∈ goalSources (normalizeArguments arguments), name ∈ goalSources arguments := by
  intro name used
  obtain ⟨argument, included, used⟩ := List.mem_flatMap.mp used
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp included
  apply List.mem_flatMap.mpr
  refine ⟨original, member, ?_⟩
  rcases List.mem_append.mp used with low | high
  · exact List.mem_append_left _ (normalize_sources original.1 name low)
  · exact List.mem_append_right _ (normalize_sources original.2 name high)

/-- Every generated endpoint name comes from an original parent endpoint.
Finite bound-name checks rule out observing the lookup fallback. This computes
provenance for arbitrary many binders and all finite where templates. -/
theorem accepted_child_sources (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings) (requirement : Nat × List Form)
    (member : requirement ∈ declaration.requirements) :
    ∀ name ∈ goalSources (child requirement (total bindings)).arguments,
      name ∈ goalSources goal.arguments := by
  intro name used
  obtain ⟨argument, included, used⟩ := List.mem_flatMap.mp used
  obtain ⟨form, formMember, rfl⟩ := List.mem_map.mp included
  have bound : ∀ binder ∈ variables form,
      ∃ original, lookup bindings binder = some original ∧ total bindings binder = original := by
    intro binder mentioned
    exact CommonRoleIntervalCandidates.all_where_bindings_exist declaration goal bindings accepted
      requirement member binder (List.mem_flatMap.mpr ⟨form, formMember, mentioned⟩)
  apply normalized_goal_sources goal.arguments name
  rcases List.mem_append.mp used with lower | upper
  · obtain ⟨binder, mentioned, present⟩ := subst_sources form _ name (normalize_sources _ name lower)
    obtain ⟨original, found, equal⟩ := bound binder mentioned
    rw [equal] at present
    exact capture_arguments_sources accepted.2.2.2.1 (binder, original)
      (lookup_member bindings binder original found) name (List.mem_append_left _ present)
  · obtain ⟨binder, mentioned, present⟩ := subst_sources form _ name (normalize_sources _ name upper)
    obtain ⟨original, found, equal⟩ := bound binder mentioned
    rw [equal] at present
    exact capture_arguments_sources accepted.2.2.2.1 (binder, original)
      (lookup_member bindings binder original found) name (List.mem_append_right _ present)

def captureJob (declaration : Declaration) (goal : Goal) (source : Nat → Nat) : Job :=
  ⟨declaration, normalizeGoal goal, source⟩

def generatedState (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (source : Nat → Nat) (bindings : Bindings) : State α :=
  CommonRoleSourceIntervalBatches.advance (CommonRoleSourceIntervalBatches.start old)
    (demands slots (captureJob declaration goal source) bindings)

/-- Exact all-model statement at a real accepted capture. Adding the models of
all original where templates loses no parent model. It does not solve children. -/
theorem generated_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal) (source : Nat → Nat)
    (bindings : Bindings) (accepted : Accepts declaration goal bindings) :
    All Common.model assignment (generatedState slots old declaration goal source bindings).atoms ↔
      ∃ values, SharedFits assignment values old ∧
        HeadFits (fun n => (assignment (slots n)).1) (values ∘ source)
          declaration.head goal.arguments ∧
        WhereFits (fun n => (assignment (slots n)).1) (values ∘ source) declaration bindings := by
  have captures : CommonRoleCaptureBatchModels.Captures (captureJob declaration goal source) bindings :=
    ⟨accepted.2.1, accepted.2.2.2.1⟩
  have exactModels := CommonRoleCaptureBatchModels.run_models_exact slots assignment old
    [captureJob declaration goal source] [demands slots (captureJob declaration goal source) bindings]
    (.cons captures .nil)
  simp only [CommonRoleSourceIntervalBatches.run, generatedState] at exactModels ⊢
  rw [exactModels]
  simp only [CommonRoleCaptureBatchModels.HeadsFit, List.forall_mem_singleton,
    captureJob, normalizeGoal, accepted.2.1, true_and]
  constructor
  · rintro ⟨values, previous, parent⟩
    have original := (normalized_heads (fun n => (assignment (slots n)).1) (values ∘ source)
      declaration.head goal.arguments).mp parent
    exact ⟨values, previous, original, accepted_where_fits _ _ _ _ _ accepted original⟩
  · rintro ⟨values, previous, parent, _⟩
    exact ⟨values, previous, (normalized_heads (fun n => (assignment (slots n)).1)
      (values ∘ source) declaration.head goal.arguments).mpr parent⟩

structure Result (α : Type) where
  bindings : Bindings
  state : State α
  children : List Goal

/-- Preserve the existing scanner's three outcomes: outside, no candidate,
and an accepted capture with all ordered children. No outcome is renamed into
language-visible pending/rejected/selected. -/
def run (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (source : Nat → Nat) :
    Option (Option (Result α)) := do
  let inspected ← inspect declaration goal
  pure (inspected.map fun bindings =>
    ⟨bindings, generatedState slots old declaration goal source bindings,
      expand declaration (total bindings)⟩)

/-- Public execution/model exactness. No accepted-capture or model premise is
assumed: the right side gives independent capture boundaries and source models.
Child success is intentionally absent; all child endpoints and order are kept. -/
theorem run_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal) (source : Nat → Nat)
    (result : Result α) :
    (run slots old declaration goal source = some (some result) ∧
      All Common.model assignment result.state.atoms) ↔
    ∃ bindings, Accepts declaration goal bindings ∧
      result = ⟨bindings, generatedState slots old declaration goal source bindings,
        expand declaration (total bindings)⟩ ∧
      ∃ values, SharedFits assignment values old ∧
        HeadFits (fun n => (assignment (slots n)).1) (values ∘ source)
          declaration.head goal.arguments ∧
        WhereFits (fun n => (assignment (slots n)).1) (values ∘ source) declaration bindings := by
  constructor
  · rintro ⟨returned, models⟩
    cases inspected : inspect declaration goal with
    | none => simp [run, inspected] at returned
    | some answer =>
      cases answer with
      | none => simp [run, inspected] at returned
      | some bindings =>
        have same : result = ⟨bindings, generatedState slots old declaration goal source bindings,
            expand declaration (total bindings)⟩ := by
          simpa [run, inspected] using returned.symm
        subst result
        have accepted := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected
        exact ⟨bindings, accepted, rfl, (generated_models_exact slots assignment old
          declaration goal source bindings accepted).mp models⟩
  · rintro ⟨bindings, accepted, rfl, models⟩
    exact ⟨by simp [run, (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted],
      (generated_models_exact slots assignment old declaration goal source bindings accepted).mpr models⟩

/-- Real output provenance does not require any model to exist. It includes
inconsistent endpoints, duplicate where children, and both original endpoints. -/
theorem returned_sources (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (source : Nat → Nat) (result : Result α)
    (returned : run slots old declaration goal source = some (some result)) :
    ∀ generated ∈ result.children, ∀ name ∈ goalSources generated.arguments,
      name ∈ goalSources goal.arguments := by
  cases inspected : inspect declaration goal with
  | none => simp [run, inspected] at returned
  | some answer =>
    cases answer with
    | none => simp [run, inspected] at returned
    | some bindings =>
      have same : result = ⟨bindings, generatedState slots old declaration goal source bindings,
          expand declaration (total bindings)⟩ := by
        simpa [run, inspected] using returned.symm
      subst result
      intro generated member name used
      obtain ⟨requirement, included, rfl⟩ := List.mem_map.mp member
      exact accepted_child_sources declaration goal bindings
        ((CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected)
        requirement included name used

end Yulang.CommonRoleWhereSourceModels
