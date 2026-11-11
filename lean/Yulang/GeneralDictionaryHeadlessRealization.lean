import Yulang.GeneralDictionaryHeadlessPlans

/-!
# Constructed instantiations for supported checked heads

Successful positional variable materialization makes every captured input
interval a singleton source identity. Checked lexical output-only binders are
disjoint from these inputs. Thus each assignment supplies a concrete compatible
instantiation, without a caller-provided Realizes premise. This is compatibility
of the supplied capture, not candidate selection or general head matching.
-/
namespace Yulang.GeneralDictionaryHeadlessRealization
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries GeneralDictionaryStateEquations
open GeneralDictionaryEmissionPlans (Frame)
open GeneralDictionaryVariableHeads (HeadlessInputs HeadDenotes)
open GeneralDictionaryVariableRealization (Realizes)
open GeneralSourceState (State Assignment Models)
variable {state : State} {roles : Roles.RoleDecls}

private theorem rowPattern_ne_var (entries : List (Nat × Pattern)) (binder : Nat) :
    rowPattern entries ≠ .var binder := by
  cases entries with
  | nil => simp [rowPattern]
  | cons first rest => cases rest <;> simp [rowPattern]

private theorem merge_var_left (first last : Pattern) (binder : Nat)
    (same : merge first last = .var binder) : first = .var binder := by
  unfold merge at same
  split at same
  · exact same
  · split at same
    · exact False.elim (rowPattern_ne_var _ _ same)
    · cases same

/-- The limited normalization fact needed here: a normalized bare variable has
an actual lexical occurrence. No general normalizer-scope theorem is assumed. -/
theorem normalized_var_occurs (pattern : Pattern) (binder : Nat)
    (same : normalize pattern = .var binder) : binder ∈ pattern.variables := by
  cases pattern with
  | var name => simp only [normalize, Pattern.var.injEq] at same; subst name; simp [Pattern.variables]
  | app name arguments => cases same
  | record label payload tail => cases same
  | variant tag payload => cases same
  | join first last =>
    have left := merge_var_left (normalize first) (normalize last) binder same
    exact List.mem_append_left _ (normalized_var_occurs first binder left)
termination_by sizeOf pattern

private theorem input_member (patterns : List Pattern) (binder : Nat)
    (member : binder ∈ variablesArgs (normalizeArgs patterns)) :
    ∃ pattern ∈ patterns, binder ∈ (normalize pattern).variables := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    simp only [normalizeArgs, variablesArgs, List.mem_append] at member
    rcases member with head | tail
    · exact ⟨first, by simp, head⟩
    · obtain ⟨pattern, present, occurrence⟩ := ih tail
      exact ⟨pattern, by simp [present], occurrence⟩

private theorem raw_member (patterns : List Pattern) (pattern : Pattern)
    (present : pattern ∈ patterns) (binder : Nat) (member : binder ∈ pattern.variables) :
    binder ∈ variablesArgs patterns := by
  induction patterns with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | tail
    · exact List.mem_append_left _ member
    · exact List.mem_append_right _ (ih tail)

/-- Every normalized input occurs at a supported positional head, hence has an
exact captured source identity and is excluded from lexical output-only names. -/
theorem supported_input (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (capture : Capture) (demand : GeneralSourceState.Demand roles)
    (head : Fin (roles demand.role).arity → Core.PresenceGeneration.TyTerm (Fin state.slots))
    (denoted : HeadDenotes declaration capture demand head)
    (binder : Nat) (input : binder ∈ declaration.inputNames) :
    (capture.inputs binder).1 = (capture.inputs binder).2 ∧ binder ∉ declaration.outputNames := by
  obtain ⟨pattern, present, member⟩ := input_member declaration.head binder input
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp present
  have arity : index < (roles demand.role).arity := by rw [← denoted.2.1]; exact bound
  obtain ⟨actual, name, slot, atIndex, normalized, _, exactInput, _, _⟩ := denoted.2.2 ⟨index, arity⟩
  have samePattern : actual = pattern := by
    have atPattern : declaration.head[index]? = some pattern := by simp [bound, equal]
    rw [atPattern] at atIndex
    exact (Option.some.inj atIndex).symm
  subst actual
  rw [normalized] at member
  have sameBinder : binder = name := by simpa [Pattern.variables] using member
  subst name
  refine ⟨exactInput, ?_⟩
  intro output
  exact checked.outputOnly.1 binder output
    (raw_member declaration.head pattern present binder (normalized_var_occurs pattern binder normalized))

/-- Constructed separately for each source invocation and assignment. -/
def values (declaration : Declaration) (capture : Capture) (assignment : Assignment) : Nat → Common.Ty :=
  fun binder => if binder ∈ declaration.outputNames then (assignment (capture.outputs binder)).1
    else (assignment (capture.inputs binder).1).1

theorem realizes (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (capture : Capture) (demand : GeneralSourceState.Demand roles)
    (head : Fin (roles demand.role).arity → Core.PresenceGeneration.TyTerm (Fin state.slots))
    (denoted : HeadDenotes declaration capture demand head) (assignment : Assignment) :
    Realizes declaration capture assignment (values declaration capture assignment) := by
  constructor
  · intro binder input
    obtain ⟨same, notOutput⟩ := supported_input declaration checked capture demand head denoted binder input
    simp only [values, notOutput, ← same]
    exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro binder output
    simp only [values, output]
    exact Common.equivalent_refl _

/-- One same-declaration witness works for every assignment. Its concrete values
realize the captured inputs and outputs; positional heads denote those values,
and recorded targets equal actual associated RHS values in every final model. -/
theorem lookup_realization (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : HeadlessInputs state root.demand)
    (result : GeneralDictionaryHeadlessPlans.Result state root)
    (found : GeneralDictionaryHeadlessPlans.lookup registry checked frame root key inputs = some result) :
    ∃ declaration, ∃ _present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      ∀ assignment : Assignment,
        Realizes declaration (frame.capture declaration.id) assignment
          (values declaration (frame.capture declaration.id) assignment) ∧
        (∀ index : Fin (registry.roles root.demand.role).arity,
          ∃ pattern binder, declaration.head[index.val]? = some pattern ∧
            normalize pattern = .var binder ∧
            Common.Equivalent (values declaration (frame.capture declaration.id) assignment binder)
              ((liftType state (result.plan.located.head index)).eval Common.model assignment)) ∧
        (Models (GeneralDictionaryEquationRecording.record result.plan.located) assignment →
          ∀ index : Fin root.demand.outputs.length,
            ∃ equation binder,
              GeneralDictionaryAssociatedProvenance.Supplies registry.roles declaration
                (root.demand.outputs[index]).name (.explicit equation) ∧
              normalize equation.rhs = .var binder ∧
              Common.Equivalent (assignment (root.demand.outputs[index]).target).1
                (values declaration (frame.capture declaration.id) assignment binder)) := by
  have plan := GeneralDictionaryHeadlessPlans.lookup_plan registry checked frame root key inputs result found
  obtain ⟨declaration, present, identity, role, built, _⟩ :=
    (GeneralDictionaryVariablePlans.lookup_exact registry checked frame root key result.inputs result.plan).mp plan
  have head := GeneralDictionaryHeadlessPlans.lookup_heads registry checked frame root key inputs result found
    declaration present identity role
  have locatedHead : HeadDenotes declaration (frame.capture declaration.id) root.demand result.plan.located.head := by
    rw [GeneralDictionaryVariablePlans.build_head declaration _ result.inputs result.plan.located built]
    exact head
  refine ⟨declaration, present, identity, role, ?_⟩
  intro assignment
  have realized := realizes declaration (checked.2 declaration present) (frame.capture declaration.id)
    root.demand result.inputs.head head assignment
  refine ⟨realized, ?_, ?_⟩
  · intro index
    exact GeneralDictionaryVariableHeads.denotesAt_realization declaration (frame.capture declaration.id)
      assignment (values declaration (frame.capture declaration.id) assignment) realized
      index.val (result.plan.located.head index) (locatedHead.2.2 index)
  · intro model index
    exact GeneralDictionaryVariableRealization.built_output_realization declaration
      (frame.capture declaration.id) (checked.2 declaration present).identified.2.2.1 result.inputs
      result.plan.located built assignment model _ realized index

end Yulang.GeneralDictionaryHeadlessRealization
