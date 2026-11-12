import Yulang.GeneralNominalSharedHistoricalBranch

/-! Transport through finite syntactically recorded equality paths, not assumed
semantic endpoint equivalences. -/
namespace Yulang.GeneralNominalSharedJournalPaths
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalMergeCongruence GeneralNominalAllocation

/-- A finite graph of equality equations actually present in ordinary journal
constraints. Reflexive, reverse and composite paths permit arbitrary lengths. -/
inductive RecordedPath (state : GeneralNominalState.State) : Nat → Nat → Prop where
  | refl (source : Nat) : RecordedPath state source source
  | edge {first last : Nat}
      (recorded : ∀ atom ∈ equations first (.var last), atom ∈ state.ordinary) :
      RecordedPath state first last
  | symm {first last : Nat} : RecordedPath state first last → RecordedPath state last first
  | trans {first middle last : Nat} : RecordedPath state first middle →
      RecordedPath state middle last → RecordedPath state first last

/-- Every path is interpreted in the SAME supplied model. -/
theorem RecordedPath.sound {state : GeneralNominalState.State} {first last : Nat}
    (path : RecordedPath state first last) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) :
    CommonNominalFullCarrier.Equivalent (model first).1 (model last).1 := by
  induction path with
  | refl => exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  | edge recorded =>
    have held : PresenceNormalForm.All CommonNominalFullCarrier.model model (equations _ (.var _)) :=
      fun atom member => valid.2.2 atom (recorded atom member)
    exact (GeneralNominalCaptureMerges.equations_exact ..).mp held
  | symm _ ih => exact ⟨ih.2,ih.1⟩
  | trans _ _ one two => exact ⟨CommonNominalFullCarrier.subtype_trans one.1 two.1,
      CommonNominalFullCarrier.subtype_trans two.2 one.2⟩

/-- Syntactic inclusion, not semantic entailment, transports certificates. -/
theorem RecordedPath.mono {before after : GeneralNominalState.State} {first last : Nat}
    (included : ∀ atom ∈ before.ordinary, atom ∈ after.ordinary)
    (path : RecordedPath before first last) : RecordedPath after first last := by
  induction path with
  | refl source => exact .refl source
  | edge recorded => exact .edge (fun atom member => included atom (recorded atom member))
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

/-- An equivalent source head has exactly the same admissible nominal-argument
observations. The observed value is retained, not merely replaced by a witness. -/
theorem nominal_observes_of_equivalent (model : GeneralNominalCommonBridge.Assignment)
    (first last name index : Nat)
    (equal : CommonNominalFullCarrier.Equivalent (model first).1 (model last).1)
    (actual : CommonNominalFullCarrier.Ty)
    (seen : Observes model (.nominal (.source last) name index) actual) :
    Observes model (.nominal (.source first) name index) actual := by
  cases seen with
  | nominal parent value found =>
    cases parent
    exact .nominal (.source first)
      ⟨CommonNominalFullCarrier.subtype_trans equal.1 value.1,
       CommonNominalFullCarrier.subtype_trans value.2 equal.2⟩ found

/-- Repeated-name coherence is invariant under source-head equivalence. -/
theorem coherent_of_equivalent (model : GeneralNominalCommonBridge.Assignment)
    (first last name : Nat) {n : Nat} (names : Fin n → Nat)
    (equal : CommonNominalFullCarrier.Equivalent (model first).1 (model last).1)
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model first name names) :
    GeneralNominalSharedCaptureFacts.Coherent model last name names := by
  intro i j same a b one two
  exact coherent i j same a b
    (nominal_observes_of_equivalent model first last name i.val equal a one)
    (nominal_observes_of_equivalent model first last name j.val equal b two)

/-- Actual equality-feedback storage contributes a path edge. This does not
claim its side conditions, novelty or generated-focus guard automatically. -/
theorem path_equate (state : GeneralNominalSaturationState.State roles) (first last : Nat) :
    RecordedPath (GeneralNominalFeedbackSteps.equate state first last).context.state first last := by
  apply RecordedPath.edge
  intro atom member
  exact List.mem_append_right _ member

/-- Previously stored paths remain certificates after actual equality storage. -/
theorem path_after_equate (state : GeneralNominalSaturationState.State roles)
    (first last a b : Nat) (path : RecordedPath state.context.state a b) :
    RecordedPath (GeneralNominalFeedbackSteps.equate state first last).context.state a b := by
  exact path.mono (fun _ member => List.mem_append_left _ member)

/-- Syntactic certificates need not survive a descriptor rebuild: their semantic
consequence nevertheless persists through EVERY actual support step history. -/
theorem path_sound_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (steps : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    {first last : Nat} (path : RecordedPath before.current.context.state first last)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    CommonNominalFullCarrier.Equivalent (model first).1 (model last).1 :=
  path.sound model (GeneralNominalSupportSteps.steps_models steps model valid).1

theorem merges_after_steps_of_journal_paths (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (after.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (after.current.context.state.base.source (bounds i).2))
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after.current.context.state registry packet.site.occurrence.identity packet.declaration
        (bindings after.current.context.state (report after.current.context packet.declaration [(slot,slot)]))) := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change BranchModels packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds model at branch
  rw [headBounds] at branch
  have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
  have parts := (propagate_models ..).mp propagated
  have oldMerge := parts.2.2
  rw [report_exact packet.context packet.declaration oldSlot oldDescriptor oldRecorded names oldBounds oldParameters oldQuery] at oldMerge
  rw [report_exact after.current.context packet.declaration slot descriptor recorded names bounds parameters query]
  simp only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def] at oldMerge ⊢
  apply (ofFn_merges_iff packet.context.state after.current.context.state packet.registry registry
    packet.site.occurrence.identity packet.declaration seed model names _ _ ?_).mp oldMerge
  intro i
  constructor
  · exact (lowerPaths i).sound model valid.1
  · exact (upperPaths i).sound model valid.1

/-- Full same-model branch for journal-path-covered histories with arbitrary
interval widths and changing endpoint identities. -/
theorem branch_after_steps_of_journal_paths (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (after.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath after.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (after.current.context.state.base.source (bounds i).2))
    (headPath : RecordedPath after.current.context.state
      (packet.context.state.base.source oldSlot) (after.current.context.state.base.source slot))
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (checked : DeclarationChecked registry.constructors roles packet.declaration)
    (terminal : packet.declaration.requirements = []) (equation : Equation)
    (associated : packet.declaration.associated = [equation])
    (output : packet.site.occurrence.demand.outputs = [⟨equation.name,after.current.context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate after.current.context.state.constructors after.current.context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    BranchModels registry after.current.context packet.site.occurrence packet.declaration checked [(slot,slot)] model := by
  apply (GeneralNominalSharedMaterializationFacts.branch_models_iff after.current.context registry
    packet.site.occurrence packet.declaration checked terminal equation associated slot descriptor recorded
    names declared bounds parameters query output translated model).mpr
  refine ⟨valid.1,?_,?_⟩
  · have same := GeneralNominalSharedJournalFacts.coherent_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
    rw [name] at same
    exact coherent_of_equivalent model _ _ _ names
      (headPath.sound model valid.1) same
  · exact merges_after_steps_of_journal_paths registry root before after path packet member oldSlot oldDescriptor oldRecorded headBounds
      names oldBounds oldParameters oldQuery slot descriptor recorded bounds parameters query lowerPaths upperPaths seed model valid
end Yulang.GeneralNominalSharedJournalPaths
