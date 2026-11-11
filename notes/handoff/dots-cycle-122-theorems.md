# Cycle122 theorem signatures and axiom audit

一般辞書関連 59 定理の elaborated signature。`#check @name` で暗黙の入力も列挙し、
前提と量化された型・状態・モデルを省いていない。M1 のどの側に効くかと未達の境界は
[cycle report](dots-cycle-122.md) を参照。34 定理が cycle122、25 定理が cycle121 の復旧。

```lean
@Yulang.GeneralSourceDictionaries.equivalent_refl : ∀ {roles : Yulang.Roles.RoleDecls}
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent tree tree
@Yulang.GeneralSourceDictionaries.equivalent_symm : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
    Yulang.GeneralSourceDictionaries.DictionaryEquivalent after before
@Yulang.GeneralSourceDictionaries.equivalent_trans : ∀ {roles : Yulang.Roles.RoleDecls}
  {before middle after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before middle →
    Yulang.GeneralSourceDictionaries.DictionaryEquivalent middle after →
      Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after
@Yulang.GeneralSourceDictionaries.equivalent_root : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after → before.root = after.root
@Yulang.GeneralSourceDictionaries.equivalent_key : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after → before.key = after.key
@Yulang.GeneralSourceDictionaries.childObservations_append : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last : List (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  Yulang.GeneralSourceDictionaries.childObservations (first ++ last) =
    Yulang.GeneralSourceDictionaries.childObservations first ++ Yulang.GeneralSourceDictionaries.childObservations last
@Yulang.GeneralSourceDictionaries.childObservations_flatten : ∀ {roles : Yulang.Roles.RoleDecls}
  (children : List (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  Yulang.GeneralSourceDictionaries.childObservations children =
    (List.map Yulang.GeneralSourceDictionaries.observations children).flatten
@Yulang.GeneralSourceDictionaries.equivalent_observations : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
    (Yulang.GeneralSourceDictionaries.observations before).Perm (Yulang.GeneralSourceDictionaries.observations after)
@Yulang.GeneralSourceDictionaries.equivalent_nodeCount : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles},
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
    Yulang.GeneralSourceDictionaries.nodeCount before = Yulang.GeneralSourceDictionaries.nodeCount after
@Yulang.GeneralSourceDictionaries.equivalent_eventCount : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (event : Yulang.GeneralSourceDictionaries.Occurrence roles × Nat → Bool),
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
    List.countP event (Yulang.GeneralSourceDictionaries.observations before) =
      List.countP event (Yulang.GeneralSourceDictionaries.observations after)
@Yulang.GeneralSourceDictionaries.evidence_node_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  Yulang.GeneralSourceDictionaries.Evidence localRule
      (Yulang.GeneralSourceDictionaries.Dictionary.node occurrence key children) ↔
    localRule occurrence key (List.map Yulang.GeneralSourceDictionaries.Dictionary.root children) ∧
      ∀ (child : Yulang.GeneralSourceDictionaries.Dictionary roles),
        child ∈ children → Yulang.GeneralSourceDictionaries.Evidence localRule child
@Yulang.GeneralSourceDictionaries.evidence_replace : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (leading trailing : List (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  before.root = after.root →
    (Yulang.GeneralSourceDictionaries.Evidence localRule before →
        Yulang.GeneralSourceDictionaries.Evidence localRule after) →
      Yulang.GeneralSourceDictionaries.Evidence localRule
          (Yulang.GeneralSourceDictionaries.Dictionary.node occurrence key (leading ++ before :: trailing)) →
        Yulang.GeneralSourceDictionaries.Evidence localRule
          (Yulang.GeneralSourceDictionaries.Dictionary.node occurrence key (leading ++ after :: trailing))
@Yulang.GeneralSourceDictionaries.evidence_equivalent : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  Yulang.GeneralSourceDictionaries.PermutationInvariant localRule →
    Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
      (Yulang.GeneralSourceDictionaries.Evidence localRule before ↔
        Yulang.GeneralSourceDictionaries.Evidence localRule after)
@Yulang.GeneralSourceDictionaries.linked_equivalent : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralSourceDictionaries.Dictionary roles} (state : Yulang.GeneralSourceState.State),
  Yulang.GeneralSourceDictionaries.DictionaryEquivalent before after →
    (Yulang.GeneralSourceDictionaries.Linked state before ↔ Yulang.GeneralSourceDictionaries.Linked state after)
@Yulang.GeneralSourceDictionaries.evidence_mono : ∀ {roles : Yulang.Roles.RoleDecls}
  {tree : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (first last : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  (∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      first occurrence key children → last occurrence key children) →
    Yulang.GeneralSourceDictionaries.Evidence first tree → Yulang.GeneralSourceDictionaries.Evidence last tree
@Yulang.GeneralSourceDictionaries.linked_refines : ∀ {before after : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} (refinement : Yulang.GeneralSourceState.Refines before after)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  Yulang.GeneralSourceDictionaries.Linked before tree → Yulang.GeneralSourceDictionaries.Linked after tree
@Yulang.GeneralSourceDictionaries.erase_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  Yulang.GeneralSourceDictionaries.Evidence localRule tree →
    Yulang.GeneralSourceDictionaries.ErasedEvidence localRule tree.root (Yulang.GeneralSourceDictionaries.erase tree)
@Yulang.GeneralSourceDictionaries.erase_forgets_occurrence : ∀ {roles : Yulang.Roles.RoleDecls}
  (demand : Yulang.GeneralSourceState.Demand roles) (first last key : Nat),
  first ≠ last →
    have left := Yulang.GeneralSourceDictionaries.Dictionary.node { identity := first, demand := demand } key [];
    have right := Yulang.GeneralSourceDictionaries.Dictionary.node { identity := last, demand := demand } key [];
    Yulang.GeneralSourceDictionaries.erase left = Yulang.GeneralSourceDictionaries.erase right ∧
      ¬Yulang.GeneralSourceDictionaries.DictionaryEquivalent left right
Yulang.GeneralSourceDictionaryEquations.intervalAtoms_exact : ∀ (lower upper : Nat)
  (head : Yulang.Core.PresenceGeneration.TyTerm Nat) (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment
      (Yulang.GeneralSourceDictionaryEquations.intervalAtoms lower upper head) ↔
    Yulang.Common.Subtype (assignment lower).fst
        (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment head) ∧
      Yulang.Common.Subtype (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment head)
        (assignment upper).fst
Yulang.GeneralSourceDictionaryEquations.outputAtoms_exact : ∀ (target : Nat)
  (rhs : Yulang.Core.PresenceGeneration.TyTerm Nat) (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment
      (Yulang.GeneralSourceDictionaryEquations.outputAtoms target rhs) ↔
    Yulang.Common.Equivalent (assignment target).fst
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment rhs)
@Yulang.GeneralSourceDictionaryEquations.equations_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles}
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment equations.atoms ↔ equations.Holds assignment
@Yulang.GeneralSourceDictionaryEquations.append_equations_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles}
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand)
  (old : List (Yulang.PresenceNormalForm.Atom Nat)) (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment (old ++ equations.atoms) ↔
    Yulang.PresenceNormalForm.All Yulang.Common.model assignment old ∧ equations.Holds assignment
@Yulang.GeneralSourceDictionaryEquations.entailed_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) {demand : Yulang.GeneralSourceState.Demand roles}
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand),
  Yulang.GeneralSourceDictionaryEquations.Entailed state equations ↔
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment → equations.Holds assignment
@Yulang.GeneralSourceDictionaryEquations.output_equality : ∀ {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles}
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment equations.atoms →
    ∀ (index : Fin demand.outputs.length),
      Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst
        (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment (equations.output index))
@Yulang.GeneralSourceDictionaryEquations.all_model_output_equality : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) {demand : Yulang.GeneralSourceState.Demand roles}
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand),
  Yulang.GeneralSourceDictionaryEquations.Entailed state equations →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment →
        ∀ (index : Fin demand.outputs.length),
          Yulang.Common.Equivalent (assignment demand.outputs[index].target).fst
            (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment (equations.output index))
Yulang.GeneralRegistryReordering.declarationReorders_refl : ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.DeclarationReorders declaration declaration
@Yulang.GeneralRegistryReordering.declarationReorders_symm : ∀ {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    Yulang.GeneralRegistryReordering.DeclarationReorders last first
@Yulang.GeneralRegistryReordering.declarationReorders_trans : ∀
  {first middle last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first middle →
    Yulang.GeneralRegistryReordering.DeclarationReorders middle last →
      Yulang.GeneralRegistryReordering.DeclarationReorders first last
Yulang.GeneralRegistryReordering.reorders_refl : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralRegistryReordering.Reorders registry registry
@Yulang.GeneralRegistryReordering.checked_permute_requirements : ∀
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls}
  (declaration : Yulang.GeneralDeclarations.Declaration) (requirements : List Yulang.GeneralDeclarations.Clause),
  declaration.requirements.Perm requirements →
    Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
      Yulang.GeneralDeclarations.DeclarationChecked constructors roles
        { id := declaration.id, role := declaration.role, head := declaration.head, requirements := requirements,
          associated := declaration.associated, outputBinders := declaration.outputBinders }
@Yulang.GeneralRegistryReordering.declarationReorders_update : ∀ {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    last =
      { id := first.id, role := first.role, head := first.head, requirements := last.requirements,
        associated := first.associated, outputBinders := first.outputBinders }
@Yulang.GeneralRegistryReordering.declarationReorders_checked : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    (Yulang.GeneralDeclarations.DeclarationChecked constructors roles first ↔
      Yulang.GeneralDeclarations.DeclarationChecked constructors roles last)
@Yulang.GeneralRegistryReordering.reorders_visible : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ first.declarations →
        ∃ other, other ∈ last.declarations ∧ Yulang.GeneralRegistryReordering.DeclarationReorders declaration other
@Yulang.GeneralRegistryReordering.reorders_declaration_ids : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    (List.map Yulang.GeneralDeclarations.Declaration.id first.declarations).Perm
      (List.map Yulang.GeneralDeclarations.Declaration.id last.declarations)
@Yulang.GeneralRegistryReordering.reorders_visible_back : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ last.declarations →
        ∃ other, other ∈ first.declarations ∧ Yulang.GeneralRegistryReordering.DeclarationReorders other declaration
@Yulang.GeneralRegistryReordering.reorders_checked : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    Yulang.GeneralDeclarations.Checked first → Yulang.GeneralDeclarations.Checked last
@Yulang.GeneralRegistryChildOrder.reorders_symm : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last → Yulang.GeneralRegistryReordering.Reorders last first
@Yulang.GeneralRegistryChildOrder.reorders_trans : ∀ {first middle last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first middle →
    Yulang.GeneralRegistryReordering.Reorders middle last → Yulang.GeneralRegistryReordering.Reorders first last
@Yulang.GeneralRegistryChildOrder.reorders_checked_iff : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    (Yulang.GeneralDeclarations.Checked first ↔ Yulang.GeneralDeclarations.Checked last)
@Yulang.GeneralRegistryChildOrder.emitAll_pmap : ∀ {roles : Yulang.Roles.RoleDecls} (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (valid : Yulang.GeneralDeclarations.Declaration.Signature roles declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (allocate : (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
  Yulang.GeneralDeclarationDemands.emitAll invocation declaration valid capture allocate =
    List.pmap
      (fun clause signature =>
        Yulang.GeneralDeclarationDemands.emit invocation declaration clause signature capture (allocate clause))
      declaration.requirements ⋯
@Yulang.GeneralRegistryChildOrder.emitAll_permute_requirements : ∀ {roles : Yulang.Roles.RoleDecls} (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (requirements : List Yulang.GeneralDeclarations.Clause),
  declaration.requirements.Perm requirements →
    ∀ (valid : Yulang.GeneralDeclarations.Declaration.Signature roles declaration)
      (valid' :
        Yulang.GeneralDeclarations.Declaration.Signature roles
          { id := declaration.id, role := declaration.role, head := declaration.head, requirements := requirements,
            associated := declaration.associated, outputBinders := declaration.outputBinders })
      (capture : Yulang.GeneralDeclarationDemands.Capture)
      (allocate :
        (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
      (Yulang.GeneralDeclarationDemands.emitAll invocation declaration valid capture allocate).Perm
        (Yulang.GeneralDeclarationDemands.emitAll invocation
          { id := declaration.id, role := declaration.role, head := declaration.head, requirements := requirements,
            associated := declaration.associated, outputBinders := declaration.outputBinders }
          valid' capture allocate)
@Yulang.GeneralRegistryChildOrder.swapped_child_order_not_equal : ∀ {roles : Yulang.Roles.RoleDecls} (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (first last : Yulang.GeneralDeclarations.Clause),
  declaration.requirements = [first, last] →
    first.id ≠ last.id →
      ∀ (valid : Yulang.GeneralDeclarations.Declaration.Signature roles declaration)
        (valid' :
          Yulang.GeneralDeclarations.Declaration.Signature roles
            { id := declaration.id, role := declaration.role, head := declaration.head, requirements := [last, first],
              associated := declaration.associated, outputBinders := declaration.outputBinders })
        (capture : Yulang.GeneralDeclarationDemands.Capture)
        (allocate :
          (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
        Yulang.GeneralDeclarationDemands.emitAll invocation declaration valid capture allocate ≠
          Yulang.GeneralDeclarationDemands.emitAll invocation
            { id := declaration.id, role := declaration.role, head := declaration.head, requirements := [last, first],
              associated := declaration.associated, outputBinders := declaration.outputBinders }
            valid' capture allocate
Yulang.GeneralDictionaryStateEquations.liftType_eval : ∀ (state : Yulang.GeneralSourceState.State)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)) (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftType state term) =
    Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model (state.assignment assignment) term
Yulang.GeneralDictionaryStateEquations.liftRow_eval : ∀ (state : Yulang.GeneralSourceState.State)
  (term : Yulang.Core.PresenceGeneration.RowTerm (Fin state.slots)) (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.Common.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftRow state term) =
    Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.Common.model (state.assignment assignment) term
@Yulang.GeneralDictionaryStateEquations.recorded_holds : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryStateEquations.Recorded located →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment → located.equations.Holds assignment
@Yulang.GeneralDictionaryStateEquations.recorded_entails : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryStateEquations.Recorded located →
    Yulang.GeneralSourceDictionaryEquations.Entailed state located.equations
Yulang.GeneralDictionaryStateEquations.lifted_arrow_separates_sources : ∀ (state : Yulang.GeneralSourceState.State)
  (input output row : Fin state.slots),
  Yulang.GeneralDictionaryStateEquations.liftType state
      ((Yulang.Core.PresenceGeneration.TyTerm.var input).arrow (Yulang.Core.PresenceGeneration.RowTerm.var row)
        (Yulang.Core.PresenceGeneration.TyTerm.var output) (Yulang.Core.PresenceGeneration.RowTerm.var row)) =
    (Yulang.Core.PresenceGeneration.TyTerm.var (state.source input)).arrow
      (Yulang.Core.PresenceGeneration.RowTerm.var (state.rowSource row))
      (Yulang.Core.PresenceGeneration.TyTerm.var (state.source output))
      (Yulang.Core.PresenceGeneration.RowTerm.var (state.rowSource row))
@Yulang.GeneralDictionaryStateEquations.entailed_refines : ∀ {before after : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} (refinement : Yulang.GeneralSourceState.Refines before after)
  (demand : Yulang.GeneralSourceState.Demand roles)
  (equations : Yulang.GeneralSourceDictionaryEquations.InstanceEquations demand),
  Yulang.GeneralSourceDictionaryEquations.Entailed before equations →
    Yulang.GeneralSourceDictionaryEquations.Entailed after equations
Yulang.GeneralDictionaryEquationExamples.recorded : Yulang.GeneralDictionaryStateEquations.Recorded
  Yulang.GeneralDictionaryEquationExamples.located
Yulang.GeneralDictionaryEquationExamples.models : Yulang.GeneralSourceState.Models
  Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryEquationExamples.assignment
Yulang.GeneralDictionaryEquationExamples.all_model_outputs : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state model →
    ∀ (index : Fin Yulang.GeneralDictionaryEquationExamples.demand.outputs.length),
      Yulang.Common.Equivalent (model 10).fst (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int)
Yulang.GeneralDictionaryEquationExamples.duplicate_outputs_retained : Yulang.GeneralDictionaryEquationExamples.demand.outputs.length =
    2 ∧
  Yulang.GeneralDictionaryEquationExamples.located.equations.atoms.length = 6
Yulang.GeneralDictionaryEquationExamples.separate_type_and_row_ids : Yulang.GeneralDictionaryStateEquations.liftType
    Yulang.GeneralDictionaryEquationExamples.state
    ((Yulang.Core.PresenceGeneration.TyTerm.var 0).arrow (Yulang.Core.PresenceGeneration.RowTerm.var 0)
      (Yulang.Core.PresenceGeneration.TyTerm.var 0) (Yulang.Core.PresenceGeneration.RowTerm.var 0)) =
  (Yulang.Core.PresenceGeneration.TyTerm.var 10).arrow (Yulang.Core.PresenceGeneration.RowTerm.var 20)
    (Yulang.Core.PresenceGeneration.TyTerm.var 10) (Yulang.Core.PresenceGeneration.RowTerm.var 20)
Yulang.GeneralCanonicalChildOrder.canonicalRequirements_perm : ∀ (clauses : List Yulang.GeneralDeclarations.Clause),
  clauses.Perm (Yulang.GeneralCanonicalChildOrder.canonicalRequirements clauses)
Yulang.GeneralCanonicalChildOrder.canonicalRequirements_eq : ∀ (first last : List Yulang.GeneralDeclarations.Clause),
  (List.map Yulang.GeneralDeclarations.Clause.id first).Nodup →
    first.Perm last →
      Yulang.GeneralCanonicalChildOrder.canonicalRequirements first =
        Yulang.GeneralCanonicalChildOrder.canonicalRequirements last
@Yulang.GeneralCanonicalChildOrder.canonical_checked : ∀ {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  {roles : Yulang.Roles.RoleDecls} (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    Yulang.GeneralDeclarations.DeclarationChecked constructors roles
      (Yulang.GeneralCanonicalChildOrder.canonicalDeclaration declaration)
@Yulang.GeneralCanonicalChildOrder.canonical_declaration_eq : ∀ {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    (List.map Yulang.GeneralDeclarations.Clause.id first.requirements).Nodup →
      Yulang.GeneralCanonicalChildOrder.canonicalDeclaration first =
        Yulang.GeneralCanonicalChildOrder.canonicalDeclaration last
@Yulang.GeneralCanonicalChildOrder.canonicalEmit_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls} (invocation : Nat),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (firstChecked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles first)
      (lastChecked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles last)
      (capture : Yulang.GeneralDeclarationDemands.Capture)
      (allocate :
        (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
      Yulang.GeneralCanonicalChildOrder.canonicalEmit invocation first firstChecked capture allocate =
        Yulang.GeneralCanonicalChildOrder.canonicalEmit invocation last lastChecked capture allocate
@Yulang.GeneralCanonicalChildOrder.canonicalEmit_perm : ∀
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls} (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (allocate : (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
  (Yulang.GeneralDeclarationDemands.emitAll invocation declaration ⋯ capture allocate).Perm
    (Yulang.GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked capture allocate)
```

## Trust-zero audit

Exit 0. Recovered I-17 target results included: 91 declarations. The allowed
axioms are propext, Classical.choice, and Quot.sound. This is a focused audit,
not the whole Audit.lean.

```text
'Yulang.B4TargetV2.tree_classifies' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.children_classify' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.render_resolves' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.renders_resolve' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.render_completed' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.renders_completed' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.classify_tree' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.classify_tree_iff' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.dictionary_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.dictionaries_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.diagnostic_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.diagnostics_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.same_diagnostic_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.rejection_not_pending' does not depend on any axioms
'Yulang.B4TargetV2.safe_survivor_not_rejected' does not depend on any axioms
'Yulang.B4TargetV2.unique_not_ambiguous' does not depend on any axioms
'Yulang.B4TargetV2.local_functional' does not depend on any axioms
'Yulang.B4TargetV2.resolves_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.resolves_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.classify_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.pending_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.pending_tree_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2.completed_exact' depends on axioms: [propext, Quot.sound]
'Yulang.B4SkeletonV2.b4_of_bridges' depends on axioms: [propext, Quot.sound]
'Yulang.B4SkeletonV2.completed_of_bridges' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2Regressions.scalar_empty_classify' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2Regressions.scalar_empty_tree' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2Regressions.scalar_empty_not_rejected' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV2Regressions.failed_child_tree' does not depend on any axioms
'Yulang.B4TargetV2Regressions.failed_child_not_root_rejected' does not depend on any axioms
'Yulang.B4TargetV2Regressions.failed_child_not_completed' depends on axioms: [propext]
'Yulang.B4TargetV2Regressions.failed_child_no_classification' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.equivalent_refl' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.equivalent_symm' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.equivalent_trans' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.equivalent_root' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.equivalent_key' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.childObservations_append' depends on axioms: [propext]
'Yulang.GeneralSourceDictionaries.childObservations_flatten' depends on axioms: [propext]
'Yulang.GeneralSourceDictionaries.equivalent_observations' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.equivalent_nodeCount' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.equivalent_eventCount' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.evidence_node_iff' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.evidence_replace' depends on axioms: [propext]
'Yulang.GeneralSourceDictionaries.evidence_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.linked_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.evidence_mono' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.linked_refines' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaries.erase_evidence' does not depend on any axioms
'Yulang.GeneralSourceDictionaries.erase_forgets_occurrence' does not depend on any axioms
'Yulang.GeneralSourceDictionaryEquations.intervalAtoms_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.outputAtoms_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.equations_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.append_equations_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.entailed_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.output_equality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralSourceDictionaryEquations.all_model_output_equality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryReordering.declarationReorders_refl' does not depend on any axioms
'Yulang.GeneralRegistryReordering.declarationReorders_symm' does not depend on any axioms
'Yulang.GeneralRegistryReordering.declarationReorders_trans' does not depend on any axioms
'Yulang.GeneralRegistryReordering.reorders_refl' does not depend on any axioms
'Yulang.GeneralRegistryReordering.checked_permute_requirements' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryReordering.declarationReorders_update' does not depend on any axioms
'Yulang.GeneralRegistryReordering.declarationReorders_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryReordering.reorders_visible' depends on axioms: [propext]
'Yulang.GeneralRegistryReordering.reorders_declaration_ids' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryReordering.reorders_visible_back' depends on axioms: [propext]
'Yulang.GeneralRegistryReordering.reorders_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryChildOrder.reorders_symm' does not depend on any axioms
'Yulang.GeneralRegistryChildOrder.reorders_trans' does not depend on any axioms
'Yulang.GeneralRegistryChildOrder.reorders_checked_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryChildOrder.emitAll_pmap' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryChildOrder.emitAll_permute_requirements' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralRegistryChildOrder.swapped_child_order_not_equal' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.liftRow_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.recorded_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.recorded_entails' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.lifted_arrow_separates_sources' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryStateEquations.entailed_refines' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEquationExamples.recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEquationExamples.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEquationExamples.all_model_outputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEquationExamples.duplicate_outputs_retained' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEquationExamples.separate_type_and_row_ids' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonicalRequirements_perm' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonicalRequirements_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonical_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonical_declaration_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonicalEmit_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralCanonicalChildOrder.canonicalEmit_perm' depends on axioms: [propext, Quot.sound]
```
