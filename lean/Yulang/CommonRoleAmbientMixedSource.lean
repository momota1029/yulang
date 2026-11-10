import Yulang.CommonRoleStructuralMixedSource

/-! Computed structural allocation includes ordinary-only source variables.
The finite extra-name list and original state remain inputs, not parser output.
This does not claim dynamic allocation, general entailment or B4 completion. -/
namespace Yulang.CommonRoleAmbientMixedSource
open CommonRoleStructuralAssociatedTemplates (Program Occurrence compile Step)
open CommonRoleSettledConstraints (State)
open CommonRoleSourceIdentity (Slot)
open CommonRoleFiniteAssociatedClosure (Fact)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleEvidenceSaturation (Linked)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)

def table (p : Program) (extra : List Nat) : List Nat :=
  CommonRoleStructuralAssociatedTemplates.table p ++ extra

abbrev name (p : Program) (extra : List Nat) (i : Slot (table p extra)) :=
  CommonRoleSourceIdentity.source (table p extra) i

def embed (p : Program) (extra : List Nat)
    (i : Slot (CommonRoleStructuralAssociatedTemplates.table p)) : Slot (table p extra) :=
  ⟨i.val, by have := i.isLt; simp only [table,List.length_append]; omega⟩

theorem name_embed (p : Program) (extra : List Nat)
    (i : Slot (CommonRoleStructuralAssociatedTemplates.table p)) :
    name p extra (embed p extra i) = CommonRoleStructuralMixedSource.name p i := by
  simp [name,embed,table,CommonRoleSourceIdentity.source,
    CommonRoleStructuralMixedSource.name,List.getElem_append_left i.isLt]

def receiver (p : Program) (extra : List Nat) (i : Fin p.length) : Slot (table p extra) :=
  embed p extra (CommonRoleNamedAssociatedSourceModels.receiver (compile p)
    ⟨i.val,by simp [compile]⟩)

def output (p : Program) (extra : List Nat) (i : Fin p.length) : Slot (table p extra) :=
  embed p extra (CommonRoleNamedAssociatedSourceModels.output (compile p)
    ⟨i.val,by simp [compile]⟩)

theorem receiver_source (p : Program) (extra : List Nat) (i : Fin p.length) :
    name p extra (receiver p extra i) = p[i.val].receiver := by
  rw [receiver,name_embed]
  change CommonRoleSourceIdentity.source (CommonRoleNamedAssociatedGraph.table (compile p))
    (CommonRoleNamedAssociatedSourceModels.receiver (compile p) _) = _
  rw [CommonRoleNamedAssociatedSourceModels.receiver_source]
  simp [compile,CommonRoleStructuralAssociatedTemplates.Occurrence.compile]

theorem output_source (p : Program) (extra : List Nat) (i : Fin p.length) :
    name p extra (output p extra i) = p[i.val].output := by
  rw [output,name_embed]
  change CommonRoleSourceIdentity.source (CommonRoleNamedAssociatedGraph.table (compile p))
    (CommonRoleNamedAssociatedSourceModels.output (compile p) _) = _
  rw [CommonRoleNamedAssociatedSourceModels.output_source]
  simp [compile,CommonRoleStructuralAssociatedTemplates.Occurrence.compile]

def occurrence (p : Program) (extra : List Nat) (i : Fin p.length) :
    CommonRoleFiniteAssociatedClosure.Occurrence (table p extra).length :=
  ⟨receiver p extra i,output p extra i,p[i.val].name,
    CommonRoleStructuralAssociatedTemplates.generate p[i.val].template⟩

def source (p : Program) (extra : List Nat) :
    CommonRoleFiniteAssociatedClosure.Source (table p extra).length :=
  ⟨name p extra,(List.finRange p.length).map (occurrence p extra)⟩

def prepared (p : Program) (extra : List Nat) (s : State (table p extra).length) :=
  CommonRoleSourceIdentity.extend (table p extra) s

theorem prepared_evidence (p : Program) (extra : List Nat) (s : State (table p extra).length)
    (i : Slot (table p extra)) (b : Inference.Base) :
    Evidence (prepared p extra s).atoms i b ↔ Evidence s.atoms i b := by
  simp only [prepared,CommonRoleSourceIdentity.extend,Evidence,List.mem_append,
    CommonRoleSourceIdentity.mem_atoms]
  simp [CommonRoleSourceIdentity.pairAtoms]

private theorem identity_edge (t : List Nat) (i j : Slot t) :
    Atom.tyLe (.var i) (.var j) ∈ CommonRoleSourceIdentity.atoms t ↔
      CommonRoleSourceIdentity.source t i = CommonRoleSourceIdentity.source t j := by
  rw [CommonRoleSourceIdentity.mem_atoms]
  constructor
  · rintro ⟨a,b,same,member⟩
    simp only [CommonRoleSourceIdentity.pairAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq | eq
    · cases eq; exact same
    · cases eq; exact same.symm
  · intro same
    exact ⟨i,j,same,by simp [CommonRoleSourceIdentity.pairAtoms]⟩

theorem prepared_linked (p : Program) (extra : List Nat) (s : State (table p extra).length)
    (i j : Slot (table p extra)) :
    Linked (prepared p extra s) i j ↔ Linked s i j ∨ name p extra i = name p extra j := by
  simp only [Linked,prepared,CommonRoleSourceIdentity.extend,List.mem_append,identity_edge]
  change (_ ∨ name p extra i = name p extra j) ∧ (_ ∨ name p extra j = name p extra i) ↔ _
  constructor
  · rintro ⟨a,b⟩
    rcases a with a | same
    · rcases b with b | same
      · exact Or.inl ⟨a,b⟩
      · exact Or.inr same.symm
    · exact Or.inr same
  · rintro (⟨a,b⟩ | same)
    · exact ⟨Or.inl a,Or.inl b⟩
    · exact ⟨Or.inr same,Or.inr same.symm⟩

/-- Independent names include ordinary-only seeds and reciprocal original edges.
Associated steps use original structural occurrences and declaration judgments. -/
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) : Nat → Inference.Base → Prop
  | initial {i b} : Evidence s.atoms i b → Derives env roles p extra s (name p extra i) b
  | transfer {i j b} : Linked s i j → Derives env roles p extra s (name p extra j) b →
      Derives env roles p extra s (name p extra i) b
  | associated (q : Occurrence) {head result} : q ∈ p →
      Derives env roles p extra s q.receiver head → Step env roles q head result →
      Derives env roles p extra s q.output result

theorem allocated_to_named (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) (f : Fact (table p extra).length)
    (h : CommonRoleMixedEvidenceClosure.Derives env roles (source p extra) (prepared p extra s) f) :
    Derives env roles p extra s (name p extra f.1) f.2 := by
  induction h with
  | initial evidence => exact .initial ((prepared_evidence ..).mp evidence)
  | @identity i j b same _ ih =>
    change name p extra i = name p extra j at same
    simpa only [same] using ih
  | @transfer i j b linked _ ih =>
    rcases (prepared_linked p extra s i j).mp linked with old | same
    · exact .transfer old ih
    · simpa only [same] using ih
  | @associated q head result member _ computed ih =>
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    have step : Step env roles p[i.val] head result :=
      (CommonRoleStructuralAssociatedTemplates.step_exact env roles p[i.val] head result).mp computed
    have result := Derives.associated (p := p) (extra := extra) (s := s) p[i.val] (List.getElem_mem i.isLt)
      (by simpa only [occurrence,receiver_source] using ih) step
    simpa only [occurrence,output_source] using result

theorem named_to_allocated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) (a : Nat) (b : Inference.Base)
    (h : Derives env roles p extra s a b) : ∀ slot : Slot (table p extra), name p extra slot = a →
      CommonRoleMixedEvidenceClosure.Derives env roles (source p extra) (prepared p extra s) (slot,b) := by
  induction h with
  | @initial i b evidence =>
    intro slot target
    exact .identity target.symm (.initial ((prepared_evidence ..).mpr evidence))
  | @transfer i j b linked _ ih =>
    intro slot target
    exact .identity target.symm (.transfer ((prepared_linked ..).mpr (Or.inl linked)) (ih j rfl))
  | @associated q head result member _ step ih =>
    intro slot target
    obtain ⟨i,bound,same⟩ := List.getElem_of_mem member
    let j : Fin p.length := ⟨i,bound⟩
    have recv : name p extra (receiver p extra j) = q.receiver := by rw [receiver_source]; exact congrArg Occurrence.receiver same
    have out : name p extra (output p extra j) = q.output := by rw [output_source]; exact congrArg Occurrence.output same
    have computed : CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles
        (CommonRoleFiniteAssociatedClosure.request (occurrence p extra j) head) result := by
      have h := (CommonRoleStructuralAssociatedTemplates.step_exact env roles q head result).mpr step
      simpa only [occurrence,CommonRoleFiniteAssociatedClosure.request,j,same,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed,
        CommonRoleNamedAssociatedSourceModels.Associated,
        CommonRoleStructuralAssociatedTemplates.Occurrence.compile] using h
    have result : CommonRoleMixedEvidenceClosure.Derives env roles (source p extra)
        (prepared p extra s) (output p extra j,result) :=
      .associated (q := occurrence p extra j) (List.mem_map.mpr ⟨j,by simp,rfl⟩)
        (ih (receiver p extra j) recv) computed
    exact .identity (out.trans target.symm) result

theorem allocated_named_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) (f : Fact (table p extra).length) :
    CommonRoleMixedEvidenceClosure.Derives env roles (source p extra) (prepared p extra s) f ↔
      Derives env roles p extra s (name p extra f.1) f.2 :=
  ⟨allocated_to_named env roles p extra s f,
    fun h => named_to_allocated env roles p extra s _ _ h f.1 rfl⟩

theorem named_support (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) (a : Nat) (b : Inference.Base)
    (h : Derives env roles p extra s a b) : ∃ slot : Slot (table p extra), name p extra slot = a := by
  cases h with
  | initial => exact ⟨_,rfl⟩
  | transfer => exact ⟨_,rfl⟩
  | associated q member _ _ =>
    obtain ⟨i,bound,same⟩ := List.getElem_of_mem member
    exact ⟨output p extra ⟨i,bound⟩,(output_source ..).trans (congrArg Occurrence.output same)⟩

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) :=
  CommonRoleMixedEvidenceClosure.completed env roles wf (source p extra) (prepared p extra s)

theorem run_evidence_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (extra : List Nat) (s : State (table p extra).length)
    (i : Slot (table p extra)) (b : Inference.Base) :
    Evidence (run env roles wf p extra s).atoms i b ↔ Derives env roles p extra s (name p extra i) b :=
  (CommonRoleMixedEvidenceClosure.completed_evidence env roles wf awf ..).trans
    (allocated_named_exact env roles p extra s (i,b))

/-- Exact models share one source type valuation across occurrence and ordinary
slots, including unseeded aliases. Effects remain separate. -/
theorem run_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (extra : List Nat) (s : State (table p extra).length)
    (v : Slot (table p extra) → Comp Common.model) :
    All Common.model v (run env roles wf p extra s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p extra) v values ∧
        ∀ a b, Derives env roles p extra s a b → Common.Equivalent (values a) (.base b) := by
  rw [run,CommonRoleMixedEvidenceClosure.completed_models env roles wf awf,
    prepared,CommonRoleSourceIdentity.extend_exact]
  constructor
  · rintro ⟨⟨old,coherent⟩,equations⟩
    obtain ⟨values,factor⟩ := (CommonRoleSourceDescent.factorization_exact (table p extra) v).mp coherent
    refine ⟨old,values,factor,?_⟩
    intro a b derived
    obtain ⟨slot,same⟩ := named_support env roles p extra s a b derived
    have eq := equations (slot,b) (named_to_allocated env roles p extra s a b derived slot same)
    have result := Common.equivalent_trans (Common.equivalent_symm (factor slot)) eq
    simpa only [← same] using result
  · rintro ⟨old,values,factor,equations⟩
    refine ⟨⟨old,CommonRoleSourceDescent.factors_coherent (table p extra) v values factor⟩,?_⟩
    intro f derived
    exact Common.equivalent_trans (factor f.1)
      (equations _ _ (allocated_to_named env roles p extra s f derived))

theorem solver_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (extra : List Nat) (s : State (table p extra).length) :
    CommonRoleOpenPropagation.consistent (run env roles wf p extra s) = true ↔
      ∃ v : Slot (table p extra) → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p extra) v values ∧
          ∀ a b, Derives env roles p extra s a b → Common.Equivalent (values a) (.base b) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_exact env roles wf awf p extra s)

theorem capacity (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (extra : List Nat) (s : State (table p extra).length) :
    (CommonRoleMixedEvidenceClosure.saturate env roles wf (source p extra) (prepared p extra s)).length ≤
      4 * (2 * p.length + extra.length) := by
  have h := CommonRoleMixedEvidenceClosure.saturate_bounded env roles wf (source p extra) (prepared p extra s)
  have len : (table p extra).length = 2 * p.length + extra.length := by
    simp [table,CommonRoleStructuralAssociatedTemplates.table,
      CommonRoleNamedAssociatedGraph.table_length,compile]
  exact Nat.le_trans h (by rw [len]; omega)

/-- Raw program checks do not imply ordinary consistency. -/
theorem checked_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (raw : CommonRoleCheckedAssociatedPrograms.RawProgram) (p : Program)
    (checked : CommonRoleCheckedAssociatedPrograms.check roles raw = some p)
    (extra : List Nat) (s : State (table p extra).length) (v : Slot (table p extra) → Comp Common.model) :
    CommonRoleCheckedAssociatedPrograms.eraseProgram p = raw ∧
      CommonRoleCheckedAssociatedPrograms.ValidProgram roles raw ∧
      (All Common.model v (run env roles wf p extra s).atoms ↔
        All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p extra) v values ∧
          ∀ a b, Derives env roles p extra s a b → Common.Equivalent (values a) (.base b)) :=
  ⟨((CommonRoleCheckedAssociatedPrograms.check_exact roles raw p).mp checked).1,
    ((CommonRoleCheckedAssociatedPrograms.check_exact roles raw p).mp checked).2,
    run_source_exact env roles wf awf p extra s v⟩

end Yulang.CommonRoleAmbientMixedSource
