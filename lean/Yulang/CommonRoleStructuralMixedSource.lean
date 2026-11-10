import Yulang.CommonRoleCheckedAssociatedPrograms
import Yulang.CommonRoleMixedEvidenceReplay

/-! Checked structural programs feed mixed associated/ordinary closure with
computed slots and physical source type identities. Finite occurrence selection,
scope-resolved names and old grammar-valid states remain source boundaries. -/
namespace Yulang.CommonRoleStructuralMixedSource
open CommonRoleStructuralAssociatedTemplates (Program Occurrence compile table Step)
open CommonRoleNamedAssociatedSourceModels (Seed receiver output occurrence source prepared)
open CommonRoleSettledConstraints (State)
open CommonRoleSourceIdentity (Slot)
open CommonRoleFiniteAssociatedClosure (Fact)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleEvidenceSaturation (Linked)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)

abbrev name (p : Program) (i : Slot (table p)) := CommonRoleSourceIdentity.source (table p) i

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

/-- Physical sharing adds exactly same-name edges, including unseeded classes. -/
theorem prepared_linked (p : Program) (s : State (table p).length) (i j : Slot (table p)) :
    Linked (prepared (compile p) s) i j ↔ Linked s i j ∨ name p i = name p j := by
  simp only [Linked,prepared,CommonRoleSourceIdentity.extend,List.mem_append,identity_edge]
  change (_ ∨ name p i = name p j) ∧ (_ ∨ name p j = name p i) ↔ _
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

/-- Independent source-name closure: no executable resolver or generated slots
occur in the associated step; ordinary transfer uses only the original state. -/
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) : Nat → Inference.Base → Prop
  | initial {a b} : Seed (compile p) s a b → Derives env roles p s a b
  | transfer {i j b} : Linked s i j → Derives env roles p s (name p j) b →
      Derives env roles p s (name p i) b
  | associated (q : Occurrence) {head result} : q ∈ p →
      Derives env roles p s q.receiver head → Step env roles q head result →
      Derives env roles p s q.output result

/-- Allocation soundness for arbitrary finite programs, including cycles. -/
theorem allocated_to_named (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (f : Fact (table p).length)
    (h : CommonRoleMixedEvidenceClosure.Derives env roles (source (compile p))
      (prepared (compile p) s) f) : Derives env roles p s (name p f.1) f.2 := by
  induction h with
  | initial evidence =>
    exact .initial ⟨_,rfl,(CommonRoleNamedAssociatedSourceModels.prepared_evidence ..).mp evidence⟩
  | @identity i j b same _ ih =>
    change name p i = name p j at same
    simpa only [same] using ih
  | @transfer i j b linked _ ih =>
    rcases (prepared_linked p s i j).mp linked with old | same
    · exact .transfer old ih
    · simpa only [same] using ih
  | @associated q head result member _ computed ih =>
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    have bound : i.val < p.length := by simpa [compile] using i.isLt
    have lookup : (compile p)[i.val] = (p[i.val]'bound).compile := by simp [compile]
    have step := (CommonRoleStructuralAssociatedTemplates.step_exact env roles p[i.val] head result).mp
      (show CommonRoleNamedAssociatedSourceModels.Associated env roles (p[i.val]'bound).compile head result from
        by simpa only [occurrence,lookup,CommonRoleAssociatedDeclarationExact.DeclarativeComputed,
          CommonRoleFiniteAssociatedClosure.request,CommonRoleNamedAssociatedSourceModels.Associated] using computed)
    have input : Derives env roles p s p[i.val].receiver head := by
      simpa only [name,occurrence,CommonRoleNamedAssociatedSourceModels.receiver_source,lookup,
        CommonRoleStructuralAssociatedTemplates.Occurrence.compile] using ih
    have result := Derives.associated p[i.val] (by simp) input step
    simpa only [name,occurrence,CommonRoleNamedAssociatedSourceModels.output_source,lookup,
      CommonRoleStructuralAssociatedTemplates.Occurrence.compile] using result

/-- Every allocated occurrence of a derived source name receives the fact. -/
theorem named_to_allocated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (a : Nat) (b : Inference.Base)
    (h : Derives env roles p s a b) : ∀ slot : Slot (table p), name p slot = a →
      CommonRoleMixedEvidenceClosure.Derives env roles (source (compile p))
        (prepared (compile p) s) (slot,b) := by
  induction h with
  | initial seed =>
    obtain ⟨origin,same,evidence⟩ := seed
    intro slot target
    exact .identity (same.trans target.symm)
      (.initial ((CommonRoleNamedAssociatedSourceModels.prepared_evidence ..).mpr evidence))
  | @transfer i j b linked _ ih =>
    intro slot target
    have result := CommonRoleMixedEvidenceClosure.Derives.transfer
      ((prepared_linked p s i j).mpr (Or.inl linked)) (ih j rfl)
    exact .identity target.symm result
  | @associated q head result member _ step ih =>
    intro slot target
    obtain ⟨i,bound,same⟩ := List.getElem_of_mem member
    let j : Fin (compile p).length := ⟨i,by simpa [compile] using bound⟩
    have lookup : (compile p)[j.val] = q.compile := by simp [compile,j,same]
    have recv : name p (receiver (compile p) j) = q.receiver := by
      simp only [name,CommonRoleNamedAssociatedSourceModels.receiver_source,lookup,
        CommonRoleStructuralAssociatedTemplates.Occurrence.compile]
    have out : name p (output (compile p) j) = q.output := by
      simp only [name,CommonRoleNamedAssociatedSourceModels.output_source,lookup,
        CommonRoleStructuralAssociatedTemplates.Occurrence.compile]
    have result : CommonRoleMixedEvidenceClosure.Derives env roles (source (compile p))
        (prepared (compile p) s) (output (compile p) j,result) :=
      .associated (q := occurrence (compile p) j) (List.mem_map.mpr ⟨j,by simp,rfl⟩)
        (ih (receiver (compile p) j) recv)
        (by simpa only [occurrence,lookup,CommonRoleAssociatedDeclarationExact.DeclarativeComputed,
          CommonRoleFiniteAssociatedClosure.request,CommonRoleNamedAssociatedSourceModels.Associated] using
          (CommonRoleStructuralAssociatedTemplates.step_exact env roles q head result).mpr step)
    exact .identity (out.trans target.symm) result

theorem allocated_named_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (f : Fact (table p).length) :
    CommonRoleMixedEvidenceClosure.Derives env roles (source (compile p))
      (prepared (compile p) s) f ↔ Derives env roles p s (name p f.1) f.2 :=
  ⟨allocated_to_named env roles p s f,
    fun h => named_to_allocated env roles p s _ _ h f.1 rfl⟩

theorem named_support (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (a : Nat) (b : Inference.Base)
    (h : Derives env roles p s a b) : ∃ slot : Slot (table p), name p slot = a := by
  cases h with
  | initial seed => obtain ⟨slot,same,_⟩ := seed; exact ⟨slot,same⟩
  | @transfer i _ _ _ _ => exact ⟨i,rfl⟩
  | @associated q head result member _ _ =>
    obtain ⟨i,bound,same⟩ := List.getElem_of_mem member
    let j : Fin (compile p).length := ⟨i,by simpa [compile] using bound⟩
    refine ⟨output (compile p) j,?_⟩
    change CommonRoleSourceIdentity.source (CommonRoleNamedAssociatedGraph.table (compile p))
      (output (compile p) j) = q.output
    rw [CommonRoleNamedAssociatedSourceModels.output_source]
    simp [compile,j,same,CommonRoleStructuralAssociatedTemplates.Occurrence.compile]

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (table p).length) :=
  CommonRoleMixedEvidenceClosure.completed env roles wf (source (compile p)) (prepared (compile p) s)

theorem run_evidence_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (i : Slot (table p)) (b : Inference.Base) :
    Evidence (run env roles wf p s).atoms i b ↔ Derives env roles p s (name p i) b :=
  (CommonRoleMixedEvidenceClosure.completed_evidence env roles wf awf ..).trans
    (allocated_named_exact env roles p s (i,b))

/-- Exact models use a single source valuation, even for unseeded names.
Only type components are shared; original effect constraints are preserved. -/
theorem run_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (v : Slot (table p) → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
        ∀ a b, Derives env roles p s a b → Common.Equivalent (values a) (.base b) := by
  rw [run,CommonRoleMixedEvidenceClosure.completed_models env roles wf awf]
  rw [show prepared (compile p) s = CommonRoleSourceIdentity.extend (table p) s from rfl,
    CommonRoleSourceIdentity.extend_exact]
  constructor
  · rintro ⟨⟨old,coherent⟩,equations⟩
    obtain ⟨values,factor⟩ := (CommonRoleSourceDescent.factorization_exact (table p) v).mp coherent
    refine ⟨old,values,factor,?_⟩
    intro a b derived
    obtain ⟨slot,same⟩ := named_support env roles p s a b derived
    have eq := equations (slot,b) (named_to_allocated env roles p s a b derived slot same)
    have result := Common.equivalent_trans (Common.equivalent_symm (factor slot)) eq
    simpa only [← same] using result
  · rintro ⟨old,values,factor,equations⟩
    refine ⟨⟨old,CommonRoleSourceDescent.factors_coherent (table p) v values factor⟩,?_⟩
    intro f derived
    exact Common.equivalent_trans (factor f.1)
      (equations _ _ (allocated_to_named env roles p s f derived))

theorem solver_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) :
    CommonRoleOpenPropagation.consistent (run env roles wf p s) = true ↔
      ∃ v : Slot (table p) → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
          ∀ a b, Derives env roles p s a b → Common.Equivalent (values a) (.base b) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_exact env roles wf awf p s)

/-- Capacity is computed from the source, not a supplied finite-domain oracle. -/
theorem capacity (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (table p).length) :
    (CommonRoleMixedEvidenceClosure.saturate env roles wf
      (source (compile p)) (prepared (compile p) s)).length ≤ 8 * p.length := by
  have h := CommonRoleMixedEvidenceClosure.saturate_bounded env roles wf
    (source (compile p)) (prepared (compile p) s)
  have len : (table p).length = 2 * p.length := by
    simp [table,CommonRoleNamedAssociatedGraph.table_length,compile]
  exact Nat.le_trans h (by change (table p).length * 4 ≤ 8 * p.length; omega)

/-- Raw validation and mixed solver correctness are separate properties. -/
theorem checked_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (raw : CommonRoleCheckedAssociatedPrograms.RawProgram) (p : Program)
    (checked : CommonRoleCheckedAssociatedPrograms.check roles raw = some p)
    (s : State (table p).length) (v : Slot (table p) → Comp Common.model) :
    CommonRoleCheckedAssociatedPrograms.eraseProgram p = raw ∧
      CommonRoleCheckedAssociatedPrograms.ValidProgram roles raw ∧
      (All Common.model v (run env roles wf p s).atoms ↔
        All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
          ∀ a b, Derives env roles p s a b → Common.Equivalent (values a) (.base b)) :=
  ⟨((CommonRoleCheckedAssociatedPrograms.check_exact roles raw p).mp checked).1,
    ((CommonRoleCheckedAssociatedPrograms.check_exact roles raw p).mp checked).2,
    run_source_exact env roles wf awf p s v⟩

end Yulang.CommonRoleStructuralMixedSource
