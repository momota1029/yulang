import Yulang.CommonRoleSourceRoleObligations

/-!
# Evidence-backed source role readiness after associated saturation

The finite allocation retains bare receivers and equation endpoints. The head
map is computed from explicit paired evidence, never chosen by the caller.
This is not general source inference or final language diagnostic classification.
-/
namespace Yulang.CommonRoleSourceStateDischarge
open Roles
open CommonRoleSourceRoleObligations (Package Obligation raw erase Discharges)
open CommonRoleAssociatedClauseExtraction (Source Clause)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence candidates)
open CommonRoleFiniteAssociatedClosure (Occurrence)
open CommonRoleFiniteAssociatedDeclaration (DeclarativeDerives)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev equationProgram (p : Package) :=
  CommonRoleStructuralAssociatedTemplates.compile p.equations
abbrev equationTable (p : Package) :=
  CommonRoleStructuralAssociatedTemplates.table p.equations

def table (p : Package) : List Nat := p.obligations.map (·.receiver) ++ equationTable p

def roleSlot (p : Package) (i : Fin p.obligations.length) : Fin (table p).length :=
  ⟨i.val, by simp only [table, List.length_append, List.length_map]; omega⟩

def equationSlot (p : Package) (i : Fin (equationTable p).length) : Fin (table p).length :=
  ⟨p.obligations.length + i.val, by
    simp only [table, List.length_append, List.length_map]; omega⟩

theorem role_source (p : Package) (i : Fin p.obligations.length) :
    CommonRoleSourceIdentity.source (table p) (roleSlot p i) = p.obligations[i.val].receiver := by
  simp [CommonRoleSourceIdentity.source, table, roleSlot, List.getElem_append_left]

theorem equation_source (p : Package) (i : Fin (equationTable p).length) :
    CommonRoleSourceIdentity.source (table p) (equationSlot p i) =
      CommonRoleSourceIdentity.source (equationTable p) i := by
  simp [CommonRoleSourceIdentity.source, table, equationSlot, List.getElem_append_right]

def liftOccurrence (p : Package) (q : Occurrence (equationTable p).length) :
    Occurrence (table p).length :=
  ⟨equationSlot p q.receiver, equationSlot p q.output, q.name, q.template⟩

def occurrences (p : Package) : List (Occurrence (table p).length) :=
  (CommonRoleNamedAssociatedSourceModels.occurrences (equationProgram p)).map (liftOccurrence p)

def graph (p : Package) := CommonRoleFiniteAssociatedSourceModels.source (table p) (occurrences p)
def prepared (p : Package) (s : State (table p).length) := CommonRoleSourceIdentity.extend (table p) s

def runState (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (p : Package) (s : State (table p).length) : State (table p).length :=
  CommonRoleFiniteAssociatedSourceModels.run env roles wf (table p) (occurrences p) s

/-- Independent graph derivation; no computed evidence or executable resolver. -/
def Derives (env : AssocEnv) (roles : RoleDecls) (p : Package)
    (s : State (table p).length) (slot : Fin (table p).length) (head : Inference.Base) : Prop :=
  DeclarativeDerives env roles (graph p) (prepared p s) (slot, head)

/-- Every role, including a bare one, receives a real slot in the joint table. -/
theorem slot_count (p : Package) :
    (table p).length = p.obligations.length + 2 * p.equations.length := by
  simp [table, equationTable, CommonRoleStructuralAssociatedTemplates.table,
    CommonRoleNamedAssociatedGraph.table_length, CommonRoleStructuralAssociatedTemplates.compile]

/-- Every equation keeps the same source identity after the shift. -/
theorem equation_identity (p : Package) (a b : Fin (equationTable p).length) :
    (graph p).identity (equationSlot p a) = (graph p).identity (equationSlot p b) ↔
      CommonRoleSourceIdentity.source (equationTable p) a =
        CommonRoleSourceIdentity.source (equationTable p) b := by
  change CommonRoleSourceIdentity.source _ _ = CommonRoleSourceIdentity.source _ _ ↔ _
  rw [equation_source, equation_source]

/-- No successful-run or model premise is required for evidence exactness. -/
theorem run_evidence_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Package) (s : State (table p).length) (slot : Fin (table p).length)
    (head : Inference.Base) :
    Evidence (runState env roles wf p s).atoms slot head ↔ Derives env roles p s slot head :=
  CommonRoleFiniteAssociatedDeclaration.run_declaration_exact env roles wf awf
    (graph p) (prepared p s) slot head

/-- Every output model is exactly an old model with source identities and all
independently derived scalar facts. Effects are preserved, not identified. -/
theorem run_models_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Package) (s : State (table p).length)
    (v : Fin (table p).length → Comp Common.model) :
    All Common.model v (runState env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ CommonRoleSourceIdentity.Coherent (table p) v ∧
        ∀ slot head, Derives env roles p s slot head → Common.Equivalent (v slot).1 (.base head) := by
  rw [runState, CommonRoleFiniteAssociatedSourceModels.run_models_exact env roles wf awf]
  simp only [Derives, graph, prepared]
  constructor
  · rintro ⟨old, coherent, h⟩
    exact ⟨old, coherent, fun slot head fact => h (slot, head) fact⟩
  · rintro ⟨old, coherent, h⟩
    exact ⟨old, coherent, fun fact derived => h fact.1 fact.2 derived⟩

def runOne (impls : List Impl) (wf : WellFormed impls) (p : Package)
    (out : State (table p).length) (i : Fin p.obligations.length) : Bool :=
  (candidates out.atoms (roleSlot p i)).any fun head =>
    CommonRoleSourceRoleObligations.runOne impls wf (fun _ => head) p.obligations[i.val]

def runRoles (impls : List Impl) (wf : WellFormed impls) (p : Package)
    (out : State (table p).length) : Bool :=
  (List.finRange p.obligations.length).all (runOne impls wf p out)

def ready (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (p : Package) (s : State (table p).length) : Bool :=
  let out := runState env roles wf p s
  CommonRoleOpenPropagation.consistent out && runRoles env.cores wf p out

/-- Independent state-backed discharge for one original source clause. -/
def Supported (env : AssocEnv) (roles : RoleDecls) (p : Package)
    (s : State (table p).length) (c : Clause) : Prop :=
  ∃ i : Fin p.obligations.length, erase p.obligations[i.val] = raw c ∧
    ∃ head, Derives env roles p s (roleSlot p i) head ∧
      Discharges env.cores (fun _ => head) c

/-- All heads are recovered from the computed saturation, not supplied maps. -/
theorem run_one_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Package) (s : State (table p).length) (i : Fin p.obligations.length)
    (c : Clause) (same : erase p.obligations[i.val] = raw c) :
    runOne env.cores wf p (runState env roles wf p s) i = true ↔
      ∃ head, Derives env roles p s (roleSlot p i) head ∧
        Discharges env.cores (fun _ => head) c := by
  simp only [runOne, List.any_eq_true, CommonRoleOrdinaryKnownness.candidates_exact,
    run_evidence_exact env roles wf awf,
    CommonRoleSourceRoleObligations.run_one_exact env.cores wf _ _ c same]

/-- Shared receivers carry identical derived evidence, even at bare positions. -/
theorem derives_same_receiver (env : AssocEnv) (roles : RoleDecls)
    (p : Package) (s : State (table p).length) (i j : Fin p.obligations.length)
    (same : p.obligations[i.val].receiver = p.obligations[j.val].receiver)
    (head : Inference.Base) :
    Derives env roles p s (roleSlot p i) head ↔ Derives env roles p s (roleSlot p j) head := by
  have identity : (graph p).identity (roleSlot p i) = (graph p).identity (roleSlot p j) := by
    change CommonRoleSourceIdentity.source _ _ = CommonRoleSourceIdentity.source _ _
    rw [role_source, role_source, same]
  exact ⟨fun h => .identity identity h, fun h => .identity identity.symm h⟩

/-- Exact source-level conjunction after one joint saturation and solver check. -/
theorem ready_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) :
    ready env roles wf p s = true ↔
      (runState env roles wf p s).Models ∧ ∀ c ∈ src, Supported env roles p s c := by
  simp only [ready, Bool.and_eq_true, CommonRoleOpenPropagation.consistent_exact,
    runRoles, List.all_eq_true, List.mem_finRange, forall_const]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    obtain ⟨o, ho, same⟩ := (CommonRoleSourceRoleObligations.checked_occurs roles src p checked (raw c)).mpr
      ⟨c, hc, rfl⟩
    obtain ⟨n, bound, eq⟩ := List.getElem_of_mem ho
    let i : Fin p.obligations.length := ⟨n, bound⟩
    have same' : erase p.obligations[i.val] = raw c := by simpa [i, eq] using same
    exact ⟨i, same', (run_one_exact env roles wf awf p s i c same').mp (h i)⟩
  · intro h i
    obtain ⟨c, hc, same⟩ := (CommonRoleSourceRoleObligations.checked_occurs roles src p checked
      (erase p.obligations[i.val])).mp ⟨_, by simp, rfl⟩
    obtain ⟨j, jsame, head, derived, discharged⟩ := h c hc
    have same' := same.symm
    have receivers : p.obligations[j.val].receiver = p.obligations[i.val].receiver :=
      congrArg CommonRoleSourceRoleObligations.RawObligation.receiver (jsame.trans same'.symm)
    apply (run_one_exact env roles wf awf p s i c same').mpr
    exact ⟨head, (derives_same_receiver env roles p s j i receivers head).mp derived, discharged⟩

/-- Every generated equation is exactly one original checked equation. -/
theorem occurrence_origin (p : Package) (q : Occurrence (table p).length)
    (member : q ∈ occurrences p) :
    ∃ o ∈ p.equations,
      (graph p).identity q.receiver = o.receiver ∧
      (graph p).identity q.output = o.output ∧
      ∀ head result, CommonRoleAssociatedDeclarationExact.DeclarativeComputed
        env roles (CommonRoleFiniteAssociatedClosure.request q head) result ↔
          CommonRoleStructuralAssociatedTemplates.Step env roles o head result := by
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp member
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq'
  have bound : j.val < p.equations.length := by
    simpa [equationProgram, CommonRoleStructuralAssociatedTemplates.compile] using j.isLt
  let o := p.equations[j.val]'bound
  have lookup : (equationProgram p)[j.val] = o.compile := by
    simp [equationProgram, CommonRoleStructuralAssociatedTemplates.compile, o]
  refine ⟨o, by simp [o], ?_, ?_, ?_⟩
  · change CommonRoleSourceIdentity.source _ (equationSlot p _) = _
    rw [equation_source]
    change CommonRoleSourceIdentity.source _ (CommonRoleNamedAssociatedSourceModels.receiver (equationProgram p) j) = _
    rw [CommonRoleNamedAssociatedSourceModels.receiver_source, lookup]
    rfl
  · change CommonRoleSourceIdentity.source _ (equationSlot p _) = _
    rw [equation_source]
    change CommonRoleSourceIdentity.source _ (CommonRoleNamedAssociatedSourceModels.output (equationProgram p) j) = _
    rw [CommonRoleNamedAssociatedSourceModels.output_source, lookup]
    rfl
  · intro head result
    change (argsBound ((equationProgram p)[j.val].template head).args = 0 ∧
      RoleConstraints.Resolves env.cores ((equationProgram p)[j.val].template head) ∧
      ∃ rhs, AssocDerives env roles ((equationProgram p)[j.val].template head)
        (equationProgram p)[j.val].name rhs ∧
        CommonRoleAssociatedStateFlow.scalar rhs = some result) ↔ _
    rw [lookup]
    exact CommonRoleStructuralAssociatedTemplates.step_exact env roles o head result

/-- Conversely every checked equation is included in the joint graph. -/
theorem occurrence_present (p : Package)
    (o : CommonRoleStructuralAssociatedTemplates.Occurrence) (member : o ∈ p.equations) :
    ∃ q ∈ occurrences p,
      (graph p).identity q.receiver = o.receiver ∧
      (graph p).identity q.output = o.output ∧
      ∀ head result, CommonRoleAssociatedDeclarationExact.DeclarativeComputed
        env roles (CommonRoleFiniteAssociatedClosure.request q head) result ↔
          CommonRoleStructuralAssociatedTemplates.Step env roles o head result := by
  obtain ⟨n, bound, same⟩ := List.getElem_of_mem member
  let j : Fin (equationProgram p).length := ⟨n, by
    simpa [equationProgram, CommonRoleStructuralAssociatedTemplates.compile] using bound⟩
  let q := liftOccurrence p (CommonRoleNamedAssociatedSourceModels.occurrence (equationProgram p) j)
  have lookup : (equationProgram p)[j.val] = o.compile := by
    simp [equationProgram, CommonRoleStructuralAssociatedTemplates.compile, j, same]
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨j, by simp, rfl⟩, rfl⟩
  · change CommonRoleSourceIdentity.source _ (equationSlot p _) = _
    rw [equation_source]
    change CommonRoleSourceIdentity.source _ (CommonRoleNamedAssociatedSourceModels.receiver (equationProgram p) j) = _
    rw [CommonRoleNamedAssociatedSourceModels.receiver_source, lookup]
    rfl
  · change CommonRoleSourceIdentity.source _ (equationSlot p _) = _
    rw [equation_source]
    change CommonRoleSourceIdentity.source _ (CommonRoleNamedAssociatedSourceModels.output (equationProgram p) j) = _
    rw [CommonRoleNamedAssociatedSourceModels.output_source, lookup]
    rfl
  · intro head result
    change (argsBound ((equationProgram p)[j.val].template head).args = 0 ∧
      RoleConstraints.Resolves env.cores ((equationProgram p)[j.val].template head) ∧
      ∃ rhs, AssocDerives env roles ((equationProgram p)[j.val].template head)
        (equationProgram p)[j.val].name rhs ∧
        CommonRoleAssociatedStateFlow.scalar rhs = some result) ↔ _
    rw [lookup]
    exact CommonRoleStructuralAssociatedTemplates.step_exact env roles o head result

/-- Original source clauses, not graph edges or executable saturation. -/
inductive SourceDerives (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Package) (s : State (table p).length) : Nat → Inference.Base → Prop
  | initial (slot : Fin (table p).length) {head} : Evidence s.atoms slot head →
      SourceDerives env roles src p s (CommonRoleSourceIdentity.source (table p) slot) head
  | equation (c : Clause) (e : CommonRoleAssociatedClauseExtraction.Equation) {head result} :
      c ∈ src → e ∈ c.equations → SourceDerives env roles src p s c.receiver head →
      CommonRoleAssociatedClauseExtraction.Step env roles c e head result →
      SourceDerives env roles src p s e.output result

theorem prepared_evidence (p : Package) (s : State (table p).length)
    (slot : Fin (table p).length) (head : Inference.Base) :
    Evidence (prepared p s).atoms slot head ↔ Evidence s.atoms slot head := by
  simp only [prepared, CommonRoleSourceIdentity.extend, Evidence, List.mem_append,
    CommonRoleSourceIdentity.mem_atoms]
  simp [CommonRoleSourceIdentity.pairAtoms]

/-- Every allocated derived fact has a derivation on the original source. -/
theorem allocated_to_source (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) (slot : Fin (table p).length) (head : Inference.Base)
    (derived : Derives env roles p s slot head) :
    SourceDerives env roles src p s (CommonRoleSourceIdentity.source (table p) slot) head := by
  have equations := CommonRoleSourceRoleObligations.checked_equations roles src p checked
  have main : ∀ fact, DeclarativeDerives env roles (graph p) (prepared p s) fact →
      SourceDerives env roles src p s (CommonRoleSourceIdentity.source (table p) fact.1) fact.2 := by
    intro fact derived
    induction derived with
    | initial evidence => exact .initial _ ((prepared_evidence p s _ _).mp evidence)
    | identity same _ ih =>
      change CommonRoleSourceIdentity.source (table p) _ = CommonRoleSourceIdentity.source (table p) _ at same
      simpa only [same] using ih
    | @associated q head result member _ computed ih =>
      obtain ⟨o, ho, receiver, output, step⟩ := occurrence_origin p q member (env := env) (roles := roles)
      have rawMember : CommonRoleCheckedAssociatedPrograms.erase o ∈ CommonRoleAssociatedClauseExtraction.lower src := by
        rw [← ((CommonRoleAssociatedClauseExtraction.check_exact roles src p.equations).mp equations).1]
        exact List.mem_map.mpr ⟨o, ho, rfl⟩
      obtain ⟨c, hc, mapped⟩ := List.mem_flatMap.mp rawMember
      obtain ⟨e, he, reverse⟩ := List.mem_map.mp mapped
      have same := reverse.symm
      have recv : o.receiver = c.receiver := congrArg CommonRoleCheckedAssociatedPrograms.RawOccurrence.receiver same
      have out : o.output = e.output := congrArg CommonRoleCheckedAssociatedPrograms.RawOccurrence.output same
      rw [show CommonRoleSourceIdentity.source (table p) q.output = e.output from output.trans out]
      change SourceDerives env roles src p s ((graph p).identity q.receiver) head at ih
      rw [receiver, recv] at ih
      exact .equation c e hc he ih
        ((CommonRoleAssociatedClauseExtraction.step_exact env roles c e o same head result).mp
          ((step head result).mp computed))
  exact main (slot, head) derived

/-- Every original source derivation reaches every occurrence of its name. -/
theorem source_to_allocated (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) (name : Nat) (head : Inference.Base)
    (derived : SourceDerives env roles src p s name head) :
    ∀ slot : Fin (table p).length, CommonRoleSourceIdentity.source (table p) slot = name →
      Derives env roles p s slot head := by
  have equations := CommonRoleSourceRoleObligations.checked_equations roles src p checked
  induction derived with
  | initial origin evidence =>
    intro slot same
    exact .identity same.symm (.initial ((prepared_evidence p s origin _).mpr evidence))
  | @equation c e head result hc he _ step ih =>
    obtain ⟨o, ho, same⟩ := (CommonRoleAssociatedClauseExtraction.checked_occurs roles src p.equations
      equations (CommonRoleAssociatedClauseExtraction.row c e)).mpr (.equation c e hc he)
    obtain ⟨q, hq, receiver, output, computed⟩ := occurrence_present p o ho (env := env) (roles := roles)
    have recv : o.receiver = c.receiver := congrArg CommonRoleCheckedAssociatedPrograms.RawOccurrence.receiver same
    have out : o.output = e.output := congrArg CommonRoleCheckedAssociatedPrograms.RawOccurrence.output same
    have fact : Derives env roles p s q.output result := .associated hq
      (ih q.receiver (receiver.trans recv))
      ((computed head result).mpr
        ((CommonRoleAssociatedClauseExtraction.step_exact env roles c e o same head result).mpr step))
    intro slot target
    exact .identity ((output.trans out).trans target.symm) fact

/-- Exact source evidence after joint saturation, including bare receivers. -/
theorem run_source_evidence_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) (slot : Fin (table p).length) (head : Inference.Base) :
    Evidence (runState env roles wf p s).atoms slot head ↔
      SourceDerives env roles src p s (CommonRoleSourceIdentity.source (table p) slot) head := by
  rw [run_evidence_exact env roles wf awf]
  exact ⟨allocated_to_source env roles src p checked s slot head,
    fun h => source_to_allocated env roles src p checked s _ head h slot rfl⟩

/-- Joint readiness against original source derivations, with no head map. -/
theorem ready_original_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) :
    ready env roles wf p s = true ↔ (runState env roles wf p s).Models ∧
      ∀ c ∈ src, ∃ head, SourceDerives env roles src p s c.receiver head ∧
        Discharges env.cores (fun _ => head) c := by
  rw [ready_source_exact env roles wf awf src p checked]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    obtain ⟨i, same, head, derived, discharged⟩ := h c hc
    have receiver : p.obligations[i.val].receiver = c.receiver :=
      congrArg CommonRoleSourceRoleObligations.RawObligation.receiver same
    refine ⟨head, ?_, discharged⟩
    have fact := allocated_to_source env roles src p checked s _ head derived
    simpa only [role_source, receiver] using fact
  · intro h c hc
    obtain ⟨head, derived, discharged⟩ := h c hc
    obtain ⟨o, ho, same⟩ := (CommonRoleSourceRoleObligations.checked_occurs roles src p checked (raw c)).mpr
      ⟨c, hc, rfl⟩
    obtain ⟨n, bound, eq⟩ := List.getElem_of_mem ho
    let i : Fin p.obligations.length := ⟨n, bound⟩
    have same' : erase p.obligations[i.val] = raw c := by simpa [i, eq] using same
    have receiver : p.obligations[i.val].receiver = c.receiver :=
      congrArg CommonRoleSourceRoleObligations.RawObligation.receiver same'
    refine ⟨i, same', head, ?_, discharged⟩
    apply source_to_allocated env roles src p checked s _ head derived
    rw [role_source, receiver]

/-- Independent models of original constraints, source identities and source
clause derivations. No emitted state or executable operation occurs here. -/
def SourceModels (env : AssocEnv) (roles : RoleDecls) (src : Source) (p : Package)
    (s : State (table p).length) : Prop :=
  ∃ v : Fin (table p).length → Comp Common.model,
    All Common.model v s.atoms ∧ CommonRoleSourceIdentity.Coherent (table p) v ∧
      ∀ slot head, SourceDerives env roles src p s
        (CommonRoleSourceIdentity.source (table p) slot) head →
          Common.Equivalent (v slot).1 (.base head)

/-- Solver models are exactly independent source models for this allocation. -/
theorem source_models_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) :
    (runState env roles wf p s).Models ↔ SourceModels env roles src p s := by
  unfold State.Models SourceModels
  apply exists_congr
  intro v
  rw [run_models_exact env roles wf awf]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h slot head derived
    exact h slot head (source_to_allocated env roles src p checked s _ head derived slot rfl)
  · intro h slot head derived
    exact h slot head (allocated_to_source env roles src p checked s slot head derived)

/-- The complete finite readiness equivalence has no executable result on its
independent side and no caller scalar map, model or successful-run premise. -/
theorem ready_declarative_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : CommonRoleSourceRoleObligations.check roles src = some p)
    (s : State (table p).length) :
    ready env roles wf p s = true ↔ SourceModels env roles src p s ∧
      ∀ c ∈ src, ∃ head, SourceDerives env roles src p s c.receiver head ∧
        Discharges env.cores (fun _ => head) c := by
  rw [ready_original_source_exact env roles wf awf src p checked,
    source_models_exact env roles wf awf src p checked]

/-- Inconsistent scalar evidence is rejected before it can certify a role. -/
theorem ready_has_models (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (p : Package) (s : State (table p).length)
    (accepted : ready env roles wf p s = true) : (runState env roles wf p s).Models := by
  simp only [ready, Bool.and_eq_true] at accepted
  exact (CommonRoleOpenPropagation.consistent_exact _).mp accepted.1

end Yulang.CommonRoleSourceStateDischarge
