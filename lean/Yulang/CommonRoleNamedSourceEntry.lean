import Yulang.CommonRoleSourceStateDischarge

/-!
# Finite source readiness from named scalar assumptions

The outer entry computes validation, allocation and initial ordinary atoms.
This fragment interprets only assumptions on names occurring in the source.
It does not infer those assumptions from expressions, preserve an arbitrary
old ordinary state, generate dynamic where children or classify diagnostics.
-/
namespace Yulang.CommonRoleNamedSourceEntry
open Roles
open CommonRoleAssociatedClauseExtraction (Source Clause Equation lower Step)
open CommonRoleSourceRoleObligations (Package ValidSource Discharges check build)
open CommonRoleSourceStateDischarge (table roleSlot equationSlot equationTable equationProgram)
open CommonRoleSourceIdentity (source)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev Assumptions := List (Nat × Inference.Base)

def names (src : Source) : List Nat :=
  src.map (·.receiver) ++ (lower src).flatMap (fun q => [q.receiver, q.output])

/-- Independent source-name facts, with no compiled package or ordinary state. -/
inductive Derives (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (input : Assumptions) : Nat → Inference.Base → Prop
  | initial {name head} : (name, head) ∈ input → Derives env roles src input name head
  | equation (c : Clause) (e : Equation) {head result} :
      c ∈ src → e ∈ c.equations → Derives env roles src input c.receiver head →
      Step env roles c e head result → Derives env roles src input e.output result

/-- One valuation of original source names satisfies all independently derived
facts in the source domain. Values of unmentioned names are not constrained. -/
def Models (env : AssocEnv) (roles : RoleDecls) (src : Source) (input : Assumptions) : Prop :=
  ∃ values : Nat → Common.Ty, ∀ name ∈ names src, ∀ head,
    Derives env roles src input name head → Common.Equivalent (values name) (.base head)

def initialFacts (p : Package) (input : Assumptions) :
    List (CommonRoleFiniteAssociatedClosure.Fact (table p).length) :=
  (CommonRoleFiniteAssociatedClosure.facts (table p).length).filter fun f =>
    (input.contains (source (table p) f.1, f.2))

def initialState (p : Package) (input : Assumptions) : State (table p).length :=
  CommonRoleFiniteAssociatedModels.emit (initialFacts p input) State.empty

theorem initial_facts_exact (p : Package) (input : Assumptions)
    (slot : Fin (table p).length) (head : Inference.Base) :
    (slot, head) ∈ initialFacts p input ↔ (source (table p) slot, head) ∈ input := by
  simp [initialFacts, CommonRoleFiniteAssociatedClosure.facts_complete]

/-- Named assumptions produce exactly their paired scalar evidence at every
occurrence of the same name; no caller slot map is needed. -/
theorem initial_evidence_exact (p : Package) (input : Assumptions)
    (slot : Fin (table p).length) (head : Inference.Base) :
    Evidence (initialState p input).atoms slot head ↔
      (source (table p) slot, head) ∈ input := by
  rw [initialState, CommonRoleFiniteAssociatedStable.emit_evidence]
  simp [Evidence, State.empty, initial_facts_exact]

theorem initial_models_exact (p : Package) (input : Assumptions)
    (v : Fin (table p).length → Comp Common.model) :
    All Common.model v (initialState p input).atoms ↔
      ∀ slot head, (source (table p) slot, head) ∈ input →
        Common.Equivalent (v slot).1 (.base head) := by
  rw [initialState, CommonRoleFiniteAssociatedModels.emit_models]
  simp only [State.empty, PresenceNormalForm.all_nil, true_and]
  constructor
  · intro h slot head mem
    exact h (slot, head) ((initial_facts_exact p input slot head).mpr mem)
  · intro h fact mem
    exact h fact.1 fact.2 ((initial_facts_exact p input fact.1 fact.2).mp mem)

private theorem named_table_member (program : CommonRoleNamedAssociatedGraph.Program) (name : Nat) :
    name ∈ CommonRoleNamedAssociatedGraph.table program ↔
      ∃ q ∈ program, name = q.receiver ∨ name = q.output := by
  simp only [CommonRoleNamedAssociatedGraph.table, List.mem_ofFn]
  constructor
  · rintro ⟨slot, same⟩
    obtain ⟨i, rfl | rfl⟩ := CommonRoleNamedAssociatedGraph.slot_origin program slot
    · exact ⟨program[i.val], by simp,
        Or.inl (same.symm.trans (CommonRoleNamedAssociatedGraph.receiver_identity program i))⟩
    · exact ⟨program[i.val], by simp,
        Or.inr (same.symm.trans (CommonRoleNamedAssociatedGraph.output_identity program i))⟩
  · rintro ⟨q, mem, h | h⟩ <;> obtain ⟨n, bound, eq⟩ := List.getElem_of_mem mem
    · exact ⟨CommonRoleNamedAssociatedGraph.receiver program ⟨n, bound⟩,
        (CommonRoleNamedAssociatedGraph.receiver_identity program ⟨n, bound⟩).trans (by simpa [eq] using h.symm)⟩
    · exact ⟨CommonRoleNamedAssociatedGraph.output program ⟨n, bound⟩,
        (CommonRoleNamedAssociatedGraph.output_identity program ⟨n, bound⟩).trans (by simpa [eq] using h.symm)⟩

/-- The computed allocation represents exactly the original finite name domain. -/
theorem table_names_exact (roles : RoleDecls) (src : Source) (p : Package)
    (checked : check roles src = some p) (name : Nat) :
    name ∈ table p ↔ name ∈ names src := by
  have h := (CommonRoleSourceRoleObligations.check_exact roles src p).mp checked
  have hr : p.obligations.map (·.receiver) = src.map (·.receiver) := by
    have eq := congrArg (List.map CommonRoleSourceRoleObligations.RawObligation.receiver) h.1
    simpa [List.map_map, Function.comp_def, CommonRoleSourceRoleObligations.erase, CommonRoleSourceRoleObligations.raw] using eq
  have he : name ∈ equationTable p ↔ name ∈ (lower src).flatMap (fun q => [q.receiver, q.output]) := by
    rw [equationTable, CommonRoleStructuralAssociatedTemplates.table, named_table_member,
      ← h.2.1]
    simp only [CommonRoleStructuralAssociatedTemplates.compile,
      CommonRoleCheckedAssociatedPrograms.eraseProgram, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨q, ⟨o, ho, rfl⟩, same⟩
      refine ⟨CommonRoleCheckedAssociatedPrograms.erase o, ⟨o, ho, rfl⟩, ?_⟩
      simpa [CommonRoleStructuralAssociatedTemplates.Occurrence.compile,
        CommonRoleCheckedAssociatedPrograms.erase] using same
    · rintro ⟨q, ⟨o, ho, rfl⟩, same⟩
      refine ⟨o.compile, ⟨o, ho, rfl⟩, ?_⟩
      simpa [CommonRoleStructuralAssociatedTemplates.Occurrence.compile,
        CommonRoleCheckedAssociatedPrograms.erase] using same
  simp only [table, names, List.mem_append, hr, he]

/-- Every original clause has a retained receiver occurrence. -/
theorem receiver_present (roles : RoleDecls) (src : Source) (p : Package)
    (checked : check roles src = some p) (c : Clause) (member : c ∈ src) :
    ∃ slot : Fin (table p).length, source (table p) slot = c.receiver := by
  have mem : c.receiver ∈ table p := (table_names_exact roles src p checked c.receiver).mpr
    (List.mem_append_left _ (List.mem_map.mpr ⟨c, member, rfl⟩))
  obtain ⟨n, bound, same⟩ := List.getElem_of_mem mem
  exact ⟨⟨n, bound⟩, same⟩

/-- Soundness from allocated evidence to original named assumptions and steps. -/
theorem allocated_to_named (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Package) (input : Assumptions) (name : Nat) (head : Inference.Base)
    (derived : CommonRoleSourceStateDischarge.SourceDerives env roles src p
      (initialState p input) name head) : Derives env roles src input name head := by
  induction derived with
  | initial slot evidence => exact .initial ((initial_evidence_exact p input slot _).mp evidence)
  | equation c e hc he _ step ih => exact .equation c e hc he ih step

/-- Completeness reaches every allocated occurrence, including bare receivers. -/
theorem named_to_allocated (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Package) (checked : check roles src = some p) (input : Assumptions)
    (name : Nat) (head : Inference.Base) (derived : Derives env roles src input name head) :
    ∀ slot : Fin (table p).length, source (table p) slot = name →
      CommonRoleSourceStateDischarge.SourceDerives env roles src p (initialState p input) name head := by
  induction derived with
  | initial mem =>
    intro slot same
    have h := CommonRoleSourceStateDischarge.SourceDerives.initial
      (env := env) (roles := roles) (src := src) (p := p) (s := initialState p input) slot
      ((initial_evidence_exact p input slot _).mpr (by simpa [same] using mem))
    simpa [same] using h
  | equation c e hc he _ step ih =>
    intro _ _
    obtain ⟨slot, same⟩ := receiver_present roles src p checked c hc
    exact .equation c e hc he (ih slot same) step

/-- Exact output evidence for arbitrary checked source and named assumptions. -/
theorem run_evidence_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p) (input : Assumptions)
    (slot : Fin (table p).length) (head : Inference.Base) :
    Evidence (CommonRoleSourceStateDischarge.runState env roles wf p (initialState p input)).atoms slot head ↔
      Derives env roles src input (source (table p) slot) head := by
  rw [CommonRoleSourceStateDischarge.run_source_evidence_exact env roles wf awf src p checked]
  exact ⟨allocated_to_named env roles src p input _ head,
    fun h => named_to_allocated env roles src p checked input _ head h slot rfl⟩


/-- Ordinary consistency of the generated state is exactly independent
source-name model existence, not a caller-chosen ordinary assignment. -/
theorem models_exact (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Package) (checked : check roles src = some p) (input : Assumptions) :
    CommonRoleSourceStateDischarge.SourceModels env roles src p (initialState p input) ↔
      Models env roles src input := by
  constructor
  · rintro ⟨v, _, coherent, facts⟩
    obtain ⟨values, factor⟩ := (CommonRoleSourceDescent.factorization_exact (table p) v).mp coherent
    refine ⟨values, ?_⟩
    intro name mem head derived
    have present := (table_names_exact roles src p checked name).mpr mem
    obtain ⟨n, bound, same⟩ := List.getElem_of_mem present
    let slot : Fin (table p).length := ⟨n, bound⟩
    have equal : source (table p) slot = name := same
    have scalar := facts slot head (by
      rw [equal]
      exact named_to_allocated env roles src p checked input name head derived slot equal)
    have descended := factor slot
    rw [equal] at descended
    exact Common.equivalent_trans (Common.equivalent_symm descended) scalar
  · rintro ⟨values, facts⟩
    let v : Fin (table p).length → Comp Common.model :=
      fun slot => Comp.pure Common.model (values (source (table p) slot))
    have present (slot : Fin (table p).length) : source (table p) slot ∈ names src :=
      (table_names_exact roles src p checked _).mp (List.getElem_mem slot.isLt)
    refine ⟨v, ?_, ?_, ?_⟩
    · apply (initial_models_exact p input v).mpr
      intro slot head mem
      exact facts _ (present slot) head (.initial mem)
    · intro left right same
      change Common.Equivalent (values (source (table p) left)) (values (source (table p) right))
      rw [same]
      exact Common.equivalent_refl _
    · intro slot head derived
      exact facts _ (present slot) head (allocated_to_named env roles src p input _ head derived)

/-- Checked internal entry, with an entirely source-named independent side. -/
theorem ready_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p) (input : Assumptions) :
    CommonRoleSourceStateDischarge.ready env roles wf p (initialState p input) = true ↔
      Models env roles src input ∧ ∀ c ∈ src, ∃ head,
        Derives env roles src input c.receiver head ∧ Discharges env.cores (fun _ => head) c := by
  rw [CommonRoleSourceStateDischarge.ready_declarative_exact env roles wf awf src p checked,
    models_exact env roles src p checked input]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    obtain ⟨head, derived, discharged⟩ := h c hc
    exact ⟨head, allocated_to_named env roles src p input _ head derived, discharged⟩
  · intro h c hc
    obtain ⟨head, derived, discharged⟩ := h c hc
    obtain ⟨slot, same⟩ := receiver_present roles src p checked c hc
    exact ⟨head, named_to_allocated env roles src p checked input _ head derived slot same, discharged⟩

/-- The public entry computes every package, slot and initial equality atom.
False denotes failure of this finite readiness check, not language rejection. -/
def runSource (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) (input : Assumptions) : Bool :=
  match check roles src with
  | none => false
  | some p => CommonRoleSourceStateDischarge.ready env roles wf p (initialState p input)

/-- Soundness and completeness for arbitrary finite sources and assumptions.
No accepted package, dependent state, successful run, fuel or model is an input.
Core/associated well-formedness and the finite fragment remain explicit. -/
theorem run_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (input : Assumptions) :
    runSource env roles wf src input = true ↔ ValidSource roles src ∧
      Models env roles src input ∧ ∀ c ∈ src, ∃ head,
        Derives env roles src input c.receiver head ∧ Discharges env.cores (fun _ => head) c := by
  unfold runSource
  cases checked : check roles src with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro valid
    have accepted := (CommonRoleSourceRoleObligations.check_accepts roles src).mpr valid
    simp [checked] at accepted
  | some p =>
    rw [ready_exact env roles wf awf src p checked]
    exact (and_iff_right ((CommonRoleSourceRoleObligations.check_exact roles src p).mp checked).2.2).symm

/-- Original derivations depend on membership, not source or assumption order. -/
theorem derives_transport (env : AssocEnv) (roles : RoleDecls) (src other : Source)
    (input more : Assumptions) (clauses : ∀ c, c ∈ src → c ∈ other)
    (seeds : ∀ f, f ∈ input → f ∈ more) (name : Nat) (head : Inference.Base)
    (derived : Derives env roles src input name head) : Derives env roles other more name head := by
  induction derived with
  | initial mem => exact .initial (seeds _ mem)
  | equation c e hc he _ step ih => exact .equation c e (clauses c hc) he ih step

/-- Name-domain membership is read directly from original clauses. -/
theorem names_member (src : Source) (name : Nat) :
    name ∈ names src ↔ ∃ c ∈ src, c.receiver = name ∨ ∃ e ∈ c.equations, e.output = name := by
  simp only [names, List.mem_append, List.mem_map, lower, List.mem_flatMap]
  constructor
  · rintro (⟨c, hc, same⟩ | ⟨q, ⟨c, hc, mapped⟩, member⟩)
    · exact ⟨c, hc, Or.inl same⟩
    · obtain ⟨e, he, rfl⟩ := mapped
      simp only [CommonRoleAssociatedClauseExtraction.row, List.mem_cons, List.not_mem_nil, or_false] at member
      exact ⟨c, hc, member.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨e, he, h.symm⟩)⟩
  · rintro ⟨c, hc, h | ⟨e, he, h⟩⟩
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inr ⟨CommonRoleAssociatedClauseExtraction.row c e, ⟨c, hc, ⟨e, he, rfl⟩⟩, by simp [CommonRoleAssociatedClauseExtraction.row, h]⟩

/-- Reordering or duplicating source clauses and named assumptions preserves
readiness without requiring a caller to reindex ordinary states. -/
theorem run_source_congr (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src other : Source) (input more : Assumptions)
    (clauses : ∀ c, c ∈ src ↔ c ∈ other) (seeds : ∀ f, f ∈ input ↔ f ∈ more) :
    runSource env roles wf src input = runSource env roles wf other more := by
  have derive (name head) : Derives env roles src input name head ↔ Derives env roles other more name head :=
    ⟨derives_transport env roles src other input more (fun c => (clauses c).mp)
      (fun f => (seeds f).mp) name head,
     derives_transport env roles other src more input (fun c => (clauses c).mpr)
      (fun f => (seeds f).mpr) name head⟩
  have nameEq (name) : name ∈ names src ↔ name ∈ names other := by
    simp only [names_member, clauses]
  have models : Models env roles src input ↔ Models env roles other more := by
    simp only [Models, nameEq, derive]
  have exactness : runSource env roles wf src input = true ↔ runSource env roles wf other more = true := by
    rw [run_source_exact env roles wf awf, run_source_exact env roles wf awf, models]
    simp only [ValidSource, clauses, derive]
  cases a : runSource env roles wf src input <;>
    cases b : runSource env roles wf other more <;> simp_all

end Yulang.CommonRoleNamedSourceEntry
