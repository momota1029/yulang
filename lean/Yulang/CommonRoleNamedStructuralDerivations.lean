import Yulang.CommonRoleStructuralRenaming

/-! An independent structural/associated judgment on original source names.
The static finite single-placeholder/scalar fragment is unchanged. Allocation,
finite indices and resolver outputs do not occur in the source judgment.
This is not the full source typing or dynamic where-generation judgment. -/
namespace Yulang.CommonRoleNamedStructuralDerivations
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleStructuralNamedInputs (Source names slot readName capacity atoms occurrences)
open CommonRoleStructuralAssociatedTemplates (Step)
open CommonRoleStructuralRenaming

abbrev equalities (name : Nat) (head : Inference.Base) : List (Atom Nat) :=
  [.tyLe (.var name) (.base head), .tyLe (.base head) (.var name)]

inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) : Atom Nat → Prop
  | seed (a) : a ∈ src.atoms → Derives env roles src a
  | split (a b) : Derives env roles src a → b ∈ CommonRoleStructuralDecomposition.atom a →
      Derives env roles src b
  | trans (l m r) : Derives env roles src (.tyLe l m) → Derives env roles src (.tyLe m r) →
      Derives env roles src (.tyLe l r)
  | associated (q head result a) : q ∈ src.program →
      (∀ b ∈ equalities q.receiver head, Derives env roles src b) →
      Step env roles q head result → a ∈ equalities q.output result → Derives env roles src a

def Known (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (name : Nat) (head : Inference.Base) :=
  ∀ a ∈ equalities name head, Derives env roles src a

theorem equalities_rename (f : Nat → Fin n) (name : Nat) (head : Inference.Base) :
    (equalities name head).map (Atom.rename f) = CommonRoleCandidateStateFrontier.equality (f name) head := rfl

theorem equalities_read (f : Fin n → Nat) (name : Fin n) (head : Inference.Base) :
    (CommonRoleCandidateStateFrontier.equality name head).map (Atom.rename f) = equalities (f name) head := rfl

/-- Every derivation in the original names compiles to an actual finite derivation. -/
theorem compile (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) (a : Atom Nat)
    (derived : Derives env roles src a) :
    CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src)
      (a.rename (slot src)) := by
  induction derived with
  | seed a member => exact .seed _ (List.mem_map.mpr ⟨a,member,rfl⟩)
  | split a b _ member ih =>
    apply CommonRoleStructuralAssociatedClosure.Derives.split _ _ ih
    rw [atom_rename]
    exact List.mem_map.mpr ⟨b,member,rfl⟩
  | trans l m r _ _ ihl ihr =>
    apply CommonRoleStructuralAssociatedClosure.Derives.trans _ _ _ ihl ihr
    simp [Atom.rename,CommonRoleFiniteStructuralClosure.compose]
  | associated q head result a member _ step eqs ih =>
    apply CommonRoleStructuralAssociatedClosure.Derives.associated
      (CommonRoleStructuralNamedInputs.occurrence src q) head result _
      (List.mem_map.mpr ⟨q,member,rfl⟩)
    · intro premise present
      change premise ∈ CommonRoleCandidateStateFrontier.equality (slot src q.receiver) head at present
      rw [← equalities_rename] at present
      obtain ⟨b,member,rfl⟩ := List.mem_map.mp present
      exact ih b member
    · exact (CommonRoleStructuralNamedInputs.occurrence_step env roles src q head result).mpr step
    · change a.rename (slot src) ∈ CommonRoleCandidateStateFrontier.equality (slot src q.output) result
      rw [← equalities_rename]
      exact List.mem_map.mpr ⟨a,eqs,rfl⟩

theorem read_atom (src : Source) (a : Atom Nat)
    (present : ∀ name ∈ CommonRoleStructuralNamedInputs.atomNames a, name ∈ names src) :
    (a.rename (slot src)).rename (readName src) = a := by
  rw [atom_rename_comp]
  calc
    a.rename (readName src ∘ slot src) = a.rename id :=
      atom_rename_congr _ _ a (fun x hx => CommonRoleStructuralNamedInputs.read_slot src x (present x hx))
    _ = a := atom_rename_id a

/-- Readback of any finite derivation is a genuine original-name derivation.
Only source endpoints and seed names need roundtrip; no global injectivity of
the total allocator is assumed. -/
theorem readback (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (a : Atom (Fin (capacity src)))
    (derived : CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src) a) :
    Derives env roles src (a.rename (readName src)) := by
  induction derived with
  | seed a member =>
    obtain ⟨original,sourceMem,rfl⟩ := List.mem_map.mp member
    rw [read_atom src original (CommonRoleStructuralNamedInputs.atom_names_present src original sourceMem)]
    exact .seed original sourceMem
  | split a b _ member ih =>
    apply Derives.split _ _ ih
    rw [atom_rename]
    exact List.mem_map.mpr ⟨b,member,rfl⟩
  | trans a b c _ _ member iha ihb =>
    cases a with
    | rowLe l r => simp [CommonRoleFiniteStructuralClosure.compose] at member
    | tyLe l m =>
      cases b with
      | rowLe l r => simp [CommonRoleFiniteStructuralClosure.compose] at member
      | tyLe m' r =>
        simp only [CommonRoleFiniteStructuralClosure.compose] at member
        split at member
        · rename_i same
          subst m'
          have same : c = .tyLe l r := by simpa using member
          subst c
          exact .trans _ _ _ iha ihb
        · contradiction
  | associated q head result a member _ step eqs ih =>
    obtain ⟨original,sourceMem,rfl⟩ := List.mem_map.mp member
    obtain ⟨receiver,output⟩ := CommonRoleStructuralNamedInputs.occurrence_names_present src original sourceMem
    apply Derives.associated original head result _ sourceMem
    · intro b present
      have preimage : b ∈ (CommonRoleCandidateStateFrontier.equality
          (slot src original.receiver) head).map (Atom.rename (readName src)) := by
        rw [equalities_read,CommonRoleStructuralNamedInputs.read_slot src original.receiver receiver]
        exact present
      obtain ⟨finite,finiteMember,rfl⟩ := List.mem_map.mp preimage
      exact ih finite finiteMember
    · exact (CommonRoleStructuralNamedInputs.occurrence_step env roles src original head result).mp step
    · have mapped := (List.mem_map (f := Atom.rename (readName src))).mpr ⟨a,eqs,rfl⟩
      change a.rename (readName src) ∈ (CommonRoleCandidateStateFrontier.equality
        (slot src original.output) result).map (Atom.rename (readName src)) at mapped
      rw [equalities_read,CommonRoleStructuralNamedInputs.read_slot src original.output output] at mapped
      exact mapped

/-- Reflection requires that the queried atom uses input names. Arbitrary
absent names cannot be justified by the allocator's shared dummy slot. -/
theorem derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) (a : Atom Nat)
    (present : ∀ name ∈ CommonRoleStructuralNamedInputs.atomNames a, name ∈ names src) :
    CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src)
      (a.rename (slot src)) ↔ Derives env roles src a := by
  constructor
  · intro h
    have h := readback env roles src _ h
    rwa [read_atom src a present] at h
  · exact compile env roles src a

theorem known_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (name : Nat) (present : name ∈ names src) (head : Inference.Base) :
    CommonRoleStructuralNamedInputs.Known env roles src name head ↔ Known env roles src name head := by
  constructor
  · intro h a member
    have result := readback env roles src _ (h (a.rename (slot src))
      (by rw [← equalities_rename]; exact List.mem_map.mpr ⟨a,member,rfl⟩))
    have scope : ∀ x ∈ CommonRoleStructuralNamedInputs.atomNames a, x ∈ names src := by
      rcases List.mem_cons.mp member with rfl | member
      · simpa [CommonRoleStructuralNamedInputs.atomNames,CommonRoleStructuralNamedInputs.tyNames] using present
      · have same : a = .tyLe (.base head) (.var name) := by simpa using member
        subst a
        simpa [CommonRoleStructuralNamedInputs.atomNames,CommonRoleStructuralNamedInputs.tyNames] using present
    rwa [read_atom src a scope] at result
  · intro h a member
    change a ∈ CommonRoleCandidateStateFrontier.equality (slot src name) head at member
    rw [← equalities_rename] at member
    obtain ⟨b,sourceMem,rfl⟩ := List.mem_map.mp member
    exact compile env roles src b (h b sourceMem)

def Models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) (v : Nat → Comp Common.model) :=
  All Common.model v src.atoms ∧ ∀ q ∈ src.program, ∀ head result,
    Known env roles src q.receiver head → Step env roles q head result →
      Common.Equivalent (v q.output).1 (.base result)

/-- The previous allocated model contract now has an independent named form. -/
theorem models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (v : Fin (capacity src) → Comp Common.model) :
    CommonRoleStructuralNamedInputs.SourceModels env roles src v ↔ Models env roles src (v ∘ slot src) := by
  apply and_congr_right
  intro _
  apply forall_congr'
  intro q
  apply forall_congr'
  intro member
  obtain ⟨present,_⟩ := CommonRoleStructuralNamedInputs.occurrence_names_present src q member
  exact forall_congr' fun head => forall_congr' fun result =>
    imp_congr_left (known_exact env roles src q.receiver present head)

/-- Actual solver success iff the raw ordinary grammar holds and some original
named valuation satisfies the independently activated associated equations. -/
theorem run_named_exists_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (CommonRoleStructuralNamedInputs.run env roles wf src).isSome = true ↔
      CommonRoleStructuralNamedInputs.Good src ∧ ∃ v : Nat → Comp Common.model, Models env roles src v := by
  rw [CommonRoleStructuralNamedInputs.run_source_exists_iff env roles wf awf]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v ∘ slot src,(models_exact env roles src v).mp hv⟩
  · rintro ⟨v,ordinary,associated⟩
    refine ⟨v ∘ readName src,?_⟩
    constructor
    · exact (CommonRoleStructuralNamedInputs.source_models src _).mp
        ((CommonRoleStructuralNamedInputs.allocated_models src v).mpr ordinary)
    · intro q member head result known step
      obtain ⟨receiver,output⟩ := CommonRoleStructuralNamedInputs.occurrence_names_present src q member
      have model := associated q member head result ((known_exact env roles src q.receiver receiver head).mp known) step
      simpa only [Function.comp_apply,CommonRoleStructuralNamedInputs.read_slot src q.output output] using model

theorem equalities_models (name : Nat) (head : Inference.Base) (v : Nat → Comp Common.model) :
    All Common.model v (equalities name head) ↔ Common.Equivalent (v name).1 (.base head) := by
  simp [All,equalities,Atom.Holds,TyTerm.eval,Common.model,Common.Equivalent]

/-- Models are exactly models of all independently derivable named atoms.
Completeness is for the stated rules, not arbitrary semantic entailment. -/
theorem all_derivations_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (v : Nat → Comp Common.model) :
    Models env roles src v ↔ ∀ a, Derives env roles src a → a.Holds Common.model v := by
  constructor
  · intro model a derived
    induction derived with
    | seed a member => exact model.1 a member
    | split a b _ member ih =>
      exact (CommonRoleStructuralDecomposition.atom_exact a v).mpr ih b member
    | trans l m r _ _ ihl ihr => exact Common.subtype_trans ihl ihr
    | associated q head result a member premises step eqs _ =>
      exact (equalities_models q.output result v).mpr (model.2 q member head result premises step) a eqs
  · intro model
    refine ⟨fun a member => model a (.seed a member),?_⟩
    intro q member head result known step
    apply (equalities_models q.output result v).mp
    intro a eqs
    exact model a (.associated q head result a member known step eqs)

theorem models_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (v w : Nat → Comp Common.model) (same : ∀ name ∈ names src, v name = w name) :
    Models env roles src v ↔ Models env roles src w := by
  have ordinary : All Common.model v src.atoms ↔ All Common.model w src.atoms := by
    apply forall_congr'
    intro a
    apply forall_congr'
    intro member
    exact CommonRoleStructuralNamedInputs.atom_holds_congr a v w
      (fun name present => same name (CommonRoleStructuralNamedInputs.atom_names_present src a member name present))
  apply and_congr ordinary
  apply forall_congr'
  intro q
  apply forall_congr'
  intro member
  rw [same q.output (CommonRoleStructuralNamedInputs.occurrence_names_present src q member).2]

/-- Every finite model of an actual returned ordinary state corresponds to the
independent source-name judgment. No successful role selection is inferred. -/
theorem run_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source)
    (output : CommonRoleSettledConstraints.State (capacity src))
    (returned : CommonRoleStructuralNamedInputs.run env roles wf src = some output)
    (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v output.atoms ↔ Models env roles src (v ∘ slot src) :=
  (CommonRoleStructuralNamedInputs.run_source_models env roles wf awf src output returned v).trans
    (models_exact env roles src v)

/-- Original-name valuations can be checked directly against returned atoms,
including arbitrary unused names and row components. -/
theorem run_named_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source)
    (output : CommonRoleSettledConstraints.State (capacity src))
    (returned : CommonRoleStructuralNamedInputs.run env roles wf src = some output)
    (v : Nat → Comp Common.model) :
    All Common.model (v ∘ readName src) output.atoms ↔ Models env roles src v := by
  rw [run_models env roles wf awf src output returned]
  exact models_congr env roles src _ v (fun name member => by
    simp only [Function.comp_apply,CommonRoleStructuralNamedInputs.read_slot src name member])

end Yulang.CommonRoleNamedStructuralDerivations
