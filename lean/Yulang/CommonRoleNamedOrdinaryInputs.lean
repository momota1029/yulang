import Yulang.CommonRoleAmbientMixedSource

/-! Finite named ordinary inequalities determine both the extra-name domain and
initial state for structural associated closure. Scope resolution and the
structural program remain inputs. Derivation detects explicit scalar pairs and
reciprocal edges, not arbitrary ordinary entailment. Solver consistency is not
resolution success for every associated occurrence. This is not B4. -/
namespace Yulang.CommonRoleNamedOrdinaryInputs
open CommonRoleStructuralAssociatedTemplates (Program Occurrence Step)
open CommonRoleSettledConstraints (State)
open CommonRoleSourceIdentity (Slot)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleEvidenceSaturation (Linked)
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)

inductive Term (α : Type) where
  | base (b : Inference.Base)
  | var (a : α)
  deriving DecidableEq

abbrev Input := List (Term Nat × Term Nat)

def Term.map (f : α → β) : Term α → Term β
  | .base b => .base b
  | .var a => .var (f a)

def Term.lower : Term α → TyTerm α
  | .base b => .base b
  | .var a => .var a

def Term.eval (v : Nat → Common.Ty) : Term Nat → Common.Ty
  | .base b => .base b
  | .var a => v a

def Term.names : Term Nat → List Nat
  | .base _ => []
  | .var a => [a]

def extra (input : Input) : List Nat :=
  (input.flatMap fun q => q.1.names ++ q.2.names).eraseDups
abbrev table (p : Program) (input : Input) := CommonRoleAmbientMixedSource.table p (extra input)
abbrev name (p : Program) (input : Input) := CommonRoleAmbientMixedSource.name p (extra input)

def terms (n : Nat) : List (Term (Fin n)) :=
  [.base .int,.base .bool,.base .str,.base .unit] ++ (List.finRange n).map Term.var

private theorem terms_complete (t : Term (Fin n)) : t ∈ terms n := by
  cases t with
  | base b => cases b <;> simp [terms]
  | var i => simp [terms]

def atoms (p : Program) (input : Input) : List (Atom (Slot (table p input))) :=
  (terms (table p input).length).flatMap fun a =>
    (terms (table p input).length).flatMap fun b =>
      if (a.map (name p input),b.map (name p input)) ∈ input then
        [.tyLe a.lower b.lower] else []

private theorem mem_atoms (p : Program) (input : Input) (atom : Atom (Slot (table p input))) :
    atom ∈ atoms p input ↔ ∃ a b : Term (Slot (table p input)),
      (a.map (name p input),b.map (name p input)) ∈ input ∧ atom = .tyLe a.lower b.lower := by
  simp only [atoms,List.mem_flatMap]
  constructor
  · rintro ⟨a,_,b,_,h⟩
    split at h
    · exact ⟨a,b,‹_›,by simpa using h⟩
    · simp at h
  · rintro ⟨a,b,h,rfl⟩
    exact ⟨a,terms_complete a,b,terms_complete b,by simp [h]⟩

private theorem lower_injective {a b : Term α} (h : a.lower = b.lower) : a = b := by
  cases a <;> cases b <;> simp_all [Term.lower]

theorem mem_inequality (p : Program) (input : Input) (a b : Term (Slot (table p input))) :
    Atom.tyLe a.lower b.lower ∈ atoms p input ↔
      (a.map (name p input),b.map (name p input)) ∈ input := by
  rw [mem_atoms]
  constructor
  · rintro ⟨c,d,h,e⟩
    have parts := Atom.tyLe.inj e
    have ac := lower_injective parts.1
    have bd := lower_injective parts.2
    simpa only [ac,bd] using h
  · intro h; exact ⟨a,b,h,rfl⟩

def initial (p : Program) (input : Input) : State (table p input).length where
  atoms := atoms p input
  child := by
    intro atom member
    obtain ⟨a,b,_,rfl⟩ := (mem_atoms p input atom).mp member
    cases a <;> cases b <;> trivial
  width := by
    intro a b member tail ht
    obtain ⟨x,y,_,eq⟩ := (mem_atoms p input _).mp member
    cases x <;> cases y <;> cases eq <;> cases ht
  rows := by
    intro atom member
    obtain ⟨a,b,_,rfl⟩ := (mem_atoms p input atom).mp member
    cases a <;> cases b <;> trivial

theorem initial_evidence (p : Program) (input : Input) (i : Slot (table p input)) (b : Inference.Base) :
    Evidence (initial p input).atoms i b ↔
      (.var (name p input i),.base b) ∈ input ∧ (.base b,.var (name p input i)) ∈ input := by
  change (Atom.tyLe (Term.var i).lower (Term.base b).lower ∈ atoms p input ∧
    Atom.tyLe (Term.base b).lower (Term.var i).lower ∈ atoms p input) ↔ _
  rw [mem_inequality,mem_inequality]
  rfl

theorem initial_linked (p : Program) (input : Input) (i j : Slot (table p input)) :
    Linked (initial p input) i j ↔
      (.var (name p input i),.var (name p input j)) ∈ input ∧
      (.var (name p input j),.var (name p input i)) ∈ input := by
  change (Atom.tyLe (Term.var i).lower (Term.var j).lower ∈ atoms p input ∧
    Atom.tyLe (Term.var j).lower (Term.var i).lower ∈ atoms p input) ↔ _
  rw [mem_inequality,mem_inequality]
  rfl

private theorem name_present (p : Program) (input : Input) (a b : Term Nat)
    (member : (a,b) ∈ input) (x : Nat) (hx : x ∈ a.names ++ b.names) :
    ∃ i : Slot (table p input), name p input i = x := by
  have he : x ∈ extra input := by
    simp only [extra,List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨(a,b),member,hx⟩
  have ht : x ∈ table p input := List.mem_append_right _ he
  obtain ⟨i,bound,eq⟩ := List.getElem_of_mem ht
  exact ⟨⟨i,bound⟩,eq⟩

private theorem represent (p : Program) (input : Input) (a b : Term Nat)
    (member : (a,b) ∈ input) :
    ∃ x y : Term (Slot (table p input)), x.map (name p input) = a ∧ y.map (name p input) = b := by
  have one (t : Term Nat) (ht : ∀ z ∈ t.names, z ∈ a.names ++ b.names) :
      ∃ x : Term (Slot (table p input)), x.map (name p input) = t := by
    cases t with
    | base c => exact ⟨.base c,rfl⟩
    | var z =>
      obtain ⟨i,eq⟩ := name_present p input a b member z (ht z (by simp [Term.names]))
      exact ⟨.var i,by simp [Term.map,eq]⟩
  obtain ⟨x,hx⟩ := one a (fun z hz => List.mem_append_left _ hz)
  obtain ⟨y,hy⟩ := one b (fun z hz => List.mem_append_right _ hz)
  exact ⟨x,y,hx,hy⟩

inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (p : Program)
    (input : Input) : Nat → Inference.Base → Prop
  | initial {a b} : (.var a,.base b) ∈ input → (.base b,.var a) ∈ input →
      Derives env roles p input a b
  | transfer {a c b} : (.var a,.var c) ∈ input → (.var c,.var a) ∈ input →
      Derives env roles p input c b → Derives env roles p input a b
  | associated (q : Occurrence) {head result} : q ∈ p →
      Derives env roles p input q.receiver head → Step env roles q head result →
      Derives env roles p input q.output result

theorem allocated_to_named (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (input : Input) (a : Nat) (b : Inference.Base)
    (h : CommonRoleAmbientMixedSource.Derives env roles p (extra input) (initial p input) a b) :
    Derives env roles p input a b := by
  induction h with
  | initial h => have pair := (initial_evidence ..).mp h; exact .initial pair.1 pair.2
  | transfer h _ ih => have pair := (initial_linked ..).mp h; exact .transfer pair.1 pair.2 ih
  | associated q member _ step ih => exact .associated q member ih step

theorem named_to_allocated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (input : Input) (a : Nat) (b : Inference.Base)
    (h : Derives env roles p input a b) :
    CommonRoleAmbientMixedSource.Derives env roles p (extra input) (initial p input) a b := by
  induction h with
  | @initial a b upper lower =>
    obtain ⟨i,eq⟩ := name_present p input _ _ upper a (by simp [Term.names])
    have pair := (initial_evidence p input i b).mpr (by simpa [eq] using And.intro upper lower)
    simpa only [eq] using CommonRoleAmbientMixedSource.Derives.initial pair
  | @transfer a c b ac ca _ ih =>
    obtain ⟨i,hi⟩ := name_present p input _ _ ac a (by simp [Term.names])
    obtain ⟨j,hj⟩ := name_present p input _ _ ac c (by simp [Term.names])
    have linked := (initial_linked p input i j).mpr (by simpa [hi,hj] using And.intro ac ca)
    have result := CommonRoleAmbientMixedSource.Derives.transfer linked (by simpa only [hj] using ih)
    simpa only [hi] using result
  | associated q member _ step ih => exact .associated q member ih step

theorem derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (input : Input) (a : Nat) (b : Inference.Base) :
    CommonRoleAmbientMixedSource.Derives env roles p (extra input) (initial p input) a b ↔
      Derives env roles p input a b :=
  ⟨allocated_to_named env roles p input a b,named_to_allocated env roles p input a b⟩

def OrdinaryModels (input : Input) (values : Nat → Common.Ty) : Prop :=
  ∀ q ∈ input, Common.Subtype (q.1.eval values) (q.2.eval values)

private theorem term_equivalent (p : Program) (input : Input)
    (v : Slot (table p input) → Comp Common.model) (values : Nat → Common.Ty)
    (factor : CommonRoleSourceDescent.Factors (table p input) v values)
    (t : Term (Slot (table p input))) :
    Common.Equivalent (t.lower.eval Common.model v) ((t.map (name p input)).eval values) := by
  cases t with
  | base b => exact Common.equivalent_refl _
  | var i => exact factor i

private theorem subtype_equivalent {a b c d : Common.Ty}
    (ac : Common.Equivalent a c) (bd : Common.Equivalent b d) :
    Common.Subtype a b ↔ Common.Subtype c d :=
  ⟨fun h => Common.subtype_trans ac.2 (Common.subtype_trans h bd.1),
    fun h => Common.subtype_trans ac.1 (Common.subtype_trans h bd.2)⟩

theorem initial_models (p : Program) (input : Input)
    (v : Slot (table p input) → Comp Common.model) (values : Nat → Common.Ty)
    (factor : CommonRoleSourceDescent.Factors (table p input) v values) :
    All Common.model v (initial p input).atoms ↔ OrdinaryModels input values := by
  constructor
  · intro models q member
    obtain ⟨x,y,hx,hy⟩ := represent p input q.1 q.2 member
    have h := models (.tyLe x.lower y.lower) ((mem_inequality p input x y).mpr (by simpa [hx,hy] using member))
    have out := (subtype_equivalent (term_equivalent p input v values factor x)
      (term_equivalent p input v values factor y)).mp h
    simpa only [hx,hy] using out
  · intro models atom member
    obtain ⟨x,y,h,rfl⟩ := (mem_atoms p input atom).mp member
    exact (subtype_equivalent (term_equivalent p input v values factor x)
      (term_equivalent p input v values factor y)).mpr (models _ h)

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (p : Program) (input : Input) :=
  CommonRoleAmbientMixedSource.run env roles wf p (extra input) (initial p input)

theorem run_evidence_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (input : Input) (i : Slot (table p input)) (b : Inference.Base) :
    Evidence (run env roles wf p input).atoms i b ↔ Derives env roles p input (name p input i) b := by
  rw [run,CommonRoleAmbientMixedSource.run_evidence_exact env roles wf awf,derives_exact]

theorem run_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (input : Input) (v : Slot (table p input) → Comp Common.model) :
    All Common.model v (run env roles wf p input).atoms ↔
      ∃ values, CommonRoleSourceDescent.Factors (table p input) v values ∧
        OrdinaryModels input values ∧
        ∀ a b, Derives env roles p input a b → Common.Equivalent (values a) (.base b) := by
  rw [run,CommonRoleAmbientMixedSource.run_source_exact env roles wf awf]
  simp only [derives_exact]
  constructor
  · rintro ⟨old,values,factor,facts⟩
    exact ⟨values,factor,(initial_models p input v values factor).mp old,facts⟩
  · rintro ⟨values,factor,old,facts⟩
    exact ⟨(initial_models p input v values factor).mpr old,values,factor,facts⟩

def Models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (p : Program) (input : Input) : Prop :=
  ∃ values : Nat → Common.Ty, OrdinaryModels input values ∧
    ∀ a b, Derives env roles p input a b → Common.Equivalent (values a) (.base b)

/-- Exact ordinary consistency no longer requires caller allocation or a State.
The input is named constraints, not arbitrary source expressions. -/
theorem solver_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (input : Input) :
    CommonRoleOpenPropagation.consistent (run env roles wf p input) = true ↔ Models env roles p input := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  constructor
  · rintro ⟨v,h⟩
    obtain ⟨values,_,old,facts⟩ := (run_source_exact env roles wf awf p input v).mp h
    exact ⟨values,old,facts⟩
  · rintro ⟨values,old,facts⟩
    let v : Slot (table p input) → Comp Common.model := fun i => Comp.pure Common.model (values (name p input i))
    exact ⟨v,(run_source_exact env roles wf awf p input v).mpr
      ⟨values,(fun _ => Common.equivalent_refl _),old,facts⟩⟩

/-- Reordering or duplicating original named constraints preserves the independent
judgment, even though the concrete allocation and atom list can change. -/
theorem derives_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (p : Program)
    (left right : Input) (same : ∀ q, q ∈ left ↔ q ∈ right) (a : Nat) (b : Inference.Base) :
    Derives env roles p left a b ↔ Derives env roles p right a b := by
  have direction (x y : Input) (included : ∀ q ∈ x, q ∈ y) (a : Nat) (b : Inference.Base)
      (h : Derives env roles p x a b) : Derives env roles p y a b := by
    induction h with
    | initial up lo => exact .initial (included _ up) (included _ lo)
    | transfer up lo _ ih => exact .transfer (included _ up) (included _ lo) ih
    | associated q member _ step ih => exact .associated q member ih step
  exact ⟨direction left right (fun q h => (same q).mp h) a b,
    direction right left (fun q h => (same q).mpr h) a b⟩

theorem models_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (p : Program)
    (left right : Input) (same : ∀ q, q ∈ left ↔ q ∈ right) :
    Models env roles p left ↔ Models env roles p right := by
  simp only [Models,OrdinaryModels,same,derives_congr env roles p left right same]

/-- Allocation changes caused by ordering or duplicate constraints cannot change
ordinary acceptance after the actual mixed closure. -/
theorem solver_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (p : Program)
    (left right : Input) (same : ∀ q, q ∈ left ↔ q ∈ right) :
    CommonRoleOpenPropagation.consistent (run env roles wf p left) = true ↔
      CommonRoleOpenPropagation.consistent (run env roles wf p right) = true := by
  rw [solver_source_exact env roles wf awf,solver_source_exact env roles wf awf,
    models_congr env roles p left right same]

end Yulang.CommonRoleNamedOrdinaryInputs
