import Yulang.GeneralRebaseOverlap281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTermCopy281
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalState (typeSources)
open CommonNominalFullCarrier (model Equivalent subtype_refl)
open GeneralRebasePortProjection280 (Supported Project)

abbrev Write := Nat × TyTerm Nat

def Unique (writes : List Write) : Prop :=
  ∀ x ∈ writes, ∀ y ∈ writes, x.1 = y.1 → x.2 = y.2

def Reads (pool : List Nat) (writes : List Write) : Prop :=
  ∀ x ∈ writes, typeSources x.2 ⊆ pool

def Respects (writes : List Write) (m : Assignment) : Prop :=
  ∀ x ∈ writes, Equivalent (m x.1).1 (x.2.eval model m)

def lookup (writes : List Write) (slot : Nat) : Option (TyTerm Nat) :=
  match writes with
  | [] => none
  | row :: tail => if row.1 = slot then some row.2 else lookup tail slot

theorem lookup_present (found : lookup writes slot = some term) : (slot,term) ∈ writes := by
  induction writes with
  | nil => cases found
  | cons first rest ih =>
    by_cases same : first.1 = slot
    · have body : first.2 = term := by simpa only [lookup,ite_eq_left same,Option.some.injEq] using found
      exact List.mem_cons.mpr (Or.inl (Prod.ext same.symm body.symm))
    · exact List.mem_cons_of_mem _ (ih (by simpa only [lookup,ite_eq_right same] using found))

theorem lookup_exact (unique : Unique writes) (member : row ∈ writes) :
    lookup writes row.1 = some row.2 := by
  induction writes with
  | nil => cases member
  | cons first rest ih =>
    by_cases h : first.1 = row.1
    · simp only [lookup,ite_eq_left h,unique _ List.mem_cons_self _ member h]
    · refine (ite_eq_right h).trans (ih ?_ ((List.mem_cons.mp member).resolve_left ?_))
      · exact fun x hx y hy eq => unique x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) eq
      · exact fun eq => h (congrArg Prod.fst eq.symm)

def kept (pool : List Nat) (writes : List Write) : List Write :=
  writes.filter (fun w => decide (w.1 ∈ pool))

def fresh (pool : List Nat) (writes : List Write) : List Write :=
  writes.filter (fun w => decide (w.1 ∉ pool))

def Copy (writes : List Write) (m : Assignment) : Assignment :=
  fun id => match lookup writes id with
    | none => m id
    | some body => (body.eval model m,(m id).2)

theorem fresh_agrees (pool : List Nat) (writes : List Write) (m : Assignment) :
    Agree pool m (Copy (fresh pool writes) m) := by
  intro id inside
  unfold Copy
  cases h : lookup (fresh pool writes) id with
  | none => rfl
  | some body =>
    have found := lookup_present h
    have outside : id ∉ pool := by
      exact of_decide_eq_true (List.mem_filter.mp found).2
    exact False.elim (outside inside)

theorem kept_supported (reads : Reads pool writes) : Supported pool (Respects (kept pool writes)) := by
  intro m n agrees
  constructor <;> intro given row inside
  · obtain ⟨listed,test⟩ := List.mem_filter.mp inside
    have fixed := agrees row.1 (of_decide_eq_true test)
    have body := GeneralNominalCenteredModelExtension.type_eval_same row.2 (fun id occurs => agrees id (reads row listed occurs))
    rw [← fixed,← body]
    exact given row inside
  · obtain ⟨listed,test⟩ := List.mem_filter.mp inside
    have fixed := agrees row.1 (of_decide_eq_true test)
    have body := GeneralNominalCenteredModelExtension.type_eval_same row.2 (fun id occurs => agrees id (reads row listed occurs))
    rw [fixed,body]
    exact given row inside

theorem fresh_obligations (unique : Unique writes) (reads : Reads pool writes) (m : Assignment) :
    Respects (fresh pool writes) (Copy (fresh pool writes) m) := by
  intro row listed
  have original := (List.mem_filter.mp listed).1
  have one : lookup (fresh pool writes) row.1 = some row.2 := lookup_exact (fun x hx y hy eq => unique x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 eq) listed
  have body := GeneralNominalCenteredModelExtension.type_eval_same row.2
    (fun id used => fresh_agrees pool writes m id (reads row original used))
  rw [← body]
  change Equivalent (Copy (fresh pool writes) m row.1).1 _
  unfold Copy
  rw [one]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem project_exact (supported : Supported pool base) (unique : Unique writes)
    (reads : Reads pool writes) (m : Assignment) :
    Project pool (fun a => base a ∧ Respects writes a) m ↔ base m ∧ Respects (kept pool writes) m := by
  constructor
  · rintro ⟨a,agree,h,done⟩
    exact ⟨(supported _ _ agree).mp h,(kept_supported reads _ _ agree).mp (fun row found => done row (List.mem_filter.mp found).1)⟩
  · rintro ⟨prior,keptValid⟩
    have same := fresh_agrees pool writes m
    refine ⟨_,fun _ found => (same _ found).symm,(supported _ _ same).mp prior,?_⟩
    intro row listed
    by_cases within : row.1 ∈ pool
    · exact (kept_supported reads _ _ same).mp keptValid row (List.mem_filter.mpr ⟨listed,decide_eq_true within⟩)
    · exact fresh_obligations unique reads m row (List.mem_filter.mpr ⟨listed,decide_eq_true within⟩)

end Yulang.GeneralRebaseTermCopy281
