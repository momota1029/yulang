import Yulang.GeneralSourceRoleCstCoverageEnd295

/-! A finite table can observe absence, but no row is not such an observation. -/
namespace Yulang.GeneralSourceRoleCstNameCatalog296
open GeneralSourceRoleCstNamingRequests295 (Query reply)
open GeneralSourceRoleSpelling292 (Environment)

abbrev Catalog := List (Query × Option Nat)

def fiber (catalog : Catalog) (q : Query) : List (Option Nat) :=
  ((catalog.filter fun p => decide (p.1 = q))).map Prod.snd

inductive Lookup where
  | unobserved
  | known (value : Option Nat)
  | ambiguous
  deriving DecidableEq, Repr

def lookup (catalog : Catalog) (q : Query) : Lookup :=
  match fiber catalog q with
  | [] => .unobserved
  | [v] => .known v
  | _::_::_ => .ambiguous

theorem known_exact (c : Catalog) (q : Query) (v : Option Nat) :
    lookup c q = .known v ↔ fiber c q = [v] := by
  cases h : fiber c q with
  | nil => simp [lookup,h]
  | cons x xs => cases xs <;> simp [lookup,h]

theorem empty_exact (c : Catalog) (q : Query) :
    lookup c q = .unobserved ↔ fiber c q = [] := by
  cases h : fiber c q with
  | nil => simp [lookup,h]
  | cons x xs => cases xs <;> simp [lookup,h]

theorem ambiguous_exact (c : Catalog) (q : Query) :
    lookup c q = .ambiguous ↔ 2 ≤ (fiber c q).length := by
  cases h : fiber c q with
  | nil => simp [lookup,h]
  | cons x xs =>
    cases xs with
    | nil => simp [lookup,h]
    | cons y ys => simp [lookup,h]

def provisional (c : Catalog) (q : Query) : Option Nat :=
  match lookup c q with
  | .known v => v
  | _ => none

def environment (c : Catalog) : Environment :=
  ⟨fun n => provisional c (.role n),fun r n => provisional c (.output r n),
    fun n => provisional c (.constructor n)⟩

theorem reply_from_catalog (c : Catalog) (q : Query) :
    reply (environment c) q = provisional c q := by cases q <;> rfl

theorem known_reply (c : Catalog) (q : Query) (v : Option Nat)
    (h : lookup c q = .known v) : reply (environment c) q = v := by
  simp [reply_from_catalog,provisional,h]

theorem member_of_fiber (c : Catalog) (q : Query) (v : Option Nat) :
    v ∈ fiber c q ↔ (q,v) ∈ c := by
  unfold fiber
  simp only [List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨key,val⟩,⟨mem,rfl⟩,rfl⟩; exact mem
  · intro mem; exact ⟨(q,v),⟨mem,rfl⟩,rfl⟩

end Yulang.GeneralSourceRoleCstNameCatalog296
