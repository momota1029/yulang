import Yulang.CommonRolePathDecomposition

/-! Finite indexed structural closure. The carrier is explicit: missing atoms are
not invented. Saturation terminates by fresh carrier indices, not a user pass
limit. Exactness below is for these finite rules, not unrestricted subtyping. -/
namespace Yulang.CommonRoleFiniteStructuralClosure
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
deriving instance DecidableEq for Atom
abbrev Index (u : List (Atom (Fin n))) := Fin u.length

def compose : Atom (Fin n) → Atom (Fin n) → List (Atom (Fin n))
  | .tyLe l m, .tyLe m' r => if m = m' then [.tyLe l r] else []
  | _, _ => []
theorem compose_sound (x y : Atom (Fin n)) (a : Fin n → Comp Common.model)
    (hx : x.Holds Common.model a) (hy : y.Holds Common.model a) :
    All Common.model a (compose x y) := by
  cases x <;> cases y <;> simp only [compose]
  case tyLe.tyLe l m m' r =>
    split
    · rename_i h; subst m'
      intro z hz
      have hz' : z = .tyLe l r := by simpa using hz
      subst z
      exact Common.subtype_trans hx hy
    · exact PresenceNormalForm.all_nil Common.model a
  all_goals exact PresenceNormalForm.all_nil Common.model a
def seedRules (seeds u : List (Atom (Fin n))) : List (FiniteHorn.Rule (Index u)) :=
  ((List.finRange u.length).filter fun i => decide (u[i] ∈ seeds)).map fun i => ⟨[],i⟩
def splitRules (u : List (Atom (Fin n))) : List (FiniteHorn.Rule (Index u)) :=
  (List.finRange u.length).flatMap fun i =>
    ((List.finRange u.length).filter fun j =>
      decide (u[j] ∈ CommonRoleStructuralDecomposition.atom u[i])).map fun j => ⟨[i],j⟩
def transRules (u : List (Atom (Fin n))) : List (FiniteHorn.Rule (Index u)) :=
  (List.finRange u.length).flatMap fun i => (List.finRange u.length).flatMap fun j =>
    ((List.finRange u.length).filter fun k => decide (u[k] ∈ compose u[i] u[j])).map fun k => ⟨[i,j],k⟩
def rules (seeds u : List (Atom (Fin n))) := seedRules seeds u ++ splitRules u ++ transRules u
def seen (seeds u : List (Atom (Fin n))) : List (Index u) :=
  FiniteHorn.saturate (rules seeds u) (List.finRange u.length)
def close (seeds extra : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  let u := seeds ++ extra
  seeds ++ (seen seeds u).map fun i => u[i]
theorem rules_sound (seeds u : List (Atom (Fin n))) (a : Fin n → Comp Common.model)
    (hm : All Common.model a seeds) :
    ∀ r ∈ rules seeds u, FiniteHorn.Valid (fun i => u[i].Holds Common.model a) r := by
  intro r hr hp
  rcases List.mem_append.mp hr with hs | ht
  · rcases List.mem_append.mp hs with hs | hd
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      exact hm _ (of_decide_eq_true (List.mem_filter.mp hi).2)
    · obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hd
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
      exact (CommonRoleStructuralDecomposition.atom_exact u[i] a).mpr
        (hp i (by simp)) _ (of_decide_eq_true (List.mem_filter.mp hj).2)
  · obtain ⟨i,_,h⟩ := List.mem_flatMap.mp ht
    obtain ⟨j,_,h⟩ := List.mem_flatMap.mp h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    exact compose_sound u[i] u[j] a (hp i (by simp)) (hp j (by simp)) _
      (of_decide_eq_true (List.mem_filter.mp hk).2)
theorem model_exact (seeds extra : List (Atom (Fin n))) (a : Fin n → Comp Common.model) :
    All Common.model a (close seeds extra) ↔ All Common.model a seeds := by
  rw [close, PresenceNormalForm.all_append]
  constructor
  · exact And.left
  · intro hm
    refine ⟨hm,?_⟩
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact FiniteHorn.saturate_preserves _ _ _ (rules_sound seeds (seeds ++ extra) a hm) i hi
theorem derivation_exact (seeds u : List (Atom (Fin n))) (i : Index u) :
    i ∈ seen seeds u ↔ FiniteHorn.Derives (rules seeds u) i :=
  FiniteHorn.saturate_exact _ _ (fun _ => List.mem_finRange _) i
theorem stopped (seeds u : List (Atom (Fin n))) :
    FiniteHorn.firstFresh (rules seeds u) (seen seeds u) (List.finRange u.length) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro i _ h
  exact FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _) i h
theorem capacity (seeds u : List (Atom (Fin n))) : (seen seeds u).length ≤ u.length := by
  simpa [seen] using FiniteHorn.saturate_length_le (rules seeds u) (List.finRange u.length)
    (fun _ => List.mem_finRange _)
/-- Only supported structural children are expanded; other constructors remain opaque. -/
def terms : TyTerm (Fin n) → List (TyTerm (Fin n))
  | t@(.pair a b) => t :: (terms a ++ terms b)
  | t@(.arrow a _ b _) => t :: (terms a ++ terms b)
  | t@(.variant _ a) => t :: terms a
  | t => [t]

def rows : TyTerm (Fin n) → List (Core.PresenceGeneration.RowTerm (Fin n))
  | .pair a b => rows a ++ rows b
  | .arrow a ea b eb => ea :: eb :: (rows a ++ rows b)
  | .variant _ a => rows a
  | _ => []

def carrier (seeds : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  let ts := (seeds.flatMap fun x => match x with
    | .tyLe l r => terms l ++ terms r
    | .rowLe _ _ => []).eraseDups
  let rs := (seeds.flatMap fun x => match x with
    | .tyLe l r => rows l ++ rows r
    | .rowLe l r => [l,r]).eraseDups
  (ts.flatMap fun l => ts.map fun r => .tyLe l r) ++
    (rs.flatMap fun l => rs.map fun r => .rowLe l r)

/-- Fully executable input-syntax carrier. Completeness outside the finite rules
is not claimed; unsupported constructors are opaque residuals. -/
def normalize (seeds : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  close seeds (carrier seeds)

theorem normalize_exact (seeds : List (Atom (Fin n))) (a : Fin n → Comp Common.model) :
    All Common.model a (normalize seeds) ↔ All Common.model a seeds :=
  model_exact seeds (carrier seeds) a

theorem seed_seen (seeds u : List (Atom (Fin n))) (i : Index u)
    (h : u[i] ∈ seeds) : i ∈ seen seeds u := by
  apply FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _)
  refine ⟨⟨[],i⟩,?_,rfl,by simp⟩
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa⟩,rfl⟩

theorem split_seen (seeds u : List (Atom (Fin n))) (i j : Index u)
    (hi : i ∈ seen seeds u) (hj : u[j] ∈ CommonRoleStructuralDecomposition.atom u[i]) :
    j ∈ seen seeds u := by
  apply FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _)
  refine ⟨⟨[i],j⟩,?_,rfl,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _, List.mem_map.mpr
      ⟨j,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa⟩,rfl⟩⟩
  · simpa [seen] using hi

theorem trans_seen (seeds u : List (Atom (Fin n))) (i j k : Index u)
    (hi : i ∈ seen seeds u) (hj : j ∈ seen seeds u)
    (hk : u[k] ∈ compose u[i] u[j]) : k ∈ seen seeds u := by
  apply FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _)
  refine ⟨⟨[i,j],k⟩,?_,rfl,?_⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _, List.mem_flatMap.mpr
      ⟨j,List.mem_finRange _, List.mem_map.mpr
        ⟨k,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa⟩,rfl⟩⟩⟩
  · simpa [seen] using And.intro hi hj

/-- Declarative finite-carrier closure, independent of rule enumeration and worklist. -/
inductive Derived (seeds u : List (Atom (Fin n))) : Index u → Prop where
  | seed (i : Index u) : u[i] ∈ seeds → Derived seeds u i
  | split (i j : Index u) : Derived seeds u i →
      u[j] ∈ CommonRoleStructuralDecomposition.atom u[i] → Derived seeds u j
  | trans (i j k : Index u) : Derived seeds u i → Derived seeds u j →
      u[k] ∈ compose u[i] u[j] → Derived seeds u k

theorem exact (seeds u : List (Atom (Fin n))) (i : Index u) :
    i ∈ seen seeds u ↔ Derived seeds u i := by
  constructor
  · intro hi
    apply FiniteHorn.saturate_preserves _ _ (Derived seeds u) _ i hi
    intro rule hr hp
    rcases List.mem_append.mp hr with hs | ht
    · rcases List.mem_append.mp hs with hs | hd
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
        exact .seed j (of_decide_eq_true (List.mem_filter.mp hj).2)
      · obtain ⟨j,_,h⟩ := List.mem_flatMap.mp hd
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
        exact .split j k (hp j (by simp))
          (of_decide_eq_true (List.mem_filter.mp hk).2)
    · obtain ⟨j,_,h⟩ := List.mem_flatMap.mp ht
      obtain ⟨k,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp h
      exact .trans j k l (hp j (by simp)) (hp k (by simp))
        (of_decide_eq_true (List.mem_filter.mp hl).2)
  · intro h
    induction h with
    | seed j hj => exact seed_seen seeds u j hj
    | split j k _ hk ih => exact split_seen seeds u j k ih hk
    | trans j k l _ _ hl ihj ihk => exact trans_seen seeds u j k l ihj ihk hl

end Yulang.CommonRoleFiniteStructuralClosure
