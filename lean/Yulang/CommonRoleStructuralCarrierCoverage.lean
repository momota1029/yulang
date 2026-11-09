import Yulang.CommonRoleFiniteStructuralClosure

/-! Syntactic coverage of the computed carrier for the existing structural rules.
This does not assert completeness for all semantic subtype consequences. -/
namespace Yulang.CommonRoleStructuralCarrierCoverage
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom)
open CommonRoleFiniteStructuralClosure

theorem self_terms (t : TyTerm (Fin n)) : t ∈ terms t := by
  cases t <;> simp [terms]

theorem descendants (t : TyTerm (Fin n)) :
    ∀ s ∈ terms t, (∀ x ∈ terms s, x ∈ terms t) ∧
      (∀ e ∈ rows s, e ∈ rows t) := by
  induction t with
  | pair a b ia ib =>
    intro s hs
    rcases (show s = .pair a b ∨ s ∈ terms a ∨ s ∈ terms b by simpa [terms] using hs) with rfl | ha | hb
    · exact ⟨fun _ h => h, fun _ h => h⟩
    · exact ⟨fun x hx => by simp [terms, (ia s ha).1 x hx], fun e he => by simp [rows, (ia s ha).2 e he]⟩
    · exact ⟨fun x hx => by simp [terms, (ib s hb).1 x hx], fun e he => by simp [rows, (ib s hb).2 e he]⟩
  | arrow a ea b eb ia ib =>
    intro s hs
    rcases (show s = .arrow a ea b eb ∨ s ∈ terms a ∨ s ∈ terms b by simpa [terms] using hs) with rfl | ha | hb
    · exact ⟨fun _ h => h, fun _ h => h⟩
    · exact ⟨fun x hx => by simp [terms, (ia s ha).1 x hx], fun e he => by simp [rows, (ia s ha).2 e he]⟩
    · exact ⟨fun x hx => by simp [terms, (ib s hb).1 x hx], fun e he => by simp [rows, (ib s hb).2 e he]⟩
  | variant tag a ia =>
    intro s hs
    rcases (show s = .variant tag a ∨ s ∈ terms a by simpa [terms] using hs) with rfl | ha
    · exact ⟨fun _ h => h, fun _ h => h⟩
    · exact ⟨fun x hx => by simp [terms, (ia s ha).1 x hx], fun e he => (ia s ha).2 e he⟩
  | _ => simp [terms, rows]

def typePool (seeds : List (Atom (Fin n))) : List (TyTerm (Fin n)) :=
  seeds.flatMap fun x => match x with
    | .tyLe l r => terms l ++ terms r
    | .rowLe _ _ => []
def rowPool (seeds : List (Atom (Fin n))) : List (RowTerm (Fin n)) :=
  seeds.flatMap fun x => match x with
    | .tyLe l r => rows l ++ rows r
    | .rowLe l r => [l,r]

def Supported (ts : List (TyTerm (Fin n))) (rs : List (RowTerm (Fin n))) : Atom (Fin n) → Prop
  | .tyLe l r => (∀ x ∈ terms l, x ∈ ts) ∧ (∀ x ∈ terms r, x ∈ ts) ∧
    (∀ e ∈ rows l, e ∈ rs) ∧ (∀ e ∈ rows r, e ∈ rs)
  | .rowLe l r => l ∈ rs ∧ r ∈ rs

theorem expand_supported (ts : List (TyTerm (Fin n))) (rs : List (RowTerm (Fin n)))
    (k : Nat) (l r : TyTerm (Fin n))
    (h : Supported ts rs (.tyLe l r)) :
    ∀ z ∈ CommonRoleStructuralDecomposition.expandFuel k l r, Supported ts rs z := by
  induction k generalizing l r with
  | zero => simpa [CommonRoleStructuralDecomposition.expandFuel] using h
  | succ k ih =>
    simp only [CommonRoleStructuralDecomposition.expandFuel]
    split
    · simp only [List.mem_append, or_imp, forall_and]
      rename_i a b c d
      simp only [Supported, terms, rows, List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq] at h
      constructor
      · apply ih; exact ⟨h.1.2.1,h.2.1.2.1,h.2.2.1.1,h.2.2.2.1⟩
      · apply ih; exact ⟨h.1.2.2,h.2.1.2.2,h.2.2.1.2,h.2.2.2.2⟩
    · rename_i a ea b eb c ec d ed
      simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
      have hs := h
      simp only [Supported, terms, rows, List.mem_cons, List.mem_append,
        or_imp, forall_and, forall_eq] at hs
      constructor
      · constructor
        · constructor
          · apply ih; exact ⟨hs.2.1.2.1, hs.1.2.1, hs.2.2.2.2.2.1, hs.2.2.1.2.2.1⟩
          · exact ⟨hs.2.2.2.1, hs.2.2.1.1⟩
        · apply ih; exact ⟨hs.1.2.2, hs.2.1.2.2, hs.2.2.1.2.2.2, hs.2.2.2.2.2.2⟩
      · exact ⟨hs.2.2.1.2.1, hs.2.2.2.2.1⟩
    · rename_i i a j b
      split
      · apply ih
        simp only [Supported, terms, rows, List.mem_cons, or_imp, forall_and, forall_eq] at h ⊢
        exact ⟨h.1.2,h.2.1.2,h.2.2⟩
      · simpa using h
    · simpa using h

theorem pool_descendants (seeds : List (Atom (Fin n))) (t : TyTerm (Fin n))
    (ht : t ∈ typePool seeds) :
    (∀ x ∈ terms t, x ∈ typePool seeds) ∧ (∀ e ∈ rows t, e ∈ rowPool seeds) := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  cases a with
  | rowLe l r => simp at ht
  | tyLe l r =>
    rcases List.mem_append.mp ht with hl | hr
    · exact ⟨fun x hx => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_left _ ((descendants l t hl).1 x hx)⟩,
        fun e he => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_left _ ((descendants l t hl).2 e he)⟩⟩
    · exact ⟨fun x hx => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_right _ ((descendants r t hr).1 x hx)⟩,
        fun e he => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_right _ ((descendants r t hr).2 e he)⟩⟩

theorem carrier_iff (seeds : List (Atom (Fin n))) (a : Atom (Fin n)) :
    a ∈ carrier seeds ↔ Supported (typePool seeds) (rowPool seeds) a := by
  cases a with
  | rowLe l r => simp [carrier, Supported, rowPool]; rfl
  | tyLe l r =>
    have mem : Atom.tyLe l r ∈ carrier seeds ↔ l ∈ typePool seeds ∧ r ∈ typePool seeds := by
      simp [carrier, typePool]; rfl
    rw [mem]
    constructor
    · rintro ⟨hl,hr⟩
      exact ⟨(pool_descendants seeds l hl).1,(pool_descendants seeds r hr).1,
        (pool_descendants seeds l hl).2,(pool_descendants seeds r hr).2⟩
    · intro h; exact ⟨h.1 l (self_terms l),h.2.1 r (self_terms r)⟩

theorem seed_coverage (seeds : List (Atom (Fin n))) (a : Atom (Fin n)) (ha : a ∈ seeds) :
    a ∈ carrier seeds := by
  apply (carrier_iff seeds a).mpr
  cases a with
  | tyLe l r =>
    exact ⟨fun x hx => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_left _ hx⟩,
      fun x hx => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_right _ hx⟩,
      fun e he => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_left _ he⟩,
      fun e he => List.mem_flatMap.mpr ⟨.tyLe l r,ha,List.mem_append_right _ he⟩⟩
  | rowLe l r =>
    exact ⟨List.mem_flatMap.mpr ⟨.rowLe l r,ha,by simp⟩,
      List.mem_flatMap.mpr ⟨.rowLe l r,ha,by simp⟩⟩

theorem split_coverage (seeds : List (Atom (Fin n))) (a b : Atom (Fin n))
    (ha : a ∈ carrier seeds) (hb : b ∈ CommonRoleStructuralDecomposition.atom a) :
    b ∈ carrier seeds := by
  apply (carrier_iff seeds b).mpr
  have h := (carrier_iff seeds a).mp ha
  cases a with
  | tyLe l r => exact expand_supported _ _ _ _ _ h b hb
  | rowLe l r =>
    have eq : b = .rowLe l r := by simpa [CommonRoleStructuralDecomposition.atom] using hb
    subst b; exact h

theorem trans_coverage (seeds : List (Atom (Fin n))) (a b c : Atom (Fin n))
    (ha : a ∈ carrier seeds) (hb : b ∈ carrier seeds) (hc : c ∈ compose a b) :
    c ∈ carrier seeds := by
  have h₁ := (carrier_iff seeds a).mp ha
  have h₂ := (carrier_iff seeds b).mp hb
  apply (carrier_iff seeds c).mpr
  cases a <;> cases b <;> simp only [compose] at hc
  case tyLe.tyLe l m m' r =>
    split at hc
    · have eq : c = .tyLe l r := by simpa using hc
      subst c; exact ⟨h₁.1,h₂.2.1,h₁.2.2.1,h₂.2.2.2⟩
    · simp at hc
  all_goals simp at hc

/-- Independent atom derivation with no carrier or index side conditions. -/
inductive Derives (seeds : List (Atom (Fin n))) : Atom (Fin n) → Prop where
  | seed (a) : a ∈ seeds → Derives seeds a
  | split (a b) : Derives seeds a → b ∈ CommonRoleStructuralDecomposition.atom a → Derives seeds b
  | trans (a b c) : Derives seeds a → Derives seeds b → c ∈ compose a b → Derives seeds c

theorem derives_coverage {seeds : List (Atom (Fin n))} {a : Atom (Fin n)}
    (h : Derives seeds a) : a ∈ carrier seeds := by
  induction h with
  | seed a ha => exact seed_coverage seeds a ha
  | split a b _ hb ih => exact split_coverage seeds a b ih hb
  | trans a b c _ _ hc iha ihb => exact trans_coverage seeds a b c iha ihb hc

theorem indexed_sound (seeds u : List (Atom (Fin n))) (i : Index u)
    (h : CommonRoleFiniteStructuralClosure.Derived seeds u i) : Derives seeds u[i] := by
  induction h with
  | seed i hi => exact .seed _ hi
  | split i j _ hj ih => exact .split _ _ ih hj
  | trans i j k _ _ hk ihi ihj => exact .trans _ _ _ ihi ihj hk

theorem derives_seen {seeds : List (Atom (Fin n))} {a : Atom (Fin n)} (h : Derives seeds a) :
    ∀ i : Index (seeds ++ carrier seeds), (seeds ++ carrier seeds)[i] = a →
      i ∈ seen seeds (seeds ++ carrier seeds) := by
  induction h with
  | seed a ha =>
    intro i hi; apply seed_seen; simpa [hi] using ha
  | split a b ha hb ih =>
    intro j hj
    have hm : a ∈ seeds ++ carrier seeds := List.mem_append_right _ (derives_coverage ha)
    obtain ⟨i,hi⟩ := List.get_of_mem hm
    apply split_seen seeds _ i j (ih i hi)
    simpa [hj,show (seeds ++ carrier seeds)[i] = a from hi] using hb
  | trans a b c ha hb hc iha ihb =>
    intro k hk
    obtain ⟨i,hi⟩ := List.get_of_mem (List.mem_append_right seeds (derives_coverage ha))
    obtain ⟨j,hj⟩ := List.get_of_mem (List.mem_append_right seeds (derives_coverage hb))
    apply trans_seen seeds _ i j k (iha i hi) (ihb j hj)
    simpa [hk,show (seeds ++ carrier seeds)[i] = a from hi,
      show (seeds ++ carrier seeds)[j] = b from hj] using hc

/-- Exactness for supported decomposition/transitivity, not full semantic subtyping. -/
theorem normalize_membership (seeds : List (Atom (Fin n))) (a : Atom (Fin n)) :
    a ∈ normalize seeds ↔ Derives seeds a := by
  constructor
  · intro h
    rcases List.mem_append.mp h with hs | hc
    · exact .seed a hs
    · obtain ⟨i,hi,eq⟩ := List.mem_map.mp hc
      subst a
      exact indexed_sound seeds _ i ((CommonRoleFiniteStructuralClosure.exact ..).mp hi)
  · intro h
    have hm : a ∈ seeds ++ carrier seeds := List.mem_append_right _ (derives_coverage h)
    obtain ⟨i,hi⟩ := List.get_of_mem hm
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,derives_seen h i hi,hi⟩

/-- Substituting derived seeds does not enlarge the rule closure. -/
theorem derives_cut {seeds more : List (Atom (Fin n))} {a : Atom (Fin n)}
    (hm : ∀ b ∈ more, Derives seeds b) (h : Derives more a) : Derives seeds a := by
  induction h with
  | seed b hb => exact hm b hb
  | split b c _ hc ih => exact .split b c ih hc
  | trans b c d _ _ hd ihb ihc => exact .trans b c d ihb ihc hd

/-- Membership idempotence; list order and duplicate multiplicities are not compared. -/
theorem normalize_idempotent (seeds : List (Atom (Fin n))) (a : Atom (Fin n)) :
    a ∈ normalize (normalize seeds) ↔ a ∈ normalize seeds := by
  rw [normalize_membership]
  constructor
  · intro h
    exact (normalize_membership seeds a).mpr
      (derives_cut (fun b hb => (normalize_membership seeds b).mp hb) h)
  · intro h; exact .seed a h

/-- The closure depends only on seed membership, not enumeration or duplicates. -/
theorem normalize_congr (left right : List (Atom (Fin n)))
    (h : ∀ a, a ∈ left ↔ a ∈ right) (a : Atom (Fin n)) :
    a ∈ normalize left ↔ a ∈ normalize right := by
  rw [normalize_membership,normalize_membership]
  exact ⟨fun d => derives_cut (fun b hb => .seed b ((h b).mp hb)) d,
    fun d => derives_cut (fun b hb => .seed b ((h b).mpr hb)) d⟩

/-- Every output is in the syntax-computed finite carrier. -/
theorem normalize_coverage (seeds : List (Atom (Fin n))) (a : Atom (Fin n))
    (h : a ∈ normalize seeds) : a ∈ carrier seeds :=
  derives_coverage ((normalize_membership seeds a).mp h)

/-- Any set containing the input and closed under the supported rules contains the output. -/
theorem normalize_least (seeds : List (Atom (Fin n))) (P : Atom (Fin n) → Prop)
    (hs : ∀ a ∈ seeds, P a)
    (hd : ∀ a b, P a → b ∈ CommonRoleStructuralDecomposition.atom a → P b)
    (ht : ∀ a b c, P a → P b → c ∈ compose a b → P c)
    (a : Atom (Fin n)) (ha : a ∈ normalize seeds) : P a := by
  have h := (normalize_membership seeds a).mp ha
  clear ha
  induction h with
  | seed b hb => exact hs b hb
  | split b c _ hc ih => exact hd b c ih hc
  | trans b c d _ _ he ihb ihc => exact ht b c d ihb ihc he

end Yulang.CommonRoleStructuralCarrierCoverage
