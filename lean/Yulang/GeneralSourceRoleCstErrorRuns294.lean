import Yulang.GeneralSourceRoleCstOriginalMarks294

/-! A portable view of adjacent original Error tokens. This is deliberately
not a reimplementation of Rust diagnostics or their grouping rules. -/
namespace Yulang.GeneralSourceRoleCstErrorRuns294
open GeneralSourceRoleCstTree293 (Path)
open GeneralSourceRoleCstOriginalMarks294 (Origin Element)

def splitLast : Path → Option (Path × Nat)
  | [] => none
  | [a] => some ([],a)
  | a::b::trail => (splitLast (b::trail)).map fun (p,i) => (a::p,i)

theorem split_exact (p parent : Path) (i : Nat) :
    splitLast p = some (parent,i) ↔ p = parent ++ [i] := by
  induction p generalizing parent i with
  | nil => simp [splitLast]
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases parent with
      | nil => simp [splitLast]
      | cons x xs =>
        constructor
        · intro bad; cases bad
        · intro h
          have impossible := (List.cons.inj h).2
          have sizes := congrArg List.length impossible
          simp at sizes
    | cons b tail =>
      cases parent with
      | nil =>
        constructor
        · intro h
          cases e : splitLast (b::tail) with
          | none => simp [splitLast,e] at h
          | some v =>
            rcases v with ⟨q,k⟩
            simp [splitLast,e] at h
        · intro h; cases h
      | cons c parents =>
        constructor
        · intro h
          cases e : splitLast (b::tail) with
          | none => simp [splitLast,e] at h
          | some v =>
            rcases v with ⟨q,k⟩
            have same : a = c ∧ q = parents ∧ k = i := by
              simpa [splitLast,e,and_assoc] using h
            rcases same with ⟨rfl,rfl,rfl⟩
            exact congrArg (a::·) ((ih q k).mp e)
        · intro h
          obtain ⟨rfl,eq⟩ := List.cons.inj h
          have e := (ih parents i).mpr eq
          simp [splitLast,e]

def bridge (a b : Origin) : Bool :=
  a.originalTag == "Error" && b.originalTag == "Error" &&
    a.originalMode == .token && b.originalMode == .token &&
    match splitLast a.occurrence.path, splitLast b.occurrence.path with
    | some (p,i),some (q,j) =>
      p == q && i+1 == j && a.occurrence.extent.high == b.occurrence.extent.low
    | _,_ => false

def Neighbors (a b : Origin) : Prop :=
  a.originalTag = "Error" ∧ b.originalTag = "Error" ∧
    a.originalMode = .token ∧ b.originalMode = .token ∧
    ∃ parent i, a.occurrence.path = parent ++ [i] ∧
      b.occurrence.path = parent ++ [i+1] ∧
      a.occurrence.extent.high = b.occurrence.extent.low

theorem bridge_exact (a b : Origin) : bridge a b = true ↔ Neighbors a b := by
  constructor
  · intro h
    simp only [bridge,Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨⟨⟨⟨atag,btag⟩,am⟩,bm⟩,location⟩ := h
    cases aPath : splitLast a.occurrence.path with
    | none => simp [aPath] at location
    | some first =>
      cases bPath : splitLast b.occurrence.path with
      | none => simp [aPath,bPath] at location
      | some second =>
        rcases first with ⟨p,i⟩
        rcases second with ⟨q,j⟩
        simp only [aPath,bPath,Bool.and_eq_true,beq_iff_eq] at location
        obtain ⟨⟨rfl,hj⟩,ends⟩ := location
        subst j
        exact ⟨atag,btag,am,bm,p,i,(split_exact ..).mp aPath,(split_exact ..).mp bPath,ends⟩
  · rintro ⟨atag,btag,am,bm,p,i,aHere,bHere,touch⟩
    have e := (split_exact ..).mpr aHere
    have f := (split_exact ..).mpr bHere
    simp [bridge,atag,btag,am,bm,e,f,touch]

def runs : List Origin → List (List Origin)
  | [] => []
  | a::more =>
    match runs more with
    | (b::tail)::rest => if bridge a b then (a::b::tail)::rest else [a]::(b::tail)::rest
    | other => [a]::other

theorem runs_flatten (origins : List Origin) : (runs origins).flatten = origins := by
  induction origins with
  | nil => rfl
  | cons a more ih =>
    cases h : runs more with
    | nil => simp [runs,h] at ih ⊢; exact ih
    | cons group rest =>
      cases group with
      | nil => simp [runs,h] at ih ⊢; exact ih
      | cons b tail =>
        by_cases bdy : bridge a b = true <;> simp [runs,h,bdy] at ih ⊢ <;> exact ih

inductive TokenRun : List Origin → Prop
  | singleton (x : Origin) : TokenRun [x]
  | cons {a b : Origin} {tail : List Origin} :
      Neighbors a b → TokenRun (b::tail) → TokenRun (a::b::tail)

theorem every_run (origins row : List Origin) (picked : row ∈ runs origins) : TokenRun row := by
  induction origins generalizing row with
  | nil => cases picked
  | cons a more ih =>
    cases h : runs more with
    | nil =>
      have is : row = [a] := by simpa [runs,h] using picked
      subst row
      exact .singleton a
    | cons group rest =>
      cases group with
      | nil =>
        have possible : row = [a] ∨ row ∈ []::rest := by simpa [runs,h] using picked
        rcases possible with rfl | next
        · exact .singleton a
        · exact ih row (h ▸ next)
      | cons b tail =>
        by_cases bdy : bridge a b = true
        · have mem : row = a::b::tail ∨ row ∈ rest := by simpa [runs,h,bdy] using picked
          rcases mem with rfl | notHere
          · exact .cons ((bridge_exact ..).mp bdy) (ih (b::tail) (h ▸ List.mem_cons_self))
          · exact ih row (h ▸ List.mem_cons_of_mem _ notHere)
        · have mem : row = [a] ∨ row ∈ (b::tail)::rest := by simpa [runs,h,bdy] using picked
          rcases mem with rfl | next
          · exact .singleton a
          · exact ih row (h ▸ next)

end Yulang.GeneralSourceRoleCstErrorRuns294
