import Yulang.GeneralDeclarativeI65I74ScopedGrammarTraversal460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
open Yulang.GeneralDeclarationPatterns

/-- Literal AST addresses, not diagnostic display locations or graph slots. -/
inductive Pose where
  | app (i : Nat)
  | payload
  | tail
  | variant
  | left
  | right
  deriving DecidableEq, Repr

abbrev Hit := List Pose × Pattern

def sourceStep : Pattern → Pose → Option Pattern
  | .app _ ps, .app i => ps[i]?
  | .record _ q _, .payload | .record _ _ q, .tail
  | .variant _ q, .variant | .join q _, .left | .join _ q, .right => some q
  | _, _ => none

def atSource (p : Pattern) : List Pose → Option Pattern
  | [] => some p
  | pose :: poses => (sourceStep p pose).bind fun q => atSource q poses

def under (b : Pose) (hits : List Hit) : List Hit :=
  hits.map fun x => (b :: x.1, x.2)

/-- Preserve every physical occurrence of a collapsed, equal join; never select
one for display. Distinct merged arms have no origin rule in this bridge. -/
def children (p : Pattern) (a : Address) : List Hit :=
  match p, a with
  | .join p q, a =>
      if normalize p = normalize q then under .left (children p a) ++ under .right (children q a)
      else []
  | .app _ ps, .arg i => (ps[i]?).toList.map fun p => ([.app i], p)
  | .record l p t, .field k =>
      if l = k then [([.payload], p)] else under .tail (children t (.field k))
  | .variant l p, .tag k => if l = k then [([.variant], p)] else []
  | _, _ => []

/-- Independent origin rules over the actual authored grammar. A hidden duplicate
of a requested field cannot be reached by going past its first written copy. -/
inductive Origin : Pattern → Address → List Pose → Pattern → Prop where
  | app : ps[i]? = some p → Origin (.app k ps) (.arg i) [.app i] p
  | field : Origin (.record l p t) (.field l) [.payload] p
  | tail : l ≠ k → Origin t (.field k) poses q →
      Origin (.record l p t) (.field k) (.tail :: poses) q
  | tag : Origin (.variant k p) (.tag k) [.variant] p
  | left : normalize p = normalize q → Origin p a poses x →
      Origin (.join p q) a (.left :: poses) x
  | right : normalize p = normalize q → Origin q a poses x →
      Origin (.join p q) a (.right :: poses) x

theorem literal_occurrence {p a poses q} (orig : Origin p a poses q) :
    atSource p poses = some q := by
  induction orig with
  | app h => simp [atSource,sourceStep,h,Option.bind]
  | field | tag => rfl
  | tail _ _ ih | left _ _ ih | right _ _ ih => exact ih

private theorem mem_under (b : Pose) (hits : List Hit) (poses : List Pose) (p : Pattern) :
    (poses,p) ∈ under b hits ↔ ∃ tail, poses = b :: tail ∧ (tail,p) ∈ hits := by
  simp only [under,List.mem_map]
  constructor
  · rintro ⟨⟨xs,q⟩,mem,heq⟩
    cases heq
    exact ⟨xs,rfl,mem⟩
  · rintro ⟨tail,rfl,mem⟩
    exact ⟨(tail,p),mem,rfl⟩

theorem exact_original_occurrences (p : Pattern) (a : Address) (poses : List Pose) (q : Pattern) :
    (poses,q) ∈ children p a ↔ Origin p a poses q := by
  constructor
  · intro mem
    cases p with
    | var n => cases a <;> simp [children] at mem
    | app k ps =>
      cases a with
      | field | tag => simp [children] at mem
      | arg i =>
        simp only [children,List.mem_map,Option.mem_toList] at mem
        obtain ⟨u,orig,eq⟩ := mem
        cases eq
        exact .app orig
    | record l p t =>
      cases a with
      | tag | arg => simp [children] at mem
      | field k =>
        by_cases same : l = k
        · subst k
          simp only [children,ite_true,List.mem_singleton] at mem
          cases mem
          exact .field
        · have z := (mem_under _ _ _ _).mp (by simpa [children,same] using mem)
          obtain ⟨tail,rfl,hit⟩ := z
          exact .tail same ((exact_original_occurrences t (.field k) tail q).mp hit)
    | variant l p =>
      cases a with
      | field | arg => simp [children] at mem
      | tag k =>
        by_cases same : l = k
        · subst k
          simp only [children,ite_true,List.mem_singleton] at mem
          cases mem
          exact .tag
        · simp [children,same] at mem
    | join p r =>
      by_cases same : normalize p = normalize r
      · have h : (poses,q) ∈ under .left (children p a) ++ under .right (children r a) := by
          simpa [children,same] using mem
        rcases List.mem_append.mp h with h | h
        · obtain ⟨tail,rfl,hit⟩ := (mem_under _ _ _ _).mp h
          exact .left same ((exact_original_occurrences p a tail q).mp hit)
        · obtain ⟨tail,rfl,hit⟩ := (mem_under _ _ _ _).mp h
          exact .right same ((exact_original_occurrences r a tail q).mp hit)
      · simp [children,same] at mem
  · intro orig
    induction orig with
    | app h => simp [children,h]
    | field | tag => simp [children]
    | tail ne _ ih => simpa [children,ne] using (mem_under _ _ _ _).mpr ⟨_,rfl,ih⟩
    | left eq _ ih =>
      simp only [children,eq,ite_true,List.mem_append]
      exact Or.inl ((mem_under _ _ _ _).mpr ⟨_,rfl,ih⟩)
    | right eq _ ih =>
      simp only [children,eq,ite_true,List.mem_append]
      exact Or.inr ((mem_under _ _ _ _).mpr ⟨_,rfl,ih⟩)
termination_by sizeOf p

/-- Exact membership when the selected normalized rule is also an existing G04
step. This checks the same selected field/argument, not an arbitrary hit. -/
def selectedOrigins (keys : KeyRead) (p : Pattern) (a : Address) : List Hit :=
  (children p a).filter fun x => match readStep keys (readTerm (normalize p)) a with
    | some q => decide (writeTerm q = normalize x.2)
    | none => false

theorem selected_occurrence_iff {keys p a poses q} :
    (poses,q) ∈ selectedOrigins keys p a ↔
      Origin p a poses q ∧ Step keys (readTerm (normalize p)) a (readTerm (normalize q)) := by
  simp only [selectedOrigins,List.mem_filter,exact_original_occurrences]
  refine and_congr_right fun _ => ?_
  cases h : readStep keys (readTerm (normalize p)) a with
  | none =>
    constructor
    · simp
    · intro s
      rw [read_step_complete s] at h
      contradiction
  | some u =>
    constructor
    · intro same
      have hs : writeTerm u = normalize q := of_decide_eq_true same
      rw [← hs,read_write_term]
      exact read_step_sound h
    · intro step
      rw [read_step_complete step] at h
      cases h
      simp


private theorem read_field_after_other_hide {k l : Nat} (ne : k ≠ l) (p : Pattern) :
    readField k (readTerm (hide l p)) = readField k (readTerm p) := by
  cases p with
  | record n u t =>
    by_cases h : l = n
    · subst n
      simpa [hide,readTerm,readField,ne] using read_field_after_other_hide ne t
    · by_cases g : k = n
      · simp [hide,h,readTerm,readField,g]
      · simpa [hide,h,readTerm,readField,g] using read_field_after_other_hide ne t
  | _ => rfl

private theorem row_pattern_does_not_expose_field (k : Nat) (xs : List (Nat × Pattern)) :
    readField k (readTerm (rowPattern xs)) = none := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    obtain ⟨l,p⟩ := x
    cases xs <;> rfl

private theorem distinct_merge_does_not_expose_field {k : Nat} {p q : Pattern} (ne : p ≠ q) :
    readField k (readTerm (merge p q)) = none := by
  unfold merge
  rw [ite_eq_right ne]
  split
  · exact row_pattern_does_not_expose_field _ _
  · rfl

/-- Every actually selected normalized field, at any authored pattern, has
an original written occurrence. This uses no chosen representative for an
equal join, and does not interpret a surviving distinct join as traversable. -/
theorem actual_normalized_field_has_literal_origin (k : Nat) (p : Pattern) (u : Term)
    (sel : readField k (readTerm (normalize p)) = some u) :
    ∃ poses q, Origin p (.field k) poses q ∧ readTerm (normalize q) = u := by
  cases p with
  | var | app | variant => simp [normalize,readTerm,readField] at sel
  | record l p t =>
    by_cases eq : l = k
    · subst l
      simp [normalize,readTerm,readField] at sel
      exact ⟨[.payload],p,.field,sel⟩
    · have ne : k ≠ l := Ne.symm eq
      simp only [normalize,readTerm,readField,ne,ite_false] at sel
      rw [read_field_after_other_hide ne] at sel
      obtain ⟨poses,q,o,h⟩ := actual_normalized_field_has_literal_origin k t u sel
      exact ⟨.tail :: poses,q,.tail eq o,h⟩
  | join p q =>
    by_cases same : normalize p = normalize q
    · simp only [normalize,merge,same,ite_true] at sel
      have h : readField k (readTerm (normalize p)) = some u := by simpa [same] using sel
      obtain ⟨poses,l,o,eq⟩ := actual_normalized_field_has_literal_origin k p u h
      exact ⟨.left :: poses,l,.left same o,eq⟩
    · simp only [normalize,distinct_merge_does_not_expose_field same] at sel
      cases sel

theorem every_existing_normalized_field_step_has_finite_original_position
    {keys : KeyRead} {p : Pattern} {k : Nat} {u : Term}
    (step : Step keys (readTerm (normalize p)) (.field k) u) :
    ∃ poses q, (poses,q) ∈ selectedOrigins keys p (.field k) ∧
      readTerm (normalize q) = u ∧ atSource p poses = some q := by
  have hit : readField k (readTerm (normalize p)) = some u := by
    revert step
    generalize readTerm (normalize p) = t
    intro step
    cases step with
    | field _ f => exact (read_field_iff ..).mpr f
  obtain ⟨poses,q,orig,same⟩ := actual_normalized_field_has_literal_origin k p u hit
  exact ⟨poses,q,selected_occurrence_iff.mpr ⟨orig,same.symm ▸ step⟩,
    same,literal_occurrence orig⟩



private theorem row_pattern_app_has_no_argument (xs : List (Nat × Pattern)) {key : Nat}
    {ps : List Pattern} (shape : rowPattern xs = .app key ps) : ps = [] := by
  cases xs with
  | nil => cases shape; rfl
  | cons x xs =>
    obtain ⟨l,p⟩ := x
    cases xs <;> cases shape

private theorem distinct_merge_app_has_no_argument {p q : Pattern} (ne : p ≠ q)
    {key : Nat} {ps : List Pattern} (shape : merge p q = .app key ps) : ps = [] := by
  unfold merge at shape
  rw [ite_eq_right ne] at shape
  split at shape
  · exact row_pattern_app_has_no_argument _ shape
  · cases shape

/-- A genuinely selected argument in a nonempty application still has a
literal original occurrence. Different merged arms cannot invent that app. -/
theorem actual_normalized_argument_has_literal_origin (p : Pattern) (key i : Nat)
    (ps : List Pattern) (v : Pattern) (shape : normalize p = .app key ps)
    (hit : ps[i]? = some v) :
    ∃ poses q, Origin p (.arg i) poses q ∧ normalize q = v := by
  cases p with
  | var | record | variant => simp [normalize] at shape
  | app name args =>
    simp only [normalize,Pattern.app.injEq] at shape
    rw [← shape.2] at hit
    have elem : ∀ (as : List Pattern) (j : Nat), (normalizeArgs as)[j]? = (as[j]?).map normalize := by
      intro as j
      induction as generalizing j with
      | nil => rfl
      | cons h t ih =>
        cases j with
        | zero => rfl
        | succ j => exact ih j
    rw [elem] at hit
    obtain ⟨q,occ,val⟩ := Option.map_eq_some_iff.mp hit
    exact ⟨[.app i],q,.app occ,val⟩
  | join p q =>
    by_cases same : normalize p = normalize q
    · have fit : normalize p = .app key ps := by simpa [normalize,merge,same] using shape
      obtain ⟨poses,x,orig,exact⟩ := actual_normalized_argument_has_literal_origin p key i ps v fit hit
      exact ⟨.left :: poses,x,.left same orig,exact⟩
    · have empty := distinct_merge_app_has_no_argument same (by simpa only [normalize] using shape)
      rw [empty] at hit
      cases hit

open RecordTraversal455.MixedQA (MixedPath)

/-- One finite enumeration for any already-selected raw path. It visits
only requested AST coordinates, and returns no new raw edges. -/
def locateRoute (keys : Nat → KeyRead) (p : Pattern) (n : Nat) : MixedPath → List Hit
  | [] => [([],p)]
  | (a,c) :: more => (selectedOrigins (keys n) p (writtenAddress a)).flatMap fun x =>
      (locateRoute keys x.2 c more).map fun y => (x.1 ++ y.1,y.2)

inductive OriginalWalk (keys : Nat → KeyRead) :
    Pattern → Nat → MixedPath → List Pose → Pattern → Prop where
  | stop : OriginalWalk keys p n [] [] p
  | down : Origin p (writtenAddress a) first q →
      Step (keys n) (readTerm (normalize p)) (writtenAddress a) (readTerm (normalize q)) →
      OriginalWalk keys q c more rest u →
      OriginalWalk keys p n ((a,c)::more) (first ++ rest) u

theorem route_occurrences_exact {keys p n path poses u} :
    (poses,u) ∈ locateRoute keys p n path ↔ OriginalWalk keys p n path poses u := by
  induction path generalizing p n poses with
  | nil =>
    constructor
    · intro h
      simp only [locateRoute,List.mem_singleton] at h
      cases h
      exact .stop
    · intro h
      cases h
      simp [locateRoute]
  | cons entry more ih =>
    obtain ⟨a,c⟩ := entry
    simp only [locateRoute,List.mem_flatMap]
    constructor
    · rintro ⟨⟨first,q⟩,source,also⟩
      rw [List.mem_map] at also
      obtain ⟨⟨rest,t⟩,inside,eq⟩ := also
      cases eq
      obtain ⟨orig,step⟩ := selected_occurrence_iff.mp source
      exact .down orig step ((ih).mp inside)
    · intro h
      cases h with
      | down orig step more =>
        exact ⟨_,selected_occurrence_iff.mpr ⟨orig,step⟩,
          List.mem_map.mpr ⟨_,ih.mpr more,rfl⟩⟩

private theorem at_appended_source (p : Pattern) (x y : List Pose) :
    atSource p (x ++ y) = (atSource p x).bind fun q => atSource q y := by
  induction x generalizing p with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.cons_append,atSource,Option.bind_assoc,ih]

theorem whole_route_is_literal_and_preserves_exact_coordinates {keys p n path poses u}
    (h : OriginalWalk keys p n path poses u) :
    atSource p poses = some u ∧
      ∃ last, CoordinateWalk keys n (readTerm (normalize p)) path last (readTerm (normalize u)) := by
  induction h with
  | stop => exact ⟨rfl,_,.stop⟩
  | down orig step _ ih =>
    obtain ⟨look,last,actual⟩ := ih
    constructor
    · rw [at_appended_source,literal_occurrence orig]
      exact look
    · exact ⟨last,.down step actual⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
