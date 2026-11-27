import Yulang.GeneralDeclarativeI65I74WrittenPattern460

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460

/-- These are readings of resolved keys at the current site, not promises
made by a proposed path witness.  A concrete replay supplies the catalogue
and point/mode evidence separately. -/
inductive KeyView where
  | emptyRow | binaryPair | covariantPoint | deferredNominal | opaque
  deriving DecidableEq

abbrev KeyRead := Nat → KeyView

inductive Address where
  | field (label : Nat)
  | tag (label : Nat)
  | arg (index : Nat)
  deriving DecidableEq

/-- A closed row may have any payload, including an unsupported term. -/
inductive ClosedSpine (keys : KeyRead) : Term → Prop
  | empty : keys key = .emptyRow → ClosedSpine keys (.app key .nil)
  | next : ClosedSpine keys tail → ClosedSpine keys (.record label item tail)

def closedSpine (keys : KeyRead) : Term → Bool
  | .app n .nil => keys n == .emptyRow
  | .record _ _ tail => closedSpine keys tail
  | _ => false

theorem closed_spine_iff (keys : KeyRead) (p : Term) :
    closedSpine keys p = true ↔ ClosedSpine keys p := by
  constructor
  · intro h
    cases p with
    | app k xs =>
      cases xs with
      | nil => exact .empty (of_decide_eq_true h)
      | cons p ps => simp [closedSpine] at h
    | record l p t => exact .next ((closed_spine_iff keys t).mp h)
    | var | variant | join => simp [closedSpine] at h
  · intro h
    induction h with
    | empty r => simp [closedSpine,r]
    | next _ ih => exact ih

/-- Find the first written field with this label, without opening any payload. -/
inductive FirstField : Nat → Term → Term → Prop
  | here : FirstField k (.record k item tail) item
  | later : k ≠ l → FirstField k tail item → FirstField k (.record l skipped tail) item

def readField (k : Nat) : Term → Option Term
  | .record l p t => if k = l then some p else readField k t
  | _ => none

theorem read_field_iff (key : Nat) (p q : Term) :
    readField key p = some q ↔ FirstField key p q := by
  constructor
  · intro h
    cases p with
    | record l p t =>
      by_cases same : key = l
      · subst l
        simp [readField] at h
        subst q
        exact .here
      · exact .later same ((read_field_iff key t q).mp (by simpa [readField,same] using h))
    | var | app | variant | join => simp [readField] at h
  · intro h
    induction h with
    | here => simp [readField]
    | later ne _ ih => simpa [readField,ne] using ih

/-- A written-child step, not a graph edge.  Applications with other kinds or
arities and joins have no rule. A captured binder does not license a visit. -/
inductive Step (keys : KeyRead) : Term → Address → Term → Prop
  | field : ClosedSpine keys tail → FirstField l (.record k p tail) q →
      Step keys (.record k p tail) (.field l) q
  | tag : Step keys (.variant t p) (.tag t) p
  | pair0 : keys k = .binaryPair → Step keys (.app k (.cons p (.cons q .nil))) (.arg 0) p
  | pair1 : keys k = .binaryPair → Step keys (.app k (.cons p (.cons q .nil))) (.arg 1) q
  | point : keys k = .covariantPoint → Step keys (.app k (.cons p .nil)) (.arg 0) p

def readStep (keys : KeyRead) : Term → Address → Option Term
  | .record k p tail, .field l =>
      if closedSpine keys tail then readField l (.record k p tail) else none
  | .variant t p, .tag l => if t = l then some p else none
  | .app k (.cons p (.cons q .nil)), .arg i =>
      if keys k = .binaryPair then
        match i with
        | 0 => some p
        | 1 => some q
        | _ => none
      else none
  | .app k (.cons p .nil), .arg 0 => if keys k = .covariantPoint then some p else none
  | _, _ => none

/-- Syntax-only route. An empty route does not assert an actual inspection.
The terminal field and raw K2 must be established by the graph-side judgment. -/
inductive Walk (keys : KeyRead) : Term → List Address → Term → Prop
  | done : Walk keys p [] p
  | next : Step keys p a q → Walk keys q as r → Walk keys p (a :: as) r

def readWalk (keys : KeyRead) (p : Term) : List Address → Option Term
  | [] => some p
  | a :: as => do readWalk keys (← readStep keys p a) as

theorem read_step_sound {keys p a q} (ok : readStep keys p a = some q) :
    Step keys p a q := by
  cases p with
  | var => simp [readStep] at ok
  | join => simp [readStep] at ok
  | record k p t =>
    cases a with
    | tag | arg => simp [readStep] at ok
    | field l =>
      by_cases closed : closedSpine keys t = true
      · exact .field ((closed_spine_iff _ _).mp closed)
          ((read_field_iff _ _ _).mp (by simpa [readStep,closed] using ok))
      · simp [readStep,closed] at ok
  | variant t p =>
    cases a with
    | field | arg => simp [readStep] at ok
    | tag l =>
      by_cases same : t = l
      · subst l
        simp [readStep] at ok
        subst q
        exact .tag
      · simp [readStep,same] at ok
  | app k xs =>
    cases a with
    | field | tag => simp [readStep] at ok
    | arg i =>
      cases xs with
      | nil => simp [readStep] at ok
      | cons p ps =>
        cases ps with
        | nil =>
          cases i with
          | zero =>
            by_cases yes : keys k = .covariantPoint
            · simp [readStep,yes] at ok
              subst q
              exact .point yes
            · simp [readStep,yes] at ok
          | succ => simp [readStep] at ok
        | cons r rs =>
          cases rs with
          | cons => simp [readStep] at ok
          | nil =>
            by_cases yes : keys k = .binaryPair
            · cases i with
              | zero =>
                simp [readStep,yes] at ok
                subst q
                exact .pair0 yes
              | succ i =>
                cases i with
                | zero =>
                  simp [readStep,yes] at ok
                  subst q
                  exact .pair1 yes
                | succ => simp [readStep,yes] at ok
            · simp [readStep,yes] at ok

theorem read_step_complete {keys p a q} (s : Step keys p a q) :
    readStep keys p a = some q := by
  cases s with
  | field c f => simp [readStep,(closed_spine_iff _ _).mpr c,(read_field_iff _ _ _).mpr f]
  | tag => simp [readStep]
  | pair0 h | pair1 h | point h => simp [readStep,h]

theorem read_step_iff {keys p a q} : readStep keys p a = some q ↔ Step keys p a q :=
  ⟨read_step_sound,read_step_complete⟩

theorem read_walk_iff (keys : KeyRead) (p : Term) (as : List Address) (q : Term) :
    readWalk keys p as = some q ↔ Walk keys p as q := by
  induction as generalizing p with
  | nil =>
    constructor
    · intro h
      have e : p = q := by simpa [readWalk] using h
      subst q
      exact .done
    · intro h
      cases h
      rfl
  | cons a as ih =>
    constructor
    · intro ok
      cases e : readStep keys p a with
      | none => simp [readWalk,e,Option.bind] at ok
      | some child =>
        exact .next (read_step_sound e) ((ih child).mp (by simpa [readWalk,e,Option.bind] using ok))
    · intro h
      cases h with
      | next step rest => simpa [readWalk,read_step_complete step,Option.bind] using (ih _).mpr rest

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
