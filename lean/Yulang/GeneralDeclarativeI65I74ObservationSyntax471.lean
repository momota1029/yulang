import Yulang.GeneralDeclarativeI65I74InlineNominalPoint458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open GeneralNormalizedObservation (Shape)
open CommonRoleCanonicalRows (normalize)
open GeneralDeclarativeI65 (State)
open InlineNominalPoint458 (checkMode HasMode only_actual_covariant_unary_declared_mode458)

/-- Addresses relative to one unchanged raw equation's literal RHS.
These are not new physical names or diagnostic display choices. -/
inductive Slot where
  | field (label : Nat)
  | variant
  | argument (ordinal : Nat)
  deriving DecidableEq, Repr

/-- Compact typed signatures. Structural names are given a common
injective finite encoding only when building an observation graph. -/
inductive Label where
  | scalar (base : Inference.Base)
  | structural (shape : Shape)
  | nominal (key : Nat)
  deriving DecidableEq

/-- Stage one collects a finite completely closed field spine.
Do not replace an open tail or unknown join with an empty record. -/
def literalFields : Expr → Option (List (Nat × Expr))
  | .primitive .emptyRecord [] => some []
  | .record key payload tail => (literalFields tail).map ((key,payload) :: ·)
  | _ => none

inductive ClosedFields : Expr → List (Nat × Expr) → Prop where
  | empty : ClosedFields (.primitive .emptyRecord []) []
  | field : ClosedFields tail fields →
      ClosedFields (.record label value tail) ((label,value) :: fields)

theorem closed_fields_read (e : Expr) {fs} (ok : literalFields e = some fs) :
    ClosedFields e fs := by
  cases e with
  | record l v tail =>
    cases next : literalFields tail with
    | none => simp [literalFields,next] at ok
    | some rest =>
      have same : (l,v) :: rest = fs := by simpa [literalFields,next] using ok
      subst fs
      exact .field (closed_fields_read tail next)
  | primitive tag args =>
    cases tag <;> cases args <;> cases ok
    exact .empty
  | «variable» | nominal | variant | join => cases ok
termination_by structural e

theorem closed_fields_exact {e fs} : literalFields e = some fs ↔ ClosedFields e fs := by
  constructor
  · exact closed_fields_read e
  · intro h
    induction h with
    | empty => rfl
    | field _ ih => simp [literalFields,ih]

def sortedFields (fs : List (Nat × Expr)) : List (Nat × Expr) :=
  (normalize fs).mergeSort (fun a b => a.1 ≤ b.1)

def RecordEntries (fs : List (Nat × Expr)) : List (Slot × Expr) :=
  (sortedFields fs).map fun f => (.field f.1,f.2)

/-- Enumerate just the actual explicit children of a constructor that
can be represented by G04. Unions, variables and unsupported heads
produce none, not negative evidence. Named expansion belongs elsewhere. -/
def readDescription (s : GeneralDeclarativeI65.State) :
    Expr → Option (Label × List (Slot × Expr))
  | .primitive (.scalar base) [] => some (.scalar base,[])
  | .primitive .pair [a,b] => some (.structural .pair,[(.argument 0,a),(.argument 1,b)])
  | .primitive .emptyRecord [] => some (.structural (.record []),[])
  | .primitive .exactEmpty [] => some (.structural .exactEmpty,[])
  | .nominal key [child] =>
      if checkMode s key then some (.nominal key,[(.argument 0,child)]) else none
  | .variant key t => some (.structural (.variant key),[(.variant,t)])
  | .record label a tail =>
      (literalFields tail).map fun fs =>
        let chosen := sortedFields ((label,a) :: fs)
        (.structural (.record (chosen.map Prod.fst)), chosen.map fun f => (.field f.1,f.2))
  | _ => none

inductive ReadsDescription (s : GeneralDeclarativeI65.State) :
    Expr → Label → List (Slot × Expr) → Prop where
  | scalar : ReadsDescription s (.primitive (.scalar k) []) (.scalar k) []
  | pair : ReadsDescription s (.primitive .pair [a,b]) (.structural .pair)
      [(.argument 0,a),(.argument 1,b)]
  | empty : ReadsDescription s (.primitive .emptyRecord []) (.structural (.record [])) []
  | exactEmpty : ReadsDescription s (.primitive .exactEmpty []) (.structural .exactEmpty) []
  | declared : HasMode s k → ReadsDescription s (.nominal k [x]) (.nominal k) [(.argument 0,x)]
  | variant : ReadsDescription s (.variant k x) (.structural (.variant k)) [(.variant,x)]
  | record : ClosedFields tail fs →
      ReadsDescription s (.record l p tail) (.structural (.record ((sortedFields ((l,p)::fs)).map Prod.fst)))
        (RecordEntries ((l,p)::fs))

theorem description_exact {s e l cs} : readDescription s e = some (l,cs) ↔ ReadsDescription s e l cs := by
  constructor
  · intro ok
    cases e with
    | «variable» | join => cases ok
    | variant => cases ok; exact .variant
    | nominal key args =>
      cases args with
      | nil => cases ok
      | cons child rem =>
        cases rem with
        | cons => cases ok
        | nil =>
          by_cases mode : checkMode s key = true
          · have pos : (.nominal key,[(Slot.argument 0,child)]) = (l,cs) := by
              simpa [readDescription,mode] using ok
            cases pos
            exact .declared ((only_actual_covariant_unary_declared_mode458 ..).mp mode)
          · simp [readDescription,mode] at ok
    | record label payload tail =>
      cases found : literalFields tail with
      | none => simp [readDescription,found] at ok
      | some fs =>
        have good := Option.some.inj (by simpa [readDescription,found,RecordEntries] using ok :
          some (.structural (.record ((sortedFields ((label,payload)::fs)).map Prod.fst)),
            RecordEntries ((label,payload)::fs)) = some (l,cs))
        cases good
        exact .record (closed_fields_exact.mp found)
    | primitive tag args =>
      cases tag <;> cases args <;> try cases ok
      all_goals first
        | exact .scalar
        | exact .empty
        | exact .exactEmpty
        | rename_i a others
          cases others with
          | nil => cases ok
          | cons b rem =>
            cases rem <;> cases ok
            exact .pair
  · intro intended
    cases intended
    case declared h => simp [readDescription,(only_actual_covariant_unary_declared_mode458 ..).mpr h]
    case record h => simp [readDescription,RecordEntries,closed_fields_exact.mpr h]
    all_goals rfl

theorem sorted_fields_keep_exact_first_visible_entries (raw : List (Nat × Expr))
    (entry : Nat × Expr) : entry ∈ sortedFields raw ↔ entry ∈ normalize raw :=
  (List.mergeSort_perm ..).mem_iff

theorem sorted_labels_are_canonical (raw : List (Nat × Expr)) :
    ((sortedFields raw).map Prod.fst).Pairwise (· < ·) := by
  have order := List.pairwise_mergeSort (le := fun (a b : Nat × Expr) => decide (a.1 ≤ b.1))
    (fun _ _ _ first last => decide_eq_true (Nat.le_trans (of_decide_eq_true first)
      (of_decide_eq_true last)))
    (fun a b => by
      rcases Nat.le_total a.1 b.1 with h | h
      · simp [h]
      · simp [h]) (normalize raw)
  have listOrder : ((sortedFields raw).map Prod.fst).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact order.imp (fun hit => of_decide_eq_true hit)
  have noDuplicates : ((sortedFields raw).map Prod.fst).Nodup :=
    ((List.mergeSort_perm ..).map Prod.fst).nodup_iff.mpr (CommonRoleCanonicalRows.normalize_unique raw)
  exact listOrder.imp₂ (fun _ _ le ne => Nat.lt_of_le_of_ne le ne) noDuplicates

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
