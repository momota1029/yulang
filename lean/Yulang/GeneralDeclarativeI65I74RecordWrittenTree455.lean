import Yulang.GeneralDeclarativeI65I74RecordHeader455
import Yulang.GeneralDeclarativeI65I74RecordPaterson455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTree455
open GeneralDeclarationPatterns

/-- Rooted record tails are a literal finite spine ending at the
authored empty constructor; a capture can never replace a tail. -/
inductive ClosedTail (empty : Nat) : Pattern → Prop where
  | closed : ClosedTail empty (.app empty [])
  | field : ClosedTail empty tail → ClosedTail empty (.record field payload tail)

def checkTail (empty : Nat) : Pattern → Bool
  | .app n [] => n == empty
  | .record _ _ tail => checkTail empty tail
  | _ => false

theorem checkTail_exact (empty : Nat) (p : Pattern) :
    checkTail empty p = true ↔ ClosedTail empty p := by
  constructor
  · intro accepted
    cases p with
    | app c args =>
      cases args with
      | nil =>
        have same : c = empty := by simpa [checkTail] using accepted
        subst c
        exact .closed
      | cons a as => simp [checkTail] at accepted
    | record l q tail =>
      exact .field ((checkTail_exact empty tail).mp (by simpa [checkTail] using accepted))
    | var => simp [checkTail] at accepted
    | variant => simp [checkTail] at accepted
    | join => simp [checkTail] at accepted
  · intro h
    induction h with
    | closed => simp [checkTail]
    | field _ ih => exact ih

theorem hide_keeps_the_closed_tail {empty : Nat} {tail : Pattern}
    (restProof : ClosedTail empty tail) (label : Nat) : ClosedTail empty (hide label tail) := by
  induction restProof with
  | closed => exact .closed
  | @field tail field payload _ ih =>
    by_cases same : label = field
    · simpa [hide,same] using ih
    · simpa [hide,same] using (ClosedTail.field (field := field) (payload := payload) ih)

theorem normalization_keeps_the_closed_tail {empty : Nat} {tail : Pattern}
    (restProof : ClosedTail empty tail) : ClosedTail empty (normalize tail) := by
  induction restProof with
  | closed => exact .closed
  | field _ ih => exact .field (hide_keeps_the_closed_tail ih _)

theorem hide_does_not_enter_captured_payloads {empty : Nat} {tail : Pattern}
    (restProof : ClosedTail empty tail) (label : Nat) (cap : Nat → Pattern) :
    hide label (tail.subst cap) = (hide label tail).subst cap := by
  induction restProof with
  | closed => rfl
  | @field tail field payload _ ih =>
    by_cases same : label = field
    · simpa [hide,Pattern.subst,same] using ih
    · simp [hide,Pattern.subst,same,ih]

mutual
  inductive Written (empty : Nat) : Pattern → Prop where
    | var : Written empty (.var n)
    | app : WrittenArgs empty args → Written empty (.app c args)
    | record : Written empty payload → Written empty tail → ClosedTail empty tail →
        Written empty (.record label payload tail)
    | variant : Written empty payload → Written empty (.variant tag payload)
  inductive WrittenArgs (empty : Nat) : List Pattern → Prop where
    | nil : WrittenArgs empty []
    | cons : Written empty head → WrittenArgs empty rest → WrittenArgs empty (head::rest)
end

mutual
  def checkTree (empty : Nat) : Pattern → Bool
    | .var _ => true
    | .app _ args => checkTrees empty args
    | .record _ payload tail => checkTree empty payload && checkTree empty tail && checkTail empty tail
    | .variant _ value => checkTree empty value
    | .join _ _ => false
  def checkTrees (empty : Nat) : List Pattern → Bool
    | [] => true
    | x :: xs => checkTree empty x && checkTrees empty xs
end

mutual
  theorem checkTree_exact (empty : Nat) (p : Pattern) :
      checkTree empty p = true ↔ Written empty p := by
    cases p with
    | var => exact ⟨fun _ => .var,fun _ => rfl⟩
    | app c args =>
      exact ⟨fun h => .app ((checkTrees_exact empty args).mp h),
        fun h => by cases h with | app keep => exact (checkTrees_exact empty args).mpr keep⟩
    | record l payload tail =>
      constructor
      · intro checked
        obtain ⟨here,tailOk⟩ := Bool.and_eq_true_iff.mp checked
        obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp here
        exact .record ((checkTree_exact empty payload).mp a) ((checkTree_exact empty tail).mp b)
          ((checkTail_exact empty tail).mp tailOk)
      · intro wanted
        cases wanted with
        | record a b c =>
          exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
            ⟨(checkTree_exact empty payload).mpr a,(checkTree_exact empty tail).mpr b⟩,
            (checkTail_exact empty tail).mpr c⟩
    | variant l p =>
      exact ⟨fun h => .variant ((checkTree_exact empty p).mp h),
        fun h => by cases h with | variant x => exact (checkTree_exact empty p).mpr x⟩
    | join a b =>
      constructor
      · intro h; cases h
      · intro h; cases h
  theorem checkTrees_exact (empty : Nat) (ps : List Pattern) :
      checkTrees empty ps = true ↔ WrittenArgs empty ps := by
    cases ps with
    | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
    | cons a as =>
      constructor
      · intro checked
        obtain ⟨first,last⟩ := Bool.and_eq_true_iff.mp checked
        exact .cons ((checkTree_exact empty a).mp first) ((checkTrees_exact empty as).mp last)
      · intro matched
        cases matched with
        | cons first last =>
          exact Bool.and_eq_true_iff.mpr
            ⟨(checkTree_exact empty a).mpr first,(checkTrees_exact empty as).mpr last⟩
end

mutual
  theorem normalize_subst_exact_for_written_trees
      {empty : Nat} {p : Pattern} (written : Written empty p) (cap : Nat → Pattern) :
      normalize (p.subst cap) = (normalize p).subst (fun b => normalize (cap b)) := by
    cases written with
    | var => rfl
    | app args =>
      simp only [Pattern.subst,normalize,normalize_subst_exact_for_written_args args cap]
    | record payload tail closes =>
      simp only [Pattern.subst,normalize,normalize_subst_exact_for_written_trees payload cap,
        normalize_subst_exact_for_written_trees tail cap,
        hide_does_not_enter_captured_payloads (normalization_keeps_the_closed_tail closes)]
    | variant payload =>
      simp only [Pattern.subst,normalize,normalize_subst_exact_for_written_trees payload cap]
  theorem normalize_subst_exact_for_written_args
      {empty : Nat} {ps : List Pattern} (written : WrittenArgs empty ps) (cap : Nat → Pattern) :
      normalizeArgs (substArgs cap ps) = substArgs (fun b => normalize (cap b)) (normalizeArgs ps) := by
    cases written with
    | nil => rfl
    | cons first last =>
      simp only [substArgs,normalizeArgs,normalize_subst_exact_for_written_trees first cap,
        normalize_subst_exact_for_written_args last cap]
end

mutual
  theorem encode_after_subst (p : Pattern) (cap : Nat → Pattern) :
      (p.subst cap).encode = Roles.Term.subst (fun b => (cap b).encode) p.encode := by
    cases p with
    | var => rfl
    | app c args => simp [Pattern.subst,Pattern.encode,Roles.Term.subst,encode_args_after_subst args cap]
    | record l p t =>
      simp [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,
        encode_after_subst p cap,encode_after_subst t cap]
    | variant l p =>
      simp [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,
        encode_after_subst p cap]
    | join p t =>
      simp [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,
        encode_after_subst p cap,encode_after_subst t cap]
  theorem encode_args_after_subst (ps : List Pattern) (cap : Nat → Pattern) :
      encodeArgs (substArgs cap ps) = Roles.substArgs (fun b => (cap b).encode) (encodeArgs ps) := by
    cases ps with
    | nil => rfl
    | cons a as =>
      simp [substArgs,encodeArgs,Roles.substArgs,encode_after_subst a cap,encode_args_after_subst as cap]
end

theorem counted_authored_tree_subst_is_term_subst {empty : Nat} {ps : List Pattern}
    (written : WrittenArgs empty ps) (cap : Nat → Pattern) :
    counted (substArgs cap ps) =
      Roles.substArgs (fun b => (normalize (cap b)).encode) (counted ps) := by
  unfold counted
  rw [normalize_subst_exact_for_written_args written cap,encode_args_after_subst]

theorem written_tree_paterson_stable_under_all_captures455
    {empty : Nat} {head child : List Pattern}
    (h : WrittenArgs empty head) (c : WrittenArgs empty child) (sm : Smaller head child) :
    StableSmaller head child :=
  RecordPaterson455.stable_from_counted_substitution455
    (counted_authored_tree_subst_is_term_subst h)
    (counted_authored_tree_subst_is_term_subst c) sm

end Yulang.GeneralDeclarativeI65.I72.RecordTree455
