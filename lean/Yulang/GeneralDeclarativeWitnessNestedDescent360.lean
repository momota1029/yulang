import Yulang.GeneralDeclarativeWitnessCovariantDescent353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNestedDescent360
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessChecks349 (ids binds lexical names counts)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def wrap (keys : List Nat) (tail : Pattern) : Pattern :=
  match keys with
  | [] => tail
  | first::rest => .app first [wrap rest tail]

private theorem wrapped_size (keys : List Nat) (capture : Nat → Pattern) (binder : Nat) :
    (normalize ((wrap keys (.var binder)).subst capture)).encode.size =
      keys.length + (normalize (capture binder)).encode.size := by
  induction keys with
  | nil => simp [wrap,Pattern.subst]
  | cons key rest ih =>
    simp only [wrap,Pattern.subst,substArgs,normalize,normalizeArgs,Pattern.encode,encodeArgs,
      Roles.Term.size,Roles.argsSize,Nat.add_zero,List.length_cons,ih]
    omega

private theorem wrapped_count (keys : List Nat) (capture : Nat → Pattern) (binder name : Nat) :
    (normalize ((wrap keys (.var binder)).subst capture)).encode.occurrences name =
      (normalize (capture binder)).encode.occurrences name := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [wrap,Pattern.subst,substArgs,normalize,normalizeArgs,Pattern.encode,encodeArgs,
      Roles.Term.occurrences,Roles.argsOccurrences,Nat.add_zero,ih]

private theorem counted_member (capture : Nat → Pattern) {p : Pattern} {ps : List Pattern}
    (inHead : p ∈ ps) : (normalize (p.subst capture)).encode ∈ counted (substArgs capture ps) := by
  induction ps with
  | nil => cases inHead
  | cons first rest ih =>
    rcases List.mem_cons.mp inHead with rfl|mem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih mem)

private theorem size_has {t : Roles.Term} {xs : List Roles.Term} (h : t ∈ xs) :
    t.size ≤ Roles.argsSize xs := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    change t.size ≤ x.size + Roles.argsSize rest
    rcases List.mem_cons.mp h with rfl|mem
    · omega
    · have hi := ih mem
      omega

private theorem count_has {t : Roles.Term} {xs : List Roles.Term} (h : t ∈ xs) (v : Nat) :
    t.occurrences v ≤ Roles.argsOccurrences v xs := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    change t.occurrences v ≤ x.occurrences v + Roles.argsOccurrences v rest
    rcases List.mem_cons.mp h with rfl|mem
    · omega
    · have hi := ih mem
      omega

/-- One actually written unary constructor path to a binder suffices,
even with arbitrary other head arguments. The full written path stays
under normalization of arbitrary captures. -/
theorem visible_chain_stays_smaller {head : List Pattern} {keys : List Nat} {binder : Nat}
    (wrapped : wrap keys (.var binder) ∈ head) (nonempty : keys ≠ []) :
    StableSmaller head [.var binder] := by
  intro capture
  have evidence := counted_member capture wrapped
  have size := size_has evidence
  have width := wrapped_size keys capture binder
  have pos : 0 < keys.length := by cases keys <;> simp_all
  constructor
  · have exact : Roles.argsSize (counted (substArgs capture [.var binder])) =
        (normalize (capture binder)).encode.size := by
      simp [counted,substArgs,Pattern.subst,normalizeArgs,encodeArgs,Roles.argsSize]
    rw [exact]
    omega
  · intro v
    have h := count_has evidence v
    rw [wrapped_count] at h
    simpa [counted,substArgs,Pattern.subst,normalizeArgs,encodeArgs,Roles.argsOccurrences] using h

def origin : Nat → Pattern → Option (List Nat × Nat)
  | 0,_ => none
  | _fuel+1,.var b => some ([],b)
  | fuel+1,.app key [rest] => (origin fuel rest).map fun hit => (key::hit.1,hit.2)
  | _,_ => none

theorem origin_exact (fuel : Nat) (p : Pattern) {keys binder} (read : origin fuel p = some (keys,binder)) :
    p = wrap keys (.var binder) := by
  induction fuel generalizing p keys binder with
  | zero => cases read
  | succ fuel ih =>
    cases p with
    | var name =>
      have pair : (([] : List Nat),name) = (keys,binder) := by simpa [origin] using read
      cases pair
      rfl
    | app name args =>
      cases args with
      | nil => simp [origin] at read
      | cons head rest =>
        cases rest with
        | cons h t => simp [origin] at read
        | nil =>
          cases q : origin fuel head with
          | none => simp [origin,q] at read
          | some answer =>
            obtain ⟨ks,b⟩ := answer
            have eq : (name::ks,b) = (keys,binder) := by simpa [origin,q] using read
            cases eq
            rw [ih head q]
            rfl
    | record => simp [origin] at read
    | variant => simp [origin] at read
    | join => simp [origin] at read

def actualOrigin (p : Pattern) := origin (p.encode.size + 1) p

def fromChain (head child : List Pattern) : Bool :=
  match child with
  | [.var binder] => head.any fun h =>
      ((actualOrigin h).map fun r => decide (r.1 ≠ [] ∧ r.2 = binder)).getD false
  | _ => false

theorem from_chain_sound {head child} (successful : fromChain head child = true) : StableSmaller head child := by
  unfold fromChain at successful
  split at successful
  · rename_i binder
    obtain ⟨p,actual,computed⟩ := List.any_eq_true.mp successful
    cases d : actualOrigin p with
    | none => simp [d] at computed
    | some pair =>
      rcases pair with ⟨keys,b⟩
      have valid : keys ≠ [] ∧ b = binder := of_decide_eq_true (by simpa [d] using computed)
      have form := origin_exact _ p d
      have same := valid.2
      subst b
      exact visible_chain_stays_smaller (form ▸ actual) valid.1
  · cases successful

def descent (head child : List Pattern) : Bool :=
  (counts head child && checkSmaller head child) &&
  (CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0,counted child⟩ && fromChain head child)

theorem descent_witness {head child} (ok : descent head child = true) :
    CountsCovered head child ∧ Smaller head child ∧ ConservativeSmaller head child ∧ StableSmaller head child := by
  obtain ⟨a,b⟩ := splitAnd ok
  exact ⟨splitAnd (splitAnd a).1,(checkSmaller_exact ..).mp (splitAnd a).2,
    (splitAnd b).1,from_chain_sound (splitAnd b).2⟩

def check (s : GeneralSourceMetadataBundle291.SourceBundle) (d : Declaration) : Bool :=
  (GeneralDeclarativeWitnessSignature349.checks s.roles d && ids d) &&
    ((binds d && lexical d) && (names d && d.requirements.all (fun c => descent d.head c.arguments)))

theorem checked_descent {s d} (ok : check s d = true) :
    ∀ c ∈ d.requirements, StableSmaller d.head c.arguments := by
  intro c member
  exact (descent_witness (List.all_eq_true.mp (splitAnd (splitAnd (splitAnd ok).2).2).2 c member)).2.2.2

end Yulang.GeneralDeclarativeWitnessNestedDescent360
