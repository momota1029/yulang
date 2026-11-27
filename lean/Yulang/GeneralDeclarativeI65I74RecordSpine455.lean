import Yulang.GeneralDeclarativeI65I74RecordEntry412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTrail455
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open RecordK2412 (header412 recordDescent412 closedWhere412)
open Checker408 (Problem)

def chain (empty : Nat) : List Nat → Pattern → Pattern
  | [], p => p
  | l :: ls, p => .record l (chain empty ls p) (.app empty [])

def queryChain : List Nat → Nat → Expr
  | [], b => .variable b
  | l :: ls, b => .record l (queryChain ls b) (.primitive .emptyRecord [])

def spine (empty : Nat) : Pattern → Option (List Nat × Nat)
  | .var b => some ([],b)
  | .record l child (.app tail []) =>
    if tail = empty then (spine empty child).map fun (ls,b) => (l::ls,b) else none
  | _ => none

theorem read_spine_sound455 (empty : Nat) (p : Pattern) {ls b}
    (read : spine empty p = some (ls,b)) : p = chain empty ls (.var b) := by
  cases p with
  | var x =>
    simp only [spine,Option.some.injEq,Prod.mk.injEq] at read
    obtain ⟨rfl,rfl⟩ := read
    rfl
  | record f child tail =>
    cases tail with
    | app e as =>
      cases as with
      | nil =>
        by_cases eEq : e = empty
        · subst e
          cases found : spine empty child with
          | none => simp [spine,found] at read
          | some pair =>
            obtain ⟨path,name⟩ := pair
            have eq : (f::path,name) = (ls,b) := by simpa [spine,found] using read
            cases eq
            rw [read_spine_sound455 empty child found]
            rfl
        · simp [spine,eEq] at read
      | cons x xs => simp [spine] at read
    | var => simp [spine] at read
    | record => simp [spine] at read
    | variant => simp [spine] at read
    | join => simp [spine] at read
  | app => simp [spine] at read
  | variant => simp [spine] at read
  | join => simp [spine] at read

theorem exact_spine_replays455 (empty b : Nat) (ls : List Nat) :
    spine empty (chain empty ls (.var b)) = some (ls,b) := by
  induction ls with
  | nil => rfl
  | cons f ls ih => simp [chain,spine,ih]

private theorem normalized_substitution_size (empty b : Nat) (ls : List Nat) (a : Nat → Pattern) :
    (normalize ((chain empty ls (.var b)).subst a)).encode.size =
      2 * ls.length + (normalize (a b)).encode.size := by
  induction ls with
  | nil => simp [chain,Pattern.subst]
  | cons f ls ih =>
    simp only [chain,Pattern.subst,substArgs,normalize,normalizeArgs,hide,Pattern.encode,
      encodeArgs,Roles.Term.size,Roles.argsSize,Nat.add_zero,List.length_cons,ih]
    omega

private theorem normalized_substitution_count (empty b x : Nat) (ls : List Nat) (a : Nat → Pattern) :
    (normalize ((chain empty ls (.var b)).subst a)).encode.occurrences x =
      (normalize (a b)).encode.occurrences x := by
  induction ls with
  | nil => rfl
  | cons f ls ih =>
    simp only [chain,Pattern.subst,substArgs,normalize,normalizeArgs,hide,Pattern.encode,
      encodeArgs,Roles.Term.occurrences,Roles.argsOccurrences,Nat.add_zero,ih]

theorem actual_closed_chain_where_prefix_strict455
    (empty b : Nat) (ls shorter : List Nat) (strict : shorter.length < ls.length) :
    StableSmaller [chain empty ls (.var b)] [chain empty shorter (.var b)] := by
  intro capture
  constructor
  · simp only [counted,substArgs,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero,
      normalized_substitution_size]
    omega
  · intro x
    simp only [counted,substArgs,normalizeArgs,encodeArgs,Roles.argsOccurrences,Nat.add_zero,
      normalized_substitution_count,Nat.le_refl]

theorem actual_closed_chain_translates_without_depth_bound455
    (cur : GeneralDeclarativeWitnessDeclaredState357.Current) (empty b : Nat) (ls : List Nat)
    (written : application (authoredRegistry cur).constructors
      (interpretation cur.environment.source.snapshot) empty [] = some (.primitive .emptyRecord [])) :
    translate (authoredRegistry cur).constructors (interpretation cur.environment.source.snapshot)
      (normalize (chain empty ls (.var b))) = some (queryChain ls b) := by
  induction ls with
  | nil => rfl
  | cons f ls ih =>
    simp [chain,queryChain,normalize,normalizeArgs,hide,translate,translateMany,ih,written]

end Yulang.GeneralDeclarativeI65.I72.RecordTrail455
