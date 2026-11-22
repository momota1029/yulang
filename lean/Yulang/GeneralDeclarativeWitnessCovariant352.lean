import Yulang.CommonDeclaredNominalInspection
import Yulang.GeneralDeclarativeWitnessTagHeader352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariant352
open CommonDeclaredNominalInspection (Registry Parameter inspect DeclaredSubtype inspect_exact)
open CommonDeclaredNominalVariance (Allowed)
open CommonNominalConstraints (HeadTerm ArgumentTerm Satisfied)
open CommonNominalHeads (Accept Demand)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralCandidateInspection (plainNames)

structure Arm (α : Type) where
  tag : Nat
  head : HeadTerm α

def unary (nominal : Nat) (term : TyTerm α) : HeadTerm α := ⟨nominal,[.value term]⟩

theorem unary_exact {α : Type} (head : HeadTerm α) {term : TyTerm α}
    (h : head.arguments = [.value term]) : head = unary head.name term := by
  cases head with
  | mk name args =>
    change args = [.value term] at h
    cases h
    rfl

def covariant : List Parameter := [⟨.value,.covariant⟩]

structure Plan (r : Registry) (tag : Nat) (first last : Arm α) where
  box : Nat
  left : TyTerm α
  right : TyTerm α
  firstTag : first.tag = tag
  lastTag : last.tag = tag
  leftHead : first.head = unary box left
  rightHead : last.head = unary box right
  variance : r[box]? = some covariant

/-- The fixed declaration must actually say covariant with exactly one
value parameter. There is no fallback via invariant nominal syntax. -/
def merge (r : Registry) (tag : Nat) (l h : Arm α) : Option (Plan r tag l h) :=
  if tagL : l.tag = tag then
    if tagH : h.tag = tag then
      if sameName : l.head.name = h.head.name then
        match first : l.head.arguments, last : h.head.arguments with
        | [.value a],[.value b] =>
          if declared : r[l.head.name]? = some covariant then some
            ⟨l.head.name,a,b,tagL,tagH,
              unary_exact l.head first,
              (unary_exact h.head last).trans (congrArg (fun name => unary name b) sameName.symm),declared⟩
          else none
        | _,_ => none
      else none
    else none
  else none

def Plan.payload {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) : TyTerm α :=
  .union p.left p.right

def Plan.merged {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) : HeadTerm α :=
  unary p.box p.payload

theorem projection {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h)
    (m : α → Comp Common.model) (qry : Demand) (known : Allowed [.covariant] qry) :
    Accept (p.merged.eval m) qry ↔ Accept (l.head.eval m) qry ∧ Accept (h.head.eval m) qry := by
  rw [p.leftHead,p.rightHead]
  exact CommonDeclaredNominalVariance.covariant_box_union_grouping p.box
    (p.left.eval Common.model m) (p.right.eval Common.model m) qry known

theorem compiler_left {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) :
    inspect r l.head p.merged = some [.tyLe p.left p.payload] := by
  rw [p.leftHead]
  simp [inspect,Plan.merged,covariant,unary,p.variance,CommonDeclaredNominalInspection.inspectArguments,
    CommonDeclaredNominalInspection.inspectArgument,CommonDeclaredNominalInspection.termKind,
    CommonDeclaredNominalInspection.directions,CommonNominalConstraints.append]

theorem compiler_right {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) :
    inspect r h.head p.merged = some [.tyLe p.right p.payload] := by
  rw [p.rightHead]
  simp [inspect,Plan.merged,covariant,unary,p.variance,CommonDeclaredNominalInspection.inspectArguments,
    CommonDeclaredNominalInspection.inspectArgument,CommonDeclaredNominalInspection.termKind,
    CommonDeclaredNominalInspection.directions,CommonNominalConstraints.append]

/-- Every actual occurrence captures the entire merged term. A request to
substitute only one arm cannot be mistaken for one of the produced bindings. -/
structure Bindings (p : Pattern) (tag box : Nat) where
  payloadPattern : Pattern
  names : List Nat
  printed : normalize p = .variant tag (.app box [payloadPattern])
  captured : plainNames payloadPattern = some names

def matchBindings (p : Pattern) (tag box : Nat) : Option (Bindings p tag box) :=
  match actual : normalize p with
  | .variant given (.app nominal [inside]) =>
    if sameTag : given = tag then
      if sameNominal : nominal = box then
        match found : plainNames inside with
        | none => none
        | some names => some ⟨inside,names,by simpa only [sameTag,sameNominal] using actual,found⟩
      else none
    else none
  | _ => none

def bind {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) {pat : Pattern}
    (b : Bindings pat tag p.box) : List (Nat × TyTerm α) :=
  b.names.map fun name => (name,p.payload)

theorem actual_capture {r : Registry} {tag : Nat} {l h : Arm α} (p : Plan r tag l h) {pat : Pattern}
    (b : Bindings pat tag p.box) (m : α → Comp Common.model) :
    ∀ x ∈ bind p b, x.2.eval Common.model m =
      .union (p.left.eval Common.model m) (p.right.eval Common.model m) := by
  intro x found
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp found
  rfl

def witnessed (r : Registry) (authored : List (Arm α)) (first last tag : Nat) (pat : Pattern) :
    Option (List (Nat × TyTerm α)) := do
  let a ← authored[first]?
  let b ← authored[last]?
  let joined ← merge r tag a b
  let captures ← matchBindings pat tag joined.box
  pure (bind joined captures)

end Yulang.GeneralDeclarativeWitnessCovariant352
