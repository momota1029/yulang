import Yulang.GeneralDeclarativeI65I74FiniteRawAliasClass472
import Yulang.GeneralDeclarativeI65I74RawObservationTable471
import Yulang.GeneralDeclarativeCongruence322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_symm)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeCongruence322 (Congruent Arguments)
open GeneralDeclarativeNestedRun332 (tagId tagId_exact)
open ObservationRawAlias471 (ClassWire checkWholeClass checked_class_is_exact_for_every_name connectedKeys)
open ObservationSyntax471 (isDefinedAt)
private abbrev Raw := GeneralDeclarativeHead320.State

abbrev Catalogue := List (Nat × ClassWire)

def checkedAlias (s : Raw) (known : Catalogue) (u v : Nat) : Bool :=
  (u == v) || known.any fun entry =>
    (entry.1 == u) && checkWholeClass s u entry.2 && decide (v ∈ connectedKeys entry.2)

theorem checked_alias_really_links_old_names {s known u v}
    (ok : checkedAlias s known u v = true) : GeneralDeclarativeLowerKnown321.Alias s u v := by
  rcases Bool.or_eq_true_iff.mp ok with same | found
  · obtain rfl := beq_iff_eq.mp same
    exact alias_refl _
  · obtain ⟨⟨name,w⟩,_,pass⟩ := List.any_eq_true.mp found
    have data : ((name == u) && checkWholeClass s u w) = true ∧
        decide (v ∈ connectedKeys w) = true := Bool.and_eq_true_iff.mp pass
    exact (checked_class_is_exact_for_every_name (Bool.and_eq_true_iff.mp data.1).2 v).mp
      (of_decide_eq_true data.2)

mutual
def checksShape (s : Raw) (known : Catalogue) : Expr → Expr → Bool
  | .variable a,.variable b => checkedAlias s known a b
  | .primitive f xs,.primitive g ys =>
      (tagId f == tagId g) && checksShapes s known xs ys
  | .nominal f xs,.nominal g ys =>
      (f == g) && checksShapes s known xs ys
  | .record l a tail,.record r b rest =>
      (l == r) && checksShape s known a b && checksShape s known tail rest
  | .variant l a,.variant r b => (l == r) && checksShape s known a b
  | .join a b,.join c d => checksShape s known a c && checksShape s known b d
  | _,_ => false
termination_by structural first => first

def checksShapes (s : Raw) (known : Catalogue) : List Expr → List Expr → Bool
  | [],[] => true
  | a::as,b::bs => checksShape s known a b && checksShapes s known as bs
  | _,_ => false
termination_by structural first => first
end

mutual
theorem checks_shape_is_literal_old_alias_congruence
    (a b : Expr) (ok : checksShape s known a b = true) : Congruent s a b := by
  cases a <;> cases b <;> try cases ok
  case «variable».«variable» =>
    exact .variable (checked_alias_really_links_old_names ok)
  case primitive.primitive f xs g ys =>
    obtain ⟨same,more⟩ := Bool.and_eq_true_iff.mp ok
    obtain rfl := tagId_exact (beq_iff_eq.mp same)
    exact .primitive (checks_shapes_are_literal_old_alias_congruence xs ys more)
  case nominal.nominal f xs g ys =>
    obtain ⟨same,more⟩ := Bool.and_eq_true_iff.mp ok
    obtain rfl := beq_iff_eq.mp same
    exact .nominal (checks_shapes_are_literal_old_alias_congruence xs ys more)
  case record.record l a tail r b rest =>
    obtain ⟨main,rl⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨same,payload⟩ := Bool.and_eq_true_iff.mp main
    obtain rfl := beq_iff_eq.mp same
    exact .record (checks_shape_is_literal_old_alias_congruence a b payload)
      (checks_shape_is_literal_old_alias_congruence tail rest rl)
  case variant.variant l a r b =>
    obtain ⟨same,data⟩ := Bool.and_eq_true_iff.mp ok
    obtain rfl := beq_iff_eq.mp same
    exact .variant (checks_shape_is_literal_old_alias_congruence a b data)
  case join.join a b c d =>
    obtain ⟨first,second⟩ := Bool.and_eq_true_iff.mp ok
    exact .join (checks_shape_is_literal_old_alias_congruence a c first)
      (checks_shape_is_literal_old_alias_congruence b d second)
termination_by structural a

theorem checks_shapes_are_literal_old_alias_congruence
    (xs ys : List Expr) (ok : checksShapes s known xs ys = true) : Arguments s xs ys := by
  cases xs <;> cases ys <;> try cases ok
  case nil.nil => exact .nil
  case cons.cons a as b bs =>
    obtain ⟨here,later⟩ := Bool.and_eq_true_iff.mp ok
    exact .cons (checks_shape_is_literal_old_alias_congruence a b here)
      (checks_shapes_are_literal_old_alias_congruence as bs later)
termination_by structural xs
end

def allDefinitions (s : Raw) (w : ClassWire) : List Equation :=
  s.equations.filter fun e => decide (e.left ∈ connectedKeys w) && isDefinedAt e.left e

structure ExactOwner (s : Raw) (name ordinal : Nat) where
  row : Equation
  literal : s.equations[ordinal]? = some row
  linked : GeneralDeclarativeLowerKnown321.Alias s name row.left
  constructorRow : isDefinedAt row.left row = true
  allOld : ∀ other ∈ s.equations, GeneralDeclarativeLowerKnown321.Alias s name other.left →
    isDefinedAt other.left other = true → Congruent s row.right other.right

/-- Use an existing equation at an explicit physical ordinal. Every
constructor definition of the entire old alias class must agree up to
literal constructor structure and verified alias leaves; otherwise this
restricted observer has no answer. It does not choose a winner. -/
def readExactOwner (s : Raw) (known : Catalogue) (name ordinal : Nat) (w : ClassWire) :
    Option (ExactOwner s name ordinal) :=
  match preserved : s.equations[ordinal]? with
  | none => none
  | some row =>
    if yes : checkWholeClass s name w = true ∧ row.left ∈ connectedKeys w ∧
        isDefinedAt row.left row = true ∧
        (allDefinitions s w).all (fun other => checksShape s known row.right other.right) = true then
      have members := checked_class_is_exact_for_every_name yes.1
      some ⟨row,preserved,(members _).mp yes.2.1,yes.2.2.1,by
        intro other mem link definition
        have actual : other ∈ allDefinitions s w := List.mem_filter.mpr
          ⟨mem,Bool.and_eq_true_iff.mpr ⟨decide_eq_true ((members _).mpr link),definition⟩⟩
        exact checks_shape_is_literal_old_alias_congruence _ _ (List.all_eq_true.mp yes.2.2.2 _ actual)⟩
    else none

theorem every_same_ordinary_fit_interprets_that_actual_owner_at_the_named_point
    {s name ordinal} (proof : ExactOwner s name ordinal) (m : GeneralNominalCommonBridge.Assignment)
    (fit : GeneralDeclarativeHead320.Models s m) :
    CommonNominalFullCarrier.Equivalent (m name).1
      (value (GeneralDeclarativeHead320.environment m) .actual proof.row.right) :=
  GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans
    (GeneralDeclarativeAliasMeaning321.alias_sound proof.linked m fit)
    (fit.2 _ (List.mem_of_getElem? proof.literal))

end Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472
