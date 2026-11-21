import Yulang.GeneralDeclarativeHeadDetermines320
import Yulang.GeneralDeclarativeAssembly320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeDefaultScope320
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarationPatterns (normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDemand320 (Demand sourceValue)
open GeneralDeclarativeOutputs320 (termPattern termPatterns positional)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeHeadDetermines320 (pattern_congruent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonRoleOutermostResolver (All₂)

mutual
 theorem term_uses (t : Roles.Term) {id : Nat} (used : id ∈ (termPattern t).variables) :
    id < t.bound := by
  cases t with
  | var n =>
    cases List.mem_singleton.mp used
    exact Nat.lt_succ_self _
  | app key args => exact terms_use args used
 termination_by sizeOf t
 theorem terms_use (ts : List Roles.Term) {id : Nat} (used : id ∈ variablesArgs (termPatterns ts)) :
    id < Roles.argsBound ts := by
  cases ts with
  | nil => cases used
  | cons first rest =>
    rcases List.mem_append.mp used with h|h
    · exact Nat.lt_of_lt_of_le (term_uses first h) (Nat.le_max_left ..)
    · exact Nat.lt_of_lt_of_le (terms_use rest h) (Nat.le_max_right ..)
 termination_by sizeOf ts
end

mutual
 theorem normal_term (t : Roles.Term) : normalize (termPattern t) = termPattern t := by
  cases t with
  | var => rfl
  | app key args => simp only [termPattern,normalize,normal_terms args]
 termination_by sizeOf t
 theorem normal_terms (ts : List Roles.Term) : normalizeArgs (termPatterns ts) = termPatterns ts := by
  cases ts with
  | nil => rfl
  | cons first rest => simp only [termPatterns,normalizeArgs,normal_term first,normal_terms rest]
 termination_by sizeOf ts
end

def withFallback (fallback : Nat) (d : Demand) (i : Nat) : Capture :=
  let center := (d.arguments[i]?.map Capture.center).getD fallback
  ⟨center,center,center⟩

theorem inside_arity (d : Demand) (fallback : Nat) {i : Nat} (present : i < d.arguments.length) :
    withFallback fallback d i = positional d i := by
  simp only [withFallback,positional,List.getElem?_eq_getElem present,Option.map_some,Option.getD_some]

theorem ordered_length {p : α → β → Prop} {xs : List α} {ys : List β} (relation : All₂ p xs ys) :
    xs.length = ys.length := by
  induction relation with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- A checked positional role default reads only real demand centers.
Its meaning is independent of the filler for an out-of-arity position,
not merely of the arbitrary filler chosen in one implementation. -/
theorem default_never_falls_back {r : Registry} {interp : Interpretation} {m : Assignment}
    {d : Demand} {decl : Declaration} {capture : Nat → Capture} {kids : List Demand}
    (checked : Checked r) (meaning : Meaning r interp m d decl capture kids)
    {output : Nat} {rhs : Roles.Term}
    (given : (r.roles decl.role).assoc output = some (some rhs)) (fallback : Nat) :
    Equivalent (sourceValue r.constructors interp (withFallback fallback d) m (termPattern rhs))
      (sourceValue r.constructors interp (positional d) m (termPattern rhs)) := by
  have scope := (r.roles decl.role).defaultsScoped output rhs given
  have arity := (ordered_length meaning.head).trans (checked.2 decl meaning.visible).signature.1
  apply pattern_congruent
  intro name used
  rw [normal_term] at used
  have within : name < d.arguments.length := by
    rw [arity]
    exact Nat.lt_of_lt_of_le (term_uses rhs used) scope
  change Equivalent (m (withFallback fallback d name).center).1 (m (positional d name).center).1
  rw [show withFallback fallback d name = positional d name from inside_arity d fallback within]
  exact eqv_refl _

end Yulang.GeneralDeclarativeDefaultScope320
