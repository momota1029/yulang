import Yulang.GeneralDeclarativeReplayNames325
import Yulang.GeneralDeclarativeClauseOrigins325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeClauseTransport325
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeCongruence322 (Congruent)
open GeneralDeclarativeEqualities322 (Derives by_stored_alias)
open GeneralDeclarativeClauseOrigins325 (Origin normalized_order)
open GeneralDeclarativeNFEmit324 (Read)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralDeclarationPatterns (Pattern normalize)

def At (s : State) (name : Nat) (target : Expr) : Prop :=
  ∃ owner stored, Alias s name owner ∧ (⟨owner,stored⟩ : Equation) ∈ s.equations ∧ Congruent s stored target

theorem inferred {s : State} (proof : At s name e) : Derives s (.variable name) e := by
  obtain ⟨_,_,linked,row,congruent⟩ := proof
  exact by_stored_alias row linked congruent

theorem from_origin {s : State} (proof : Origin s name e) (refl : Congruent s e e) : At s name e := by
  obtain ⟨owner,aliases,row⟩ := proof
  exact ⟨owner,e,aliases,row,refl⟩

/-- This is the ordinary reused-name branch: both the target and any
subordinate stored term names can differ from the current source names.
Only constructorwise alias substitution is used, and all modes are
independently checked for compound where inputs. -/
theorem read_reused {s : State} {cl : Clause} {impl : Declaration} {names : Names}
    (compiled : translateMany r.constructors i (cl.arguments.map normalize) = some codes)
    (sons : ∀ (pos : Nat) p e, cl.arguments[pos]? = some p → codes[pos]? = some e → Compound p →
      At s (compound pos).lower (logical names.input .lower e) ∧
      At s (compound pos).center (logical names.input .actual e) ∧
      At s (compound pos).upper (logical names.input .upper e))
    (returns : ∀ eq ∈ cl.outputs, ∃ code,
      translate r.constructors i (normalize eq.rhs) = some code ∧
      (¬Direct impl eq → At s (useOutput impl names targets eq).target (logical names.input .actual code))) :
    Read s r i impl cl names compound targets := by
  refine ⟨⟨codes,normalized_order compiled,?_⟩,?_⟩
  · intro pos pat code p e h
    obtain ⟨lo,mid,hi⟩ := sons pos pat code p e h
    exact ⟨inferred lo,inferred mid,inferred hi⟩
  · intro eq asked
    obtain ⟨code,translated,needs⟩ := returns eq asked
    exact ⟨code,translated,fun use => inferred (needs use)⟩

end Yulang.GeneralDeclarativeClauseTransport325
