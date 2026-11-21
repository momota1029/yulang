import Yulang.GeneralDeclarativeNFEmit324
import Yulang.GeneralDeclarativeVisibleCode325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeClauseOrigins325
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeEqualities322 (Derives by_stored_alias)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeExistingClause322 (Refers)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeNFEmit324 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (All₂)

def Origin (s : State) (chosen : Nat) (e : Expr) : Prop :=
  ∃ ordinaryName, Alias s chosen ordinaryName ∧ (⟨ordinaryName,e⟩ : Equation) ∈ s.equations

theorem origin_reads {s : State} (ordinary : Origin s chosen e) :
    Derives s (.variable chosen) e := by
  obtain ⟨owner,also,stored⟩ := ordinary
  exact .trans (.congruent (.variable also)) (.row stored)

theorem origin_here {s : State} (actual : (⟨chosen,e⟩ : Equation) ∈ s.equations) :
    Origin s chosen e := ⟨chosen,alias_refl _,actual⟩

theorem shape_order (built : translateMany c i ps = some es) :
    All₂ (fun p e => translate c i p = some e) ps es := by
  induction ps generalizing es with
  | nil =>
    cases Option.some.inj built
    exact .nil
  | cons p rest ih =>
    cases hd : translate c i p with
    | none => simp [translateMany,hd] at built
    | some e =>
      cases tl : translateMany c i rest with
      | none => simp [translateMany,hd,tl] at built
      | some tail =>
        have eq : e :: tail = es := by simpa [translateMany,hd,tl] using built
        subst es
        exact .cons hd (ih tl)

theorem normalized_rel (proof : All₂ (fun p e => translate c i p = some e) (ps.map normalize) es) :
    All₂ (fun p e => translate c i (normalize p) = some e) ps es := by
  induction ps generalizing es with
  | nil => cases proof; exact .nil
  | cons p rest ih =>
    cases proof with
    | cons hd tl => exact .cons hd (ih tl)

theorem normalized_order (built : translateMany c i (ps.map normalize) = some es) :
    All₂ (fun p e => translate c i (normalize p) = some e) ps es :=
  normalized_rel (shape_order built)

/-- The three compound positions and the non-direct output are proven
from actual ordinary rows, whose owner may merely be aliased with the
source-chosen endpoint. Direct occurrences need no row at all. -/
theorem from_ordinary_rows {s : State} {cl : Clause} {names : Names} {impl : Declaration}
    (compiled : translateMany r.constructors i (cl.arguments.map normalize) = some codes)
    (compoundRows : ∀ (pos : Nat) (p : Pattern) (e : Expr),
      cl.arguments[pos]? = some p → codes[pos]? = some e → Compound p →
        Origin s (compound pos).lower (logical names.input .lower e) ∧
        Origin s (compound pos).center (logical names.input .actual e) ∧
        Origin s (compound pos).upper (logical names.input .upper e))
    (outRows : ∀ eq ∈ cl.outputs, ∃ e, translate r.constructors i (normalize eq.rhs) = some e ∧
      (¬Direct impl eq → Origin s (useOutput impl names targets eq).target (logical names.input .actual e))) :
    Read s r i impl cl names compound targets := by
  refine ⟨⟨codes,normalized_order compiled,?_⟩,?_⟩
  · intro pos p e member emitted nonDirect
    have witnesses := compoundRows pos p e member emitted nonDirect
    exact ⟨origin_reads witnesses.1,origin_reads witnesses.2.1,origin_reads witnesses.2.2⟩
  · intro eq used
    obtain ⟨e,built,found⟩ := outRows eq used
    exact ⟨e,built,fun needed => origin_reads (found needed)⟩

end Yulang.GeneralDeclarativeClauseOrigins325
