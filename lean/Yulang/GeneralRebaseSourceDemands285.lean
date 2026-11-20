import Yulang.GeneralNominalEffectSupport249

/-! Source-template demands before materializing typed leaves. Nominal
arguments use actual mode even under a lower/upper outer evaluation. -/
namespace Yulang.GeneralRebaseSourceDemands285
open GeneralNominalMaterialization (Mode)
open GeneralNominalRebaseEffectView243 (OldExpr compile compileMany)
open GeneralNominalEffectSupport249 (support supports)
open GeneralPresenceUsedSupport245 (typedReads)
open Core.PresenceGeneration (TyTerm)

abbrev Demand := Mode × Nat

mutual
 def demands (mode : Mode) : OldExpr → List Demand
 | .variable name => [(mode,name)]
 | .primitive _ args => demandsMany mode args
 | .nominal _ args => demandsMany .actual args
 | .record _ a b | .join a b => demands mode a ++ demands mode b
 | .variant _ a => demands mode a
 def demandsMany (mode : Mode) : List OldExpr → List Demand
 | [] => []
 | a :: as => demands mode a ++ demandsMany mode as
end

def expand (variables : Mode → Nat → TyTerm Nat) (d : Demand) : List Nat :=
 typedReads (variables d.1 d.2)

mutual
 theorem exact_support (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (e : OldExpr) :
     support (compile variables mode e) = (demands mode e).flatMap (expand variables) := by
  cases e with
  | «variable» => simp [support,compile,demands,expand]
  | primitive c args => exact exact_many variables mode args
  | nominal c args => exact exact_many variables .actual args
  | record l a b | join a b =>
    simp only [support,compile,demands,List.flatMap_append,exact_support variables mode a,
      exact_support variables mode b]
  | variant l a => exact exact_support variables mode a
 theorem exact_many (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (es : List OldExpr) :
     supports (compileMany variables mode es) = (demandsMany mode es).flatMap (expand variables) := by
  cases es with
  | nil => rfl
  | cons a as => simp only [supports,compileMany,demandsMany,List.flatMap_append,
      exact_support variables mode a,exact_many variables mode as]
end

theorem covered_iff (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (e : OldExpr)
    (watch : List Nat) : support (compile variables mode e) ⊆ watch ↔
      ∀ d ∈ demands mode e, expand variables d ⊆ watch := by
  rw [exact_support]
  constructor
  · intro all d hd n hn
    exact all (List.mem_flatMap.mpr ⟨d,hd,hn⟩)
  · intro every n hn
    obtain ⟨d,hd,read⟩ := List.mem_flatMap.mp hn
    exact every d hd read

end Yulang.GeneralRebaseSourceDemands285
