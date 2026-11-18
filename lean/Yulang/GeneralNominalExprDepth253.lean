import Yulang.GeneralNominalRebaseEffectView243
namespace Yulang.GeneralNominalExprDepth253
open Core.PresenceGeneration (TyTerm)
open GeneralNominalMaterialization (Mode)
abbrev Raw := GeneralNominalCenteredHeadMatExpressions.Expr
abbrev Materialized := GeneralNominalRebaseEffectView243.Expr

/-- Type-constructor depth. Row syntax is a separate sort. -/
def typeDepth : TyTerm Nat → Nat
 | .var _ => 0
 | .union first last | .inter first last | .pair first last | .record _ first last | .recordDefault _ first last =>
   1 + max (typeDepth first) (typeDepth last)
 | .required _ term | .variant _ term => 1 + typeDepth term
 | .arrow first _ last _ => 1 + max (typeDepth first) (typeDepth last)
 | _ => 1

mutual
 def rawDepth : Raw → Nat
 | .variable _ => 0
 | .primitive _ args | .nominal _ args => 1 + rawDepths args
 | .record _ first last | .join first last => 1 + max (rawDepth first) (rawDepth last)
 | .variant _ term => 1 + rawDepth term
 def rawDepths : List Raw → Nat
 | [] => 0
 | first :: rest => max (rawDepth first) (rawDepths rest)
end

mutual
 def materializedDepth : Materialized → Nat
 | .source term => typeDepth term
 | .primitive _ args | .nominal _ args => 1 + materializedDepths args
 | .record _ first last | .join first last => 1 + max (materializedDepth first) (materializedDepth last)
 | .variant _ term => 1 + materializedDepth term
 def materializedDepths : List Materialized → Nat
 | [] => 0
 | first :: rest => max (materializedDepth first) (materializedDepths rest)
end

mutual
 theorem compile_depth (variables : Mode → Nat → TyTerm Nat) (bound : Nat)
 (bounded : ∀ mode name, typeDepth (variables mode name) ≤ bound) (mode : Mode) (term : Raw) :
 materializedDepth (GeneralNominalRebaseEffectView243.compile variables mode term) ≤ rawDepth term + bound := by
 cases term with
 | «variable» name => simpa only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,Nat.zero_add] using bounded mode name
 | primitive constructor args =>
   have result := compile_depths variables bound bounded mode args
   simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth]
   omega
 | nominal name args =>
   have result := compile_depths variables bound bounded .actual args
   simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth]
   omega
 | record label first last =>
   have one := compile_depth variables bound bounded mode first
   have two := compile_depth variables bound bounded mode last
   simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth]
   omega
 | variant tag term =>
   have result := compile_depth variables bound bounded mode term
   simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth]
   omega
 | join first last =>
   have one := compile_depth variables bound bounded mode first
   have two := compile_depth variables bound bounded mode last
   simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth]
   omega
 theorem compile_depths (variables : Mode → Nat → TyTerm Nat) (bound : Nat)
 (bounded : ∀ mode name, typeDepth (variables mode name) ≤ bound) (mode : Mode) (terms : List Raw) :
 materializedDepths (GeneralNominalRebaseEffectView243.compileMany variables mode terms) ≤ rawDepths terms + bound := by
 cases terms with
 | nil => exact Nat.zero_le _
 | cons first rest =>
   have one := compile_depth variables bound bounded mode first
   have two := compile_depths variables bound bounded mode rest
   simp only [GeneralNominalRebaseEffectView243.compileMany,materializedDepths,rawDepths]
   omega
end

mutual
 theorem reference_depth (names : Mode → Nat → Nat) (mode : Mode) (term : Raw) :
 materializedDepth (GeneralNominalRebaseEffectView243.compile (fun mode name => .var (names mode name)) mode term) = rawDepth term := by
 cases term with
 | «variable» => rfl
 | primitive => simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,reference_depths]
 | nominal => simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,reference_depths]
 | record => simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,reference_depth]
 | variant => simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,reference_depth]
 | join => simp only [GeneralNominalRebaseEffectView243.compile,materializedDepth,rawDepth,reference_depth]
 theorem reference_depths (names : Mode → Nat → Nat) (mode : Mode) (terms : List Raw) :
 materializedDepths (GeneralNominalRebaseEffectView243.compileMany (fun mode name => .var (names mode name)) mode terms) = rawDepths terms := by
 cases terms with
 | nil => rfl
 | cons => simp only [GeneralNominalRebaseEffectView243.compileMany,materializedDepths,rawDepths,reference_depth,reference_depths]
end
end Yulang.GeneralNominalExprDepth253
