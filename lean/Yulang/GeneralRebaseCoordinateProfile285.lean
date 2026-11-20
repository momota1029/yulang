import Yulang.GeneralRebaseBodyReads285
import Yulang.GeneralRebaseFiniteRowReads285

/-! A profile can be calculated from source demand leaves and substituted
coordinates. Preserve row-only reads without manufacturing typed reads. -/
namespace Yulang.GeneralRebaseCoordinateProfile285
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralNominalMaterialization (Mode)
open GeneralNominalRebaseEffectView243 (OldExpr Equation body compile compileMany eval bodyVariables)
open GeneralNominalEffectSupport249 (support equationReads)
open GeneralRebaseFiniteRowReads285 (effects effectsMany equationRows)
open GeneralRebaseSourceDemands285 (demands demandsMany)
open GeneralPresenceUsedSupport245 (typedReads rowReads)
open GeneralNominalCenters (Plan)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralNominalCommonBridge (Assignment)

structure Profile where
 types : List Nat
 rows : List Nat
 deriving DecidableEq, Repr

def Profile.agrees (profile : Profile) (a b : Assignment) : Prop :=
 (∀ n ∈ profile.types, (a n).1 = (b n).1) ∧ (∀ n ∈ profile.rows, (a n).2 = (b n).2)

mutual
 theorem rows_exact (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (e : OldExpr) :
     effects (compile variables mode e) =
      (demands mode e).flatMap (fun d => rowReads (variables d.1 d.2)) := by
  cases e with
  | «variable» => simp [effects,compile,demands]
  | primitive c args => exact rows_many variables mode args
  | nominal c args => exact rows_many variables .actual args
  | record l a b | join a b => simp only [effects,compile,demands,List.flatMap_append,
      rows_exact variables mode a,rows_exact variables mode b]
  | variant l a => exact rows_exact variables mode a
 theorem rows_many (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (es : List OldExpr) :
     effectsMany (compileMany variables mode es) =
       (demandsMany mode es).flatMap (fun d => rowReads (variables d.1 d.2)) := by
  cases es with
  | nil => rfl
  | cons a as => simp only [effectsMany,compileMany,demandsMany,List.flatMap_append,
      rows_exact variables mode a,rows_many variables mode as]
end

def ofExpr (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (e : OldExpr) : Profile :=
  ⟨(demands mode e).flatMap (GeneralRebaseSourceDemands285.expand variables),
   (demands mode e).flatMap (fun d => rowReads (variables d.1 d.2))⟩

def Profile.prepend (target : TyTerm Nat) (p : Profile) : Profile :=
  ⟨typedReads target ++ p.types,rowReads target ++ p.rows⟩

def ofBody (p : Plan roles) (mapping : Nat → CompTerm Nat) (src : Body) : Option Profile :=
  (compileBody p src).map (ofExpr (bodyVariables p mapping src) .actual)

def ofEquation (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (src : Body) :
    Option Profile := (ofBody p mapping src).map (Profile.prepend (mapping target).1)

theorem ofBody_types (p : Plan roles) (mapping : Nat → CompTerm Nat) (src : Body) :
    (ofBody p mapping src).map Profile.types = GeneralRebaseBodyReads285.program p mapping src := by
  cases found : compileBody p src <;> simp [ofBody,GeneralRebaseBodyReads285.program,found,ofExpr]

theorem ofEquation_exact (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (src : Body) :
    ofEquation p mapping target src = (body p mapping target src).map
      (fun e => ⟨equationReads e,equationRows e⟩) := by
  cases found : compileBody p src
  · simp [ofEquation,ofBody,body,found]
  · simp only [ofEquation,ofBody,body,found,Option.map_some,Profile.prepend,ofExpr,
      equationReads,equationRows,GeneralRebaseSourceDemands285.exact_support,rows_exact]

theorem exact_observation (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (src : Body)
    {e : Equation} (translated : body p mapping target src = some e) {q : Profile}
    (loaded : ofEquation p mapping target src = some q) (a b : Assignment) (equal : q.agrees a b) :
    e.Holds a ↔ e.Holds b := by
  have h := ofEquation_exact p mapping target src
  rw [loaded,translated] at h
  have profile : q = ⟨equationReads e,equationRows e⟩ := Option.some.inj h
  subst q
  exact GeneralRebaseFiniteRowReads285.equation_iff e a b equal.1 equal.2

end Yulang.GeneralRebaseCoordinateProfile285
