import Yulang.GeneralRebaseSourceDemands285

namespace Yulang.GeneralRebaseBodyReads285
open GeneralNominalCenters (Plan)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralNominalRebaseEffectView243 (body bodyVariables Equation OldExpr compile eval)
open GeneralNominalEffectSupport249 (equationReads support eval_equal)
open GeneralRebaseSourceDemands285 (demands expand exact_support)
open GeneralPresenceUsedSupport245 (typedReads)
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)

def program (p : Plan roles) (mapping : Nat → CompTerm Nat) (origin : Body) : Option (List Nat) :=
  (compileBody p origin).map (fun e => (demands .actual e).flatMap (expand (bodyVariables p mapping origin)))

def frame (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (origin : Body) :
    Option (List Nat) :=
  (program p mapping origin).map (fun reads => typedReads (mapping target).1 ++ reads)

theorem program_exact (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (origin : Body) :
    (body p mapping target origin).map (fun e => support e.expression) = program p mapping origin := by
  unfold body program
  cases found : compileBody p origin with
  | none => rfl
  | some e => exact congrArg some (exact_support (bodyVariables p mapping origin) .actual e)

theorem frame_exact (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (origin : Body) :
    (body p mapping target origin).map equationReads = frame p mapping target origin := by
  unfold body frame program
  cases found : compileBody p origin with
  | none => rfl
  | some e =>
    exact congrArg some (congrArg (typedReads (mapping target).1 ++ ·)
      (exact_support (bodyVariables p mapping origin) .actual e))

theorem value_agrees (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (origin : Body)
    {eqn : Equation} (found : body p mapping target origin = some eqn) {reads : List Nat}
    (calculated : program p mapping origin = some reads) (a b : Assignment)
    (rows : ∀ n, (a n).2 = (b n).2) (types : ∀ n ∈ reads, (a n).1 = (b n).1) :
    eval a eqn.expression = eval b eqn.expression := by
  have same := program_exact p mapping target origin
  rw [found,calculated] at same
  have exactReads : support eqn.expression = reads := Option.some.inj same
  rw [← exactReads] at types
  exact eval_equal eqn.expression a b rows types

theorem equation_agrees (p : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (origin : Body)
    {eqn : Equation} (found : body p mapping target origin = some eqn) {reads : List Nat}
    (calculated : frame p mapping target origin = some reads) (a b : Assignment)
    (rows : ∀ n, (a n).2 = (b n).2) (types : ∀ n ∈ reads, (a n).1 = (b n).1) :
    eqn.Holds a ↔ eqn.Holds b := by
  have same := frame_exact p mapping target origin
  rw [found,calculated] at same
  exact GeneralNominalEffectSupport249.equation_iff eqn a b rows (Option.some.inj same ▸ types)

end Yulang.GeneralRebaseBodyReads285
