import Yulang.GeneralRebaseBodyReads285
import Yulang.GeneralRebaseOutputDepthSuccessor271
import Yulang.GeneralOutputRebasePublic260

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralRebaseDepthReads285
open GeneralDictionaryOutputDepth252 (plan root registry declaration initial snapshot rhs P)
open GeneralDictionaryOutputDepthInstall252 (installed step)
open GeneralRebaseBodyReads285 (program frame value_agrees equation_agrees)
open GeneralNominalRebaseEffectView243 (body Equation eval)
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (Body)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open GeneralNominalVersionedJournal232 (Models)

abbrev explicit : Body := .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩

theorem translated : GeneralNominalCenteredHeadMatEffects.compileBody plan explicit = some rhs := by
  rfl

theorem actualDemand (mode : GeneralNominalMaterialization.Mode) :
    GeneralRebaseSourceDemands285.demands mode rhs = [(.actual,0)] := rfl

theorem translated_variable :
    GeneralNominalRebaseEffectView243.bodyVariables plan CompTerm.var explicit .actual 0 = .var 2 := by
  change GeneralNominalRebaseEffectView243.variables plan CompTerm.var .actual 0 = .var 2
  unfold GeneralNominalRebaseEffectView243.variables
  split <;> exact congrArg Core.PresenceGeneration.TyTerm.var ((GeneralNominalVersionedFrame231.binder_eq plan 0).symm.trans GeneralDictionaryOutputDepth252.binder_exact)

theorem equation_emitted :
    body plan CompTerm.var 3 explicit =
      some ⟨.var 3,.nominal 0 [.nominal 0 [.source (.var 2)]]⟩ := by
  unfold body
  rw [translated]
  simp only [Option.map_some,GeneralNominalRebaseEffectView243.compile,
    GeneralNominalRebaseEffectView243.compileMany,translated_variable]
  rfl

theorem read_input : program plan CompTerm.var explicit = some [2] := by
  unfold program
  rw [translated]
  simp only [Option.map_some,actualDemand,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    GeneralRebaseSourceDemands285.expand,translated_variable]
  rfl

theorem read_equation : frame plan CompTerm.var 3 explicit = some [3,2] := by
  rw [frame,read_input]
  rfl

def valueFromInput (m : Assignment) : Ty := nominal 0 [.inl (nominal 0 [.inl (m 2).1])]

abbrev actualEquation : Equation := ⟨.var 3,.nominal 0 [.nominal 0 [.source (.var 2)]]⟩

theorem body_value (m : Assignment) : eval m actualEquation.expression = valueFromInput m := rfl

theorem sameValue (a b : Assignment) (same : (a 2).1 = (b 2).1) :
    eval a actualEquation.expression = eval b actualEquation.expression := by
  rw [body_value,body_value]
  simp only [valueFromInput,same]

theorem installed_body (m : Assignment) (valid : Models installed m) : actualEquation.Holds m := by
  have raw := valid.2.1 plan List.mem_cons_self
  have outs := raw.2.2
  unfold GeneralNominalVersionedPlans231.Outputs at outs
  rw [GeneralDictionaryOutputDepth252.emitted_exact] at outs
  have result := outs ⟨3,.actual,rhs⟩ List.mem_cons_self
  change Equivalent (m 3).1
    (nominal 0 [.inl (nominal 0 [.inl (m (GeneralNominalVersionedFrame231.binder plan 0)).1])]) at result
  rw [GeneralDictionaryOutputDepth252.binder_exact] at result
  exact result

theorem real_readback : GeneralNominalVersionedMixedKernel234.Step registry root initial installed ∧
    frame plan CompTerm.var 3 explicit = some [3,2] ∧
    (∀ m, Models installed m → actualEquation.Holds m) :=
  ⟨step,read_equation,installed_body⟩

end Yulang.GeneralRebaseDepthReads285
