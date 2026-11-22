import Yulang.GeneralDeclarativeModeCongruence344
import Yulang.GeneralDeclarativeModeBridge343

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCommitPort344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause)
open GeneralWhereVersionCompiler317 (child)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedPlans231 (variables)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalVersionedExpressionFrame236 (reads)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeClauseBatch327 (Input Port)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralStoppedOrdinarySite335 (argument)
open GeneralStoppedPlacement335 (Meaning)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

/-- A comparison of read operands, not of whole raw/logical result
values. Actual operands under a nominal expression stay actual. -/
def OperandMatch (p : Plan rs) (m : Assignment) (cap : Nat → Capture) (mode : Mode) (code : Expr) : Prop :=
  ∀ key ∈ reads mode code, Equivalent (variables p m key.1 key.2)
    (GeneralDeclarativeWhere319.variables cap m key.1 key.2)

theorem literal_mode {s : State} (cap : Nat → Capture) {mode : Mode} {name : Nat}
    {code : Expr} (read : Origin s name (logical cap mode code))
    (m : Assignment) (fit : Models s m) :
    Equivalent (m name).1 (value (GeneralDeclarativeWhere319.variables cap m) mode code) := by
  have got := semantic (origin_reads read) m fit
  change Equivalent (m name).1 (value (GeneralDeclarativeHead320.environment m) .actual (logical cap mode code)) at got
  rwa [logical_value] at got

/-- Read the checked raw compiler rows and the actual prepared ordinary
port, and derive all positional mode equalities from operand matching.
There is no equality assumption on the child itself. -/
theorem compound_position (p : Plan rs) (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (idx : Fin (rs cl.role).arity) (m : Assignment)
    (raw : Holds p m) {s : State} (fit : Models s m) (cap : Nat → Capture) (port : Port)
    (prepared : Input s p.packet.registry.constructors p.packet.context.interpretation cap cl port)
    (pat : GeneralDeclarationPatterns.Pattern) (code : Expr)
    (written : cl.arguments[idx.val]? = some pat) (atPort : port.code[idx.val]? = some code)
    (compound : Compound pat)
    (printed : translate p.packet.registry.constructors p.packet.context.interpretation pat = some code)
    (lo : OperandMatch p m cap .lower code) (mid : OperandMatch p m cap .actual code)
    (hi : OperandMatch p m cap .upper code) :
    Meaning m (argument (child p cl sig) idx) (port.input idx.val) := by
  have actualPat : cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt) = pat :=
    (List.getElem?_eq_some_iff.mp written).2
  have rawPrint : translate p.packet.registry.constructors p.packet.context.interpretation
      (cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt)) = some code := actualPat.symm ▸ printed
  have modes := GeneralDeclarativeCommitModes344.all_modes p cl inside sig idx m raw code rawPrint
  have reads := (prepared.2 idx.val pat code written atPort compound).2
  exact ⟨eqv_trans modes.1 (eqv_trans (GeneralDeclarativeModeCongruence344.expression _ _ _ _ lo)
      (eqv_symm (literal_mode cap reads.1 m fit))),
    eqv_trans modes.2.1 (eqv_trans (GeneralDeclarativeModeCongruence344.expression _ _ _ _ mid)
      (eqv_symm (literal_mode cap reads.2.1 m fit))),
    eqv_trans modes.2.2 (eqv_trans (GeneralDeclarativeModeCongruence344.expression _ _ _ _ hi)
      (eqv_symm (literal_mode cap reads.2.2 m fit)))⟩

end Yulang.GeneralDeclarativeCommitPort344
