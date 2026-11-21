import Yulang.GeneralDeclarativePairProbe326
import Yulang.CommonNominalFullFiniteConstructors

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairUnion326
open CommonNominalFullCarrier (Ty Equivalent Subtype observeTy)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans union_congr)
open CommonNominalFullDemand (ProbeAt ProbeStep MaskedProbeStep)

/-- The covariant pair constructor groups joins componentwise in the
full nominal observer, with arbitrary children. This is not a split
of an invariant nominal or a witness using a chosen endpoint. -/
theorem pair_group (a b c d : Ty) :
    Equivalent (.union (CommonNominalFullCarrier.pair a b) (CommonNominalFullCarrier.pair c d))
      (CommonNominalFullCarrier.pair (.union a c) (.union b d)) := by
  have equivalentAt (depth : Nat) :
      CommonNominalFullDemand.ProducerEq Common.rowLe
        (observeTy depth (.union (CommonNominalFullCarrier.pair a b) (CommonNominalFullCarrier.pair c d)))
        (observeTy depth (CommonNominalFullCarrier.pair (.union a c) (.union b d))) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env obs
    cases depth <;> cases rank <;> cases obs <;>
      simp [CommonNominalFullCarrier.pair,observeTy,CommonNominalSyntax.Layer.evalAt,
        CommonNominalSyntax.observe,CommonNominalSyntax.graph,ProbeAt,ProbeStep,MaskedProbeStep]
  exact ⟨fun d => (equivalentAt d).1,fun d => (equivalentAt d).2⟩

open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativePairCenters326 (pair)
open GeneralNominalCenteredHeadMatExpressions (Expr value translate)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeForwardHead325 (by_walk)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)

/-- Visible positive pair terms are defined by their center expression
alone: a pair, or a join of such terms. This does not match arbitrary
ordinary models merely by checking the two endpoint tags. -/
inductive Coordinates : Expr → Expr → Expr → Prop where
  | literal : Coordinates (pair a b) a b
  | union : Coordinates a p q → Coordinates b r s →
      Coordinates (.join a b) (.join p r) (.join q s)

theorem exact (read : Coordinates expression left right) (m : Assignment) :
    eqAt m expression (pair left right) := by
  induction read with
  | literal => exact eqv_refl _
  | union a b one two => exact eqv_trans (union_congr one two) (pair_group ..)

theorem center_rule {s : State}
    (visible : Derives s (.variable name) expression) (read : Coordinates expression left right) :
    Entails s ⟨name,pair left right⟩ :=
  fun m valid => eqv_trans (entails visible m valid) (exact read m)

theorem with_joined_centers {s : State}
    (printed : translate c i (normalize p) = some (pair lcode rcode))
    (visible : Derives s (.variable arg.center) expr) (read : Coordinates expr left right)
    (one : Walk .actual left lcode before) (two : Walk .actual right rcode after)
    (bindings : Binds s cap (before ++ after)) : Result s (fact c i cap arg p) := by
  apply by_walk printed (center_rule visible read) ?_ bindings
  simpa only [pair,List.append_nil] using Walk.primitive (.cons one (.cons two .nil))

end Yulang.GeneralDeclarativePairUnion326
