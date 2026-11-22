import Yulang.GeneralDeclarativeEndpointCase336
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointMixedTail336
open GeneralDeclarativeEndpointCase336 (loFields hiFields rowLo endCode model)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeEndpointRecord336 (Read mask_below)
open GeneralDeclarativeEndpointResidual336 (exact_residuals)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Subtype Equivalent record mask exactEmpty emptyRecord subtype_refl subtype_trans)
open CommonNominalFullDemand (ProbeAt ProbeStep MaskedProbeStep)
open CommonNominalSyntax (Layer)
open GeneralNominalCommonBridge (Assignment)

abbrev width : Expr := .primitive .emptyRecord []
abbrev rowHi : Equation := ⟨2,.record 7 (.variable 4) width⟩
abbrev source : State := ⟨⟨[],[(0,1),(1,2)]⟩,[rowLo,rowHi]⟩
def support : Supported source (fun _ => False) :=
  ⟨fun row o => row ∈ source.equations ∧ o = .source,And.left⟩

theorem observed : Read support arg [7] loFields hiFields loFields hiFields endCode width :=
  ⟨⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩,by decide,
    .inline (alias_refl _) .exactEnd (from_source support ⟨List.mem_cons_self,rfl⟩),
    .inline (alias_refl _) .width (from_source support ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩),
    rfl,rfl⟩

def mixedModel : Assignment := fun j =>
  if j = 2 then (record 7 .top emptyRecord,(model j).2) else model j

theorem inhabited : Models source mixedModel := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e here
    change e ∈ [(0,1),(1,2)] at here
    rcases List.mem_cons.mp here with rfl|last
    · exact (GeneralDeclarativeRecordSplit330.interval 7).1
    · cases List.mem_singleton.mp last
      exact subtype_trans (GeneralDeclarativeRecordSplit330.interval 7).2
        (CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _) CommonNominalFullCarrier.exactEmpty_below_width)
  · intro row here
    change row ∈ [rowLo,rowHi] at here
    rcases List.mem_cons.mp here with rfl|last
    · exact eqv_refl _
    · cases List.mem_singleton.mp last
      exact eqv_refl _

/-- Exact/width terminal remains distinguishable at every uncaptured
label, even after the residual mask. -/
theorem strict (keys : List Nat) (q : Nat) (fresh : q ∉ keys) :
    ¬ Subtype (mask keys emptyRecord) (mask keys exactEmpty) := by
  intro below
  let env : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row :=
    ⟨fun _ => .bottom,fun _ => []⟩
  have receives : ProbeAt Common.rowLe 0 env (.mask keys .exactEmpty) (.optional q (.base .int)) := by
    simp [ProbeAt,ProbeStep,MaskedProbeStep,fresh]
  have rejects := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env _ receives
  change ProbeAt Common.rowLe 0 env (.mask keys .emptyRecord) (.optional q (.base .int)) at rejects
  simp [ProbeAt,ProbeStep,MaskedProbeStep] at rejects

theorem exact (m : Assignment) (fit : Models source m) :
    InInterval (mask [7] exactEmpty) (mask [7] emptyRecord) (mask [7] (m 1).1) :=
  exact_residuals observed m fit

theorem genuine_interval :
    InInterval (mask [7] exactEmpty) (mask [7] emptyRecord) (mask [7] (mixedModel 1).1) ∧
    ¬Equivalent (mask [7] exactEmpty) (mask [7] emptyRecord) :=
  ⟨exact _ inhabited,fun eq => strict [7] 8 (by decide) eq.2⟩

end Yulang.GeneralDeclarativeEndpointMixedTail336
