import Yulang.GeneralDeclarativeI65I74CanonicalCertificateErasure461
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.ExistingUseBoundary
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open WrittenPattern460
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessVarianceFixtures357 (source)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open InlineStructuralPolicy458 (Ticket policy)

private def endType : Pattern := .app 9 []
private def tagArm : Pattern := .variant 7 (.record 31 (.var 3) endType)
private def head : Pattern := .record 10 (.join tagArm (.join tagArm tagArm)) endType
private def cond : Clause := ⟨6,19,[.var 3],[]⟩
private def decl : Declaration := ⟨218,19,[head],[cond],[],[]⟩
private def bundle : InputBundle :=
  let ks : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,ks⟩,⟨.absent,ks⟩,⟨0,[⟨19,1,[]⟩]⟩,[decl]⟩
private def empty : Expr := .primitive .emptyRecord []
private def snapshot : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,.record 10 (.variable 1) empty⟩,⟨1,.variant 7 (.variable 1)⟩]⟩
private def rootNative : TyTerm Nat := .record 10 (.var 1) .emptyRecord
private def childNative : TyTerm Nat := .variant 7 (.var 1)
private def sourceOrigins : List Origin := [⟨0,[701],.ordinary rootNative⟩,⟨1,[702],.ordinary childNative⟩]
private def build : Option FullProblem := do
  let graph ← compile source
  let src ← GeneralSourceMetadataBareBundle291.compile bundle
  let env : Environment := ⟨3,2,0,source,graph,src⟩
  let core : CoreState := ⟨⟨env,snapshot,[]⟩,[],sourceOrigins,[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)
private def p : FullProblem := build.get (by decide +kernel)
private def w : EligibleWire (exactHeaderReader (alreadyHomogeneous p.old)) :=
  ⟨(9 : Nat),⟨.down () ⟨0,.same,.field 0 0,(.older (.old 0) : Ticket)⟩
    ⟨[0,1],[0,1]⟩ (.stop ()),⟨⟨1,.same,1⟩,[],.same⟩⟩⟩
private def report : ReportAtField := ⟨[71,2],218,0,6,[(.field 10,1)],1⟩
private def exactQuery : Expr := .record 10 (.variant 7 (.record 31 (.variable 3) empty)) empty
private def stamp : Option Bool :=
  (readJoint snapshot (policy p.old.state.core) (fun _ => queryKeys p.old.state.core)
    inheritedCompilerPlacement 0 (normalized (readTerm head)) exactQuery w.along.visit).map fun u => u.2.2.2

/-- info: [true, true, false] -/
#guard_msgs in
#eval [decide (readEligibleField (exactHeaderReader (alreadyHomogeneous p.old)) w = some report),
  decide (stamp = some false),
  HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 report) (.fieldK2 (toPriorCertificate p w))]

theorem actual_named_only_case_cannot_set_the_prior_inline_stamp :
    readEligibleField (exactHeaderReader (alreadyHomogeneous p.old)) w = some report ∧
    stamp = some false ∧
    HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 report)
      (.fieldK2 (toPriorCertificate p w)) = false := by
  decide +kernel

open CommonNominalFullCarrier (Ty Equivalent record variant)
private def recursiveVariant : Ty := .variant 7 (.block [.variant 7 (.inl 0)] 0)

private theorem exact_variant_unroll : Equivalent recursiveVariant (variant 7 recursiveVariant) := by
  have same (k : Nat) : CommonNominalFullCarrier.observeTy k recursiveVariant =
      CommonNominalFullCarrier.observeTy k (variant 7 recursiveVariant) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [← same]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [same]
    exact CommonNominalFullDemand.producerLe_refl _

private def model : I72.Model :=
  ⟨fun n => (if n = 0 then record 10 recursiveVariant .emptyRecord else recursiveVariant,Common.rowEmpty),
   fun _ => none, fun n => if n = 0 then some (.ordinary rootNative)
     else if n = 1 then some (.ordinary childNative) else none⟩

theorem actual_named_only_receipt_is_on_a_real_fitting_state : I72.FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro row hit
    change row ∈ snapshot.equations at hit
    simp only [snapshot,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact exact_variant_unroll
  · intro _ absent; cases absent
  · intro orig hit
    change orig ∈ sourceOrigins at hit
    simp only [sourceOrigins,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl <;> rfl
  · intro _ absent; cases absent

#print axioms actual_named_only_receipt_is_on_a_real_fitting_state
#print axioms actual_named_only_case_cannot_set_the_prior_inline_stamp

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461.ExistingUseBoundary
