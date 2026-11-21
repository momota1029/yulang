import Yulang.GeneralVersionedRecursiveCut314

set_option backward.isDefEq.respectTransparency false
/-! Effective endpoint operands need only their own side to be tight. The
old and current identifiers and the other side of either interval can differ.
A checked head provides the missing direction of the subtype judgement. -/
namespace Yulang.GeneralVersionedTightOperands315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent subtype_refl)
open GeneralFiniteTypedWrites312 (reflexive symmetric transitive)

def TightSide (p : Plan roles) (m : Assignment) (mode : Mode) (name : Nat) : Prop :=
  match mode with
  | .actual => True
  | .lower => Subtype (variables p m .actual name) (variables p m .lower name)
  | .upper => Subtype (variables p m .upper name) (variables p m .actual name)

theorem of_fits (p : Plan roles) (m : Assignment) (mode : Mode) (name : Nat)
    (fits : GeneralNominalCaptureMerges.Fits m ((capture p.packet).inputs name) (m (binder p name)).1)
    (tight : TightSide p m mode name) :
    Equivalent (variables p m mode name) (variables p m .actual name) := by
  by_cases output : name ∈ p.packet.declaration.outputNames
  · simp only [variables,output,ite_true]
    exact reflexive _
  · cases mode with
    | actual => exact reflexive _
    | lower =>
      exact ⟨by simpa only [variables,output,ite_false] using fits.1,tight⟩
    | upper =>
      exact ⟨tight,by simpa only [variables,output,ite_false] using fits.2⟩

theorem of_point (p : Plan roles) (m : Assignment) (mode : Mode) (name : Nat)
    (point : ((capture p.packet).inputs name).1 = ((capture p.packet).inputs name).2) :
    TightSide p m mode name := by
  have same (chosen : Mode) : variables p m chosen name = variables p m .actual name := by
    by_cases out : name ∈ p.packet.declaration.outputNames
    · simp only [variables,out,ite_true]
    · cases chosen <;> simp only [variables,binder,out,ite_false,point,ite_true]
  cases mode with
  | actual => trivial
  | lower => unfold TightSide; rw [same .lower]; exact subtype_refl _
  | upper => unfold TightSide; rw [same .upper]; exact subtype_refl _

theorem operand {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration)
    (m : Assignment) (valid : Models s m) (head : HeadModels p.packet m) (schema : SchemaHolds p p.headSchema m)
    (mode : Mode) (name : Nat) (named : name ∈ p.packet.declaration.inputNames ∨ name ∈ p.packet.declaration.outputNames)
    (ready : mode = .actual ∨ name ∈ p.packet.declaration.outputNames ∨
      TightSide q m mode name ∧ TightSide p m mode name) :
    Equivalent (variables q m mode name) (variables p m mode name) := by
  have same := GeneralVersionedRevisitActual314.actual_agree checked actual frame stored identity rule m valid schema name named
  have fromOutput (out : name ∈ p.packet.declaration.outputNames) :
      Equivalent (variables q m mode name) (variables p m mode name) := by
    have prior : name ∈ q.packet.declaration.outputNames := rule.symm ▸ out
    simpa only [variables,out,prior,ite_true] using same
  rcases ready with rfl|out|⟨previous,current⟩
  · exact same
  · exact fromOutput out
  rcases named with input|output
  · have before := (GeneralNominalVersionedDiagnostic232.head_equations (valid.2.1 q stored)).2.1 name (rule.symm ▸ input)
    have after := GeneralNominalVersionedCurrentHead237.capture_fits p frame valid head schema name (.inl input)
    exact transitive (of_fits q m mode name before previous) (transitive same (symmetric (of_fits p m mode name after current)))
  · exact fromOutput output

end Yulang.GeneralVersionedTightOperands315
