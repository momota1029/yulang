import Yulang.GeneralNominalHeadCandidateSupport186
import Yulang.GeneralNominalHeadCandidateSemantic186

/-! Binder collisions separate point endpoints from purpose-eight allocations.
For revisited candidates, remaining nonpoint collisions reduce to equal names
and hence to one historical actual head witness. -/
namespace Yulang.GeneralNominalHeadBinderCollisions186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same same_trans same_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem point_binder (candidate : Plan roles) (name : Nat)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2) :
    candidate.binder name = ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 := by
  simp only [Plan.binder,input,ite_false,point,ite_true]

theorem nonpoint_name (candidate : Plan roles) (first last : Nat)
    (one : first ∉ candidate.packet.declaration.outputNames)
    (two : last ∉ candidate.packet.declaration.outputNames)
    (a : ((GeneralNominalPacketSupport.capture candidate.packet).inputs first).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs first).2)
    (b : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs last).2)
    (same : candidate.binder first = candidate.binder last) : first = last := by
  rw [GeneralNominalBinderIdentity181.binder_fresh candidate first one a,
    GeneralNominalBinderIdentity181.binder_fresh candidate last two b] at same
  have identities := (GeneralNominalIdentities.source_identity candidate.packet.context.state.seed _ _).mp same
  exact congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) identities

theorem point_fits (candidate : Plan roles) (name : Nat)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (model : Assignment) (value : Ty)
    (fits : GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name) value) :
    Equivalent value (model (candidate.binder name)).1 := by
  rw [point_binder candidate name input point]
  exact ⟨by simpa only [← point] using fits.2,fits.1⟩

theorem historical_coherence (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (first last : Use) (one : first ∈ candidate.headSchema.variables) (two : last ∈ candidate.headSchema.variables)
    (oneActual : first.mode = .actual) (twoActual : last.mode = .actual)
    (oneInput : first.name ∉ candidate.packet.declaration.outputNames)
    (twoInput : last.name ∉ candidate.packet.declaration.outputNames)
    (model : Assignment) (valid : Models state model)
    (a b : Ty) (seenA : Observes model first.origin a) (seenB : Observes model last.origin b)
    (fitA : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name) a)
    (fitB : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name) b)
    (same : candidate.binder first.name = candidate.binder last.name) : Equivalent a b := by
  by_cases pointA : ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name).2
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).2
    · have left := point_fits candidate first.name oneInput pointA model a fitA
      have right := point_fits candidate last.name twoInput pointB model b fitB
      rw [same] at left
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · exact False.elim ((GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate
        reachable candidate current last.name twoInput pointB first.name).1
        (same.symm.trans (point_binder candidate first.name oneInput pointA)))
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).2
    · exact False.elim ((GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate
        reachable candidate current first.name oneInput pointA last.name).1
        (same.trans (point_binder candidate last.name twoInput pointB)))
    · have names := nonpoint_name candidate first.name last.name oneInput twoInput pointA pointB same
      have left := GeneralNominalHeadCandidateSemantic186.candidate_actual checked reachable historical candidate
        member registered identity current declaration first one oneActual model valid
      have right := GeneralNominalHeadCandidateSemantic186.candidate_actual checked reachable historical candidate
        member registered identity current declaration last two twoActual model valid
      rw [names] at left
      exact (same_trans left (same_symm right)).2.2 a b seenA seenB

end Yulang.GeneralNominalHeadBinderCollisions186
