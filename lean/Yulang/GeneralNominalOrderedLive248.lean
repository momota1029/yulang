import Yulang.GeneralNominalOrderedRaw248
import Yulang.GeneralNominalRebaseLiveView243
/-! Actual centered live-site bounds and value transport. Output labels and
site identities stay fixed, while their explicitly compiled expressions retain
old meaning. This is not the whole journal or an operational transition. -/
namespace Yulang.GeneralNominalOrderedLive248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceModelCongruence245
open CommonNominalFullCarrier

theorem site_compatible (site : GeneralNominalCenters.Site roles)
 (same : Compatible model first last) : site.Holds first ↔ site.Holds last := by
 apply forall_congr'
 intro index
 exact and_congr
   (GeneralNominalAssignmentCongruence238.subtype_iff (same _).1 (same _).1)
   (GeneralNominalAssignmentCongruence238.subtype_iff (same _).1 (same _).1)

theorem site_forward (site : GeneralNominalCenters.Site roles) (old fresh : List (Entry Nat))
 (safe : SafeOrder old) (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 (GeneralNominalRebaseLiveView243.compile site (mapping old)).Holds (solve model fresh assignment) ↔
 site.Holds assignment := by
 rw [GeneralNominalRebaseLiveView243.compile_holds,GeneralNominalOrderedRaw248.read_mapping,
   solve_absorbs model old fresh safe within]
 exact site_compatible site (GeneralPresenceOrderedRecovery247.solve_compatible model
   GeneralPresenceCommonLaws245.common_laws old assignment valid)

theorem sites_forward (sites : List (GeneralNominalCenters.Site roles)) (old fresh : List (Entry Nat))
 (safe : SafeOrder old) (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 (∀ site ∈ GeneralNominalRebaseLiveView243.compileAll sites (mapping old), site.Holds (solve model fresh assignment)) ↔
 ∀ site ∈ sites, site.Holds assignment := by
 simp only [GeneralNominalRebaseLiveView243.compileAll,List.forall_mem_map,site_forward _ old fresh safe within assignment valid]

theorem outputs_forward (site : GeneralNominalCenters.Site roles) (old fresh : List (Entry Nat))
 (safe : SafeOrder old) (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (output : GeneralSourceState.Output)
 (member : output ∈ site.occurrence.demand.outputs) :
 ∃ translated ∈ (GeneralNominalRebaseLiveView243.compile site (mapping old)).outputs,
   translated.name = output.name ∧
   Equivalent (translated.target.eval model (solve model fresh assignment)) (assignment output.target).1 := by
 obtain ⟨translated,present,name,equal⟩ := GeneralNominalRebaseLiveView243.output_read site (mapping old)
   (solve model fresh assignment) output member
 refine ⟨translated,present,name,?_⟩
 rw [equal,GeneralNominalOrderedRaw248.read_mapping,solve_absorbs model old fresh safe within]
 exact (GeneralPresenceOrderedRecovery247.solve_compatible model GeneralPresenceCommonLaws245.common_laws old assignment valid output.target).1

theorem role_identity (site : GeneralNominalCenters.Site roles) (entries : List (Entry Nat)) :
 (GeneralNominalRebaseLiveView243.compile site (mapping entries)).identity = site.occurrence.identity ∧
 (GeneralNominalRebaseLiveView243.compile site (mapping entries)).role = site.occurrence.demand.role := ⟨rfl,rfl⟩
end Yulang.GeneralNominalOrderedLive248
