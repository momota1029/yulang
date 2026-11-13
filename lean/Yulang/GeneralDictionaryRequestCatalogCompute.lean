import Yulang.GeneralDictionaryRequestCatalog

/-! An executable extraction of the finite per-request catalog. This computes
only syntactic eligible requests from the actual journal, not model validity,
full Evidence, or saturation. No classical proposition test is needed. -/
namespace Yulang.GeneralDictionaryRequestCatalogCompute
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalMaterialization
open GeneralDictionaryReachableRequestHistory
variable {roles : Roles.RoleDecls}

def packetRequests (packet : Packet roles) : List Request :=
  (emitted packet).filter fun request =>
    (generated packet.context.state packet.context.interpretation [request]).variables.isEmpty

def catalog (state : Tracked roles) : List Request :=
  state.current.packets.reverse.flatMap packetRequests

theorem packet_exact (packet : Packet roles) :
    packetRequests packet = GeneralDictionaryRequestCatalog.eligibleRequests packet := by
  classical
  unfold packetRequests GeneralDictionaryRequestCatalog.eligibleRequests
  apply List.filter_congr
  intro request member
  cases h : (generated packet.context.state packet.context.interpretation [request]).variables <;> simp

theorem catalog_exact (state : Tracked roles) : catalog state = GeneralDictionaryRequestCatalog.catalog state := by
  unfold catalog GeneralDictionaryRequestCatalog.catalog
  exact congrArg (fun f => state.current.packets.reverse.flatMap f) (funext packet_exact)

/-- Exactness is with respect to syntactic historical coverage, not semantics. -/
theorem coverage_exact (state : Tracked roles) (batch : List Request) :
    GeneralDictionaryRecordedBatchModels.Covered state.current batch ↔
      ∀ request ∈ batch, request ∈ catalog state := by
  rw [catalog_exact]
  exact GeneralDictionaryRequestCatalog.covered_iff state batch
end Yulang.GeneralDictionaryRequestCatalogCompute
