import Yulang.GeneralDictionaryCollectedRequests

/-! Recover the chronological request history directly from an actual reachable
journal. The only extra restriction is syntactic variable-freedom of its packets;
no final batch provenance, historical observations or semantic validity is supplied. -/
namespace Yulang.GeneralDictionaryReachableRequestHistory
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization
open GeneralDictionaryCollectedRequests
variable {roles : Roles.RoleDecls}

def emitted (packet : Packet roles) : List Request :=
  requests packet.context.state packet.registry packet.site.occurrence
    packet.declaration packet.checked packet.bindings

/-- Reverse the prepend-only packet journal to obtain installation order. -/
def catalog (state : Tracked roles) : List Request := state.current.packets.reverse.flatMap emitted

def Closed (state : Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets, (GeneralNominalPacketSupport.namedSchema packet).variables = []

theorem closed_before {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (step : GeneralNominalValueSteps.Step registry root before after) (closed : Closed after) : Closed before :=
  fun packet member => closed packet (GeneralNominalValueBudget.at_packets step.choose_spec.2 packet member)

theorem administrative_packets {registry : Registry} {before after : State roles} {focus}
    (step : GeneralNominalSupportSteps.Administrative registry before focus after) :
    after.packets = before.packets := by
  cases step <;> rfl

theorem catalog_install (before : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) :
    catalog (GeneralNominalValueSteps.install before packet support) = catalog before ++ emitted packet := by
  simp [catalog,GeneralNominalValueSteps.install,GeneralNominalSupportSteps.install,
    GeneralNominalFeedbackSites.install,List.reverse_cons,List.flatMap_append]

theorem history_step {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (history : Collected registry root before (catalog before))
    (step : GeneralNominalValueSteps.Step registry root before after) (closed : Closed after) :
    Collected registry root after (catalog after) := by
  obtain ⟨focus,reached,action⟩ := step
  cases action with
  | administrative focus state action =>
    have eq : catalog {before with current := state} = catalog before := by
      simp only [catalog,administrative_packets action]
    rw [eq]
    exact .advance history ⟨focus,reached,.administrative focus state action⟩
  | install packet support enabled novel guard =>
    rw [catalog_install]
    exact .install history packet support ⟨_,reached,.install packet support enabled novel guard⟩
      (closed packet List.mem_cons_self)
  | merge first last support one two same novel guard =>
    exact .advance history ⟨_,reached,.merge first last support one two same novel guard⟩

/-- Final journal syntax suffices to reconstruct an actual finite collection
history from the ordinary Reachable witness. -/
theorem history {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (closed : Closed state) : Collected registry root state (catalog state) := by
  obtain ⟨start,initial,path⟩ := reachable
  induction path with
  | refl =>
    obtain ⟨context,source,rfl⟩ := initial
    exact .initial context source
  | tail path step ih => exact history_step (ih (closed_before step closed)) step closed

/-- Membership in the actual finite journal catalog replaces a manually built
per-request provenance witness. -/
theorem supported {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (closed : Closed state) (batch : List Request) (included : ∀ request ∈ batch, request ∈ catalog state) :
    GeneralDictionaryRequestProvenance.Supported registry root state batch :=
  supported_subset (history reachable closed) batch included
/-- A finite catalog that retains exactly variable-free packet emissions.
The filter is syntactic, not a test of model validity or dictionary evidence. -/
noncomputable def eligible (packet : Packet roles) : List Request := by
  classical
  exact if (GeneralNominalPacketSupport.namedSchema packet).variables = [] then emitted packet else []

noncomputable def safeCatalog (state : Tracked roles) : List Request :=
  state.current.packets.reverse.flatMap eligible

theorem eligible_closed (packet : Packet roles)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []) :
    eligible packet = emitted packet := by simp [eligible,closed]

theorem safeCatalog_install (before : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) :
    safeCatalog (GeneralNominalValueSteps.install before packet support) = safeCatalog before ++ eligible packet := by
  simp [safeCatalog,GeneralNominalValueSteps.install,GeneralNominalSupportSteps.install,
    GeneralNominalFeedbackSites.install,List.reverse_cons,List.flatMap_append]

theorem safe_history_step {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (history : Collected registry root before (safeCatalog before))
    (step : GeneralNominalValueSteps.Step registry root before after) :
    Collected registry root after (safeCatalog after) := by
  classical
  obtain ⟨focus,reached,action⟩ := step
  cases action with
  | administrative focus state action =>
    have eq : safeCatalog {before with current := state} = safeCatalog before := by
      simp only [safeCatalog,administrative_packets action]
    rw [eq]
    exact .advance history ⟨focus,reached,.administrative focus state action⟩
  | install packet support enabled novel guard =>
    rw [safeCatalog_install]
    by_cases closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []
    · rw [eligible_closed packet closed]
      exact .install history packet support ⟨_,reached,.install packet support enabled novel guard⟩ closed
    · simp only [eligible,closed,ite_false,List.append_nil]
      exact .advance history ⟨_,reached,.install packet support enabled novel guard⟩
  | merge first last support one two same novel guard =>
    exact .advance history ⟨_,reached,.merge first last support one two same novel guard⟩

/-- Every actual reachable state has an operational collection history for its
finite variable-free emission catalog. No final Closed or Supported premise. -/
theorem safe_history {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    Collected registry root state (safeCatalog state) := by
  obtain ⟨start,initial,path⟩ := reachable
  induction path with
  | refl =>
    obtain ⟨context,source,rfl⟩ := initial
    exact .initial context source
  | tail _ step ih => exact safe_history_step ih step

theorem safe_member (state : Tracked roles) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (request : Request) (member : request ∈ emitted packet) : request ∈ safeCatalog state := by
  apply List.mem_flatMap.mpr
  refine ⟨packet,?_,?_⟩
  · exact List.mem_reverse.mpr recorded
  · rw [eligible_closed packet closed]; exact member

theorem safe_models {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (selected : List Request) (included : ∀ request ∈ selected, request ∈ safeCatalog state)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation selected) model :=
  GeneralDictionaryCollectedRequests.models (safe_history reachable) selected included
    declaration capture report model valid
end Yulang.GeneralDictionaryReachableRequestHistory
