import Yulang.GeneralNominalRawFrame179
import Yulang.GeneralNominalCenteredAllocation

set_option backward.isDefEq.respectTransparency false

/-! Ordinary packet inspection starts without supplied actual origins. Every
origin it later recovers is rooted in a source slot of that historical context.
This does not bound generated-schema or registered-site origin support. -/
namespace Yulang.GeneralNominalRawOrigin182
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCenteredModelExtension (originSource)

def ReportRoots (result : Report state) (names : List Nat) : Prop :=
  (∀ anchor ∈ result.anchors, originSource anchor.1 ∈ names) ∧
  (∀ test ∈ result.tests, originSource test.1 ∈ names) ∧
  ∀ capture ∈ result.captures, ∀ origin, capture.origin = some origin → originSource origin ∈ names

private theorem empty (result : Report state) (anchors : result.anchors = [])
    (tests : result.tests = []) (captures : result.captures = []) : ReportRoots result names := by
  refine ⟨?_,?_,?_⟩
  · intro anchor member; rw [anchors] at member; cases member
  · intro test member; rw [tests] at member; cases member
  · intro capture member; rw [captures] at member; cases member

private theorem appended (one : ReportRoots (first : Report state) names)
    (two : ReportRoots last names) : ReportRoots (first.append last) names := by
  refine ⟨?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_append.mp member with member | member
    · exact one.1 anchor member
    · exact two.1 anchor member
  · intro test member
    rcases List.mem_append.mp member with member | member
    · exact one.2.1 test member
    · exact two.2.1 test member
  · intro capture member
    rcases List.mem_append.mp member with member | member
    · exact one.2.2 capture member
    · exact two.2.2 capture member

private theorem visited (bounds : Bounds state) (origin : Option Origin) (test : Test)
    (result : Report state) (valid : ReportRoots result names)
    (known : ∀ ref, origin = some ref → originSource ref ∈ names) :
    ReportRoots (Report.visit bounds origin test result) names := by
  refine ⟨?_,?_,valid.2.2⟩
  · intro anchor member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨ref,present,rfl⟩ := List.mem_map.mp member
      exact known ref (by simpa using present)
    · exact valid.1 anchor member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨ref,present,rfl⟩ := List.mem_map.mp member
      exact known ref (by simpa using present)
    · exact valid.2.1 entry member

private theorem fallback (state : GeneralNominalState.State) (names : List Nat)
    (slots : ∀ slot, state.base.source slot ∈ names) (origin : Option Origin)
    (known : ∀ ref, origin = some ref → originSource ref ∈ names) (slot : Fin state.base.slots) :
    originSource (origin.getD (.source (state.base.source slot))) ∈ names := by
  cases origin with
  | none => exact slots slot
  | some ref => exact known ref rfl

mutual
  theorem inspect_roots (state : GeneralNominalState.State) (names : List Nat)
      (slots : ∀ slot, state.base.source slot ∈ names)
      (query : Query) (bounds : Bounds state) (origin : Option Origin)
      (known : ∀ ref, origin = some ref → originSource ref ∈ names) :
      ReportRoots (inspect state query bounds origin) names := by
    have structural (shape index) : ∀ ref,
        (origin.map fun parent => Origin.structural parent shape index) = some ref → originSource ref ∈ names := by
      intro ref recorded
      cases origin with
      | none => cases recorded
      | some parent => cases recorded; exact known parent rfl
    have nominal (name index slot) : ∀ ref,
        some (Origin.nominal (origin.getD (.source (state.base.source slot))) name index) = some ref →
        originSource ref ∈ names := by
      intro ref recorded
      cases recorded
      exact fallback state names slots origin known slot
    cases query with
    | variables variables =>
        simp only [inspect]
        refine ⟨?_,?_,?_⟩
        · intro anchor member
          obtain ⟨ref,present,rfl⟩ := List.mem_map.mp member
          exact known ref (by simpa using present)
        · intro test member; cases member
        · intro capture member ref recorded
          obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
          exact known ref recorded
    | deferred => simpa only [inspect] using (empty (block bounds) rfl rfl rfl : ReportRoots (block bounds) names)
    | scalar expected =>
        simp only [inspect]
        apply visited _ _ _ _ _ known
        split
        · exact empty _ rfl rfl rfl
        · split
          · split <;> exact empty _ rfl rfl rfl
          · exact empty _ rfl rfl rfl
          · exact empty _ rfl rfl rfl
    | node expected patterns =>
        simp only [inspect]
        apply visited _ _ _ _ _ known
        split
        · split
          · exact many_roots state names slots patterns _ _ _ (fun index => structural expected index)
          · exact empty _ rfl rfl rfl
        · exact empty _ rfl rfl rfl
        · exact empty _ rfl rfl rfl
    | nominal expected patterns =>
        simp only [inspect]
        apply visited _ _ _ _ _ known
        split
        · split
          · exact empty _ rfl rfl rfl
          · exact empty _ rfl rfl rfl
          · exact empty _ rfl rfl rfl
        · split
          · split
            · exact empty _ rfl rfl rfl
            · split
              · exact many_roots state names slots patterns _ _ _ (fun index => nominal expected index _)
              · split
                · exact empty _ rfl rfl rfl
                · split
                  · split
                    · exact empty _ rfl rfl rfl
                    · exact appended
                        (many_roots state names slots patterns _ _ _ (fun index => nominal expected index _))
                        (many_roots state names slots patterns _ _ _ (fun index => nominal expected index _))
                  · exact empty _ rfl rfl rfl
          · exact empty _ rfl rfl rfl
  termination_by sizeOf query

  theorem many_roots (state : GeneralNominalState.State) (names : List Nat)
      (slots : ∀ slot, state.base.source slot ∈ names)
      (queries : List Query) (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (known : ∀ index ref, origins index = some ref → originSource ref ∈ names) :
      ReportRoots (inspectMany state queries bounds origins offset) names := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany] <;> exact empty _ rfl rfl rfl
    | cons query queries =>
      cases bounds with
      | nil => simp only [inspectMany]; exact empty _ rfl rfl rfl
      | cons interval intervals =>
          simp only [inspectMany]
          exact appended (inspect_roots state names slots query interval (origins offset) (known offset))
            (many_roots state names slots queries intervals origins (offset+1) known)
  termination_by sizeOf queries
end

theorem report_roots (context : GeneralNominalCandidates.Context) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds context.state)) :
    ReportRoots (GeneralNominalRecursiveCandidates.report context declaration bounds)
      (GeneralNominalState.sources context.state) :=
  many_roots context.state _
    (fun slot => List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))))
    _ bounds _ 0 (fun _ _ impossible => by cases impossible)

theorem report_sources_subset (context : GeneralNominalCandidates.Context)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds context.state)) :
    GeneralNominalRawFrame179.reportSources context.state
      (GeneralNominalRecursiveCandidates.report context declaration bounds) ⊆
      GeneralNominalState.sources context.state := by
  intro name member
  have roots := report_roots context declaration bounds
  simp only [GeneralNominalRawFrame179.reportSources,List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact member
  · obtain ⟨anchor,present,rfl⟩ := List.mem_map.mp member
    exact roots.1 anchor present
  · obtain ⟨test,present,rfl⟩ := List.mem_map.mp member
    exact roots.2.1 test present
  · obtain ⟨capture,present,member⟩ := List.mem_flatMap.mp member
    obtain ⟨origin,recorded,rfl⟩ := List.mem_map.mp member
    exact roots.2.2 capture present origin (by simpa using recorded)

open GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAncestry (InstalledDepthBound)
open GeneralNominalActualTraceSupport (pool)

theorem packet_context_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      GeneralNominalState.sources packet.context.state ⊆ pool registry context root limit := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.1.2.1]
        exact (GeneralNominalCenteredEnumeration.source_pool source bound path).1
      · exact ih packet member

theorem packet_report_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets) :
    GeneralNominalRawFrame179.reportSources packet.context.state
      (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) ⊆
      pool registry context root limit :=
  fun _ present => packet_context_pool source bound path packet member
    (report_sources_subset packet.context packet.declaration packet.bounds present)

theorem fresh_outside_packet_report
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (centerPurpose : 7 ≤ purpose) :
    GeneralNominalCenters.fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.reportSources packet.context.state
        (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) :=
  fun present => GeneralNominalCenteredAllocation.outside_pool source centerPurpose
    (packet_report_pool source bound path packet member present)

end Yulang.GeneralNominalRawOrigin182
