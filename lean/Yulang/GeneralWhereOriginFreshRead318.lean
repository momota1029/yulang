import Yulang.GeneralWhereOriginBatch318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralWhereOriginFreshRead318
open GeneralNominalIdentities (Origin source)
open GeneralNominalAllocation (origin occurrences)
open GeneralNominalVersionedFrame231 (binder capture frame)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralNominalState (sources)
open GeneralNominalCenters (Plan)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralWhereOriginBatch318 (CellOperands common)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedPlans231 (variables)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)

theorem read_capture {p : Plan rs} {k : Origin} (high : 9 < k.2.2.1)
    (outside : source p.packet.context.state.seed k ∉ sources p.packet.context.state) (name : Nat) :
    ((capture p.packet).inputs name).1 ≠ source p.packet.context.state.seed k ∧
    ((capture p.packet).inputs name).2 ≠ source p.packet.context.state.seed k := by
  have allocated (mode : Nat) (small : mode ≤ 1) :
      GeneralNominalAggregateVersion231.slot p.packet.context.state.seed
        p.packet.site.occurrence.identity p.packet.declaration.id mode name p.packet.bindings ≠
      source p.packet.context.state.seed k := by
    apply GeneralVersionedHighOrigins315.distinct
    change mode ≠ k.2.2.1
    omega
  have singleton (interval : GeneralSourceState.Interval) (one : occurrences p.packet.bindings name = [interval]) :
      interval.1 ≠ source p.packet.context.state.seed k ∧ interval.2 ≠ source p.packet.context.state.seed k := by
    have gets : interval ∈ occurrences p.packet.bindings name := one ▸ List.mem_singleton_self _
    have within := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
      name interval gets
    exact ⟨fun eq => outside (eq ▸ within.1),fun eq => outside (eq ▸ within.2)⟩
  unfold capture frame GeneralNominalVersionedAllocation231.capture
  cases rec : occurrences p.packet.bindings name with
  | nil => simpa only [rec] using And.intro (allocated 0 (by decide)) (allocated 1 (by decide))
  | cons lo rest =>
    cases rest with
    | nil => simpa only [rec] using singleton lo rec
    | cons hi tail => simpa only [rec] using And.intro (allocated 0 (by decide)) (allocated 1 (by decide))

theorem read_binder {p : Plan rs} {k : Origin} (high : 9 < k.2.2.1)
    (outside : source p.packet.context.state.seed k ∉ sources p.packet.context.state) (name : Nat) :
    binder p name ≠ source p.packet.context.state.seed k := by
  unfold binder
  split
  · change source p.packet.context.state.seed
      (origin p.packet.site.occurrence.identity p.packet.declaration.id 2 name 0) ≠ _
    apply GeneralVersionedHighOrigins315.distinct
    change (2:Nat) ≠ k.2.2.1
    omega
  · split
    · exact (read_capture high outside name).1
    · change source p.packet.context.state.seed
        (origin p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0) ≠ _
      apply GeneralVersionedHighOrigins315.distinct
      change (8:Nat) ≠ k.2.2.1
      omega

theorem read_operand {p : Plan rs} {k : Origin} (high : 9 < k.2.2.1)
    (outside : source p.packet.context.state.seed k ∉ sources p.packet.context.state) (mode) (name : Nat) :
    variableSource p mode name ≠ source p.packet.context.state.seed k := by
  unfold variableSource
  split
  · exact read_binder high outside name
  · cases mode
    · exact (read_capture high outside name).1
    · exact (read_capture high outside name).2
    · exact read_binder high outside name

theorem fresh_not_read {p : Plan rs} (c d : Cell p)
    (fresh : c.row.target ∉ sources p.packet.context.state) : c.row.target ∉ CellOperands d := by
  intro recorded
  obtain ⟨k,tag,asSource⟩ := c.high rfl
  obtain ⟨cell,_,whereAt⟩ := List.mem_map.mp recorded
  exact read_operand tag (asSource ▸ fresh) cell.1 cell.2 (whereAt.trans asSource)

/-- In a real current frame the RHS cut follows from raw absence and
the key namespace. No legacy-reachability assumption is needed:
another high endpoint can already be in raw support and be read.
It must not be one of the targets patched as fresh. -/
theorem common_without_read_assumption {j : Journal rs} (checked : (boundary rs).Checked r)
    (trace : Trace r j) (frame : Frame (Compiled r) j.mixed.core focus key p)
    (reuse fresh : List (Cell p)) (guard : List Nat)
    (preserved : ∀ c ∈ reuse, ∃ i, sourceSlot (rawOf j).base c.row.target = some i)
    (absent : ∀ c ∈ fresh, c.row.target ∉ sources (rawOf j) ∧ c.row.target ∉ journalSources j ∧
      c.row.target ∉ guard)
    (m : Assignment) (valid : Models j m) :
    ∃ n, Models j n ∧ Agree (journalSources j ++ guard) m n ∧
      (∀ c ∈ reuse ++ fresh, c.row.Holds (variables p n) n) := by
  apply common checked trace frame reuse fresh guard preserved absent _ m valid
  intro c recorded d _
  exact fresh_not_read c d (by rw [frame.context_eq]; exact (absent c recorded).1)

end Yulang.GeneralWhereOriginFreshRead318
