import Yulang.GeneralWhereOriginTrace318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralWhereOriginConfig318
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models)
open GeneralWhereOriginTrace318 (Trace rawOf withContext)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralWhereVersionStoredRow317 (Endpoint)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderLocations (sourceSlot)

theorem step_config {a b : Journal rs} (step : InstallStep r a b) :
    b.mixed.core.erased.current.context.interpretation = a.mixed.core.erased.current.context.interpretation ∧
    (∀ p ∈ b.versionedWhere, p ∈ a.versionedWhere ∨
      p.packet.registry = Compiled r ∧ p.packet.declaration ∈ (Compiled r).declarations) := by
  cases step with
  | whereRow ctx chosen _ frame _ _ _ same _ =>
    refine ⟨same,?_⟩
    intro p member
    rcases List.mem_append.mp member with prev|added
    · exact .inl prev
    · cases List.mem_singleton.mp added
      exact .inr ⟨frame.registry_eq,frame.visible⟩

theorem fresh_record_context {a b : Journal rs} (step : InstallStep r a b) :
    ∀ p ∈ b.versionedWhere, p ∉ a.versionedWhere →
      p.packet.context = a.mixed.core.erased.current.context := by
  cases step with
  | whereRow ctx chosen _ frame _ _ _ _ _ =>
    intro p member absent
    rcases List.mem_append.mp member with prev|added
    · exact False.elim (absent prev)
    · cases List.mem_singleton.mp added
      exact frame.context_eq

structure Config (r : Registry) (j : Journal rs) (p : Plan rs) : Prop where
  registry : p.packet.registry = Compiled r
  visible : p.packet.declaration ∈ (Compiled r).declarations
  interp : p.packet.context.interpretation = j.mixed.core.erased.current.context.interpretation
  seed : p.packet.context.state.seed = (rawOf j).seed

theorem history_config {j : Journal rs} (trace : Trace r j) (p : Plan rs) (member : p ∈ j.versionedWhere) :
    Config r j p := by
  induction trace with
  | legacy _ _ => cases member
  | @reobserve j ctx _ same layout ih =>
    have old := ih member
    exact ⟨old.registry,old.visible,old.interp.trans same.symm,old.seed.trans layout.refinement.seed.symm⟩
  | @placed j ctx plan _ step layout ih =>
    have data := step_config step
    by_cases present : p ∈ j.versionedWhere
    · have old := ih present
      exact ⟨old.registry,old.visible,old.interp.trans data.1.symm,old.seed.trans layout.refinement.seed.symm⟩
    · have cfg := (data.2 p member).resolve_left present
      have context := fresh_record_context step p member present
      exact ⟨cfg.1,cfg.2,
        (congrArg Context.interpretation context).trans data.1.symm,
        (congrArg (fun c : Context => c.state.seed) context).trans layout.refinement.seed.symm⟩

/-- Reuse is justified by an exact recorded row from the generating
rule, not by raw source membership. The old and new cells may
differ in their whole reports or Fin slot positions. -/
theorem already_holds {j : Journal rs} {p : Plan rs} {i : Fin (rawOf j).base.slots}
    (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus key p) (c : Cell p)
    (located : sourceSlot (rawOf j).base c.row.target = some i)
    (m : Assignment) (valid : Models j m) : c.row.Holds (variables p m) m := by
  have seed : (rawOf j).seed = p.packet.context.state.seed :=
    congrArg (fun c : Context => c.state.seed) frame.context_eq.symm
  obtain ⟨prior,recorded,d,sameTarget,row,typed⟩ :=
    GeneralWhereOriginTrace318.from_lookup trace located (c.high seed)
  have cfg := history_config trace prior recorded
  have sameReg := frame.registry_eq.trans cfg.registry.symm
  have agrees := (congrArg Context.interpretation frame.context_eq).trans cfg.interp.symm
  have consistent := seed.symm.trans cfg.seed.symm
  have proper := (checked_compiled checked).2
  have currentVisible : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq.symm ▸ frame.visible
  have priorVisible : prior.packet.declaration ∈ prior.packet.registry.declarations := cfg.registry.symm ▸ cfg.visible
  have proper' : GeneralDeclarations.Checked p.packet.registry := frame.registry_eq.symm ▸ proper
  exact (GeneralWhereVersionStoredRow317.same_target_iff proper' sameReg agrees consistent
    currentVisible priorVisible c.written.2 typed sameTarget.symm m).mpr ((valid.2 prior recorded).1.rows _ row)

end Yulang.GeneralWhereOriginConfig318
