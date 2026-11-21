import Yulang.GeneralWhereOriginPartition318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralWhereOriginReady318
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginPartition318 (allClassified checked_batch)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedPacketFrame236 (headSources head_models_iff captureSources captures_iff)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)

structure HeadReady (j : Journal rs) (p : Plan rs) (m : Assignment) : Prop where
  head : HeadModels p.packet m
  input : p.input.Holds m
  captures : ∀ n, n ∈ p.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed p.packet n →
    GeneralNominalCaptureMerges.Fits m ((capture p.packet).inputs n) (m (binder p n)).1
  schema : SchemaHolds p p.headSchema m
  effects : ClassEffects j.mixed.core p.packet.site.occurrence p m

noncomputable def headGuard (j : Journal rs) (p : Plan rs) : List Nat :=
  headSources p.packet ++ siteSources p.input ++ captureSources p ++
  GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema ++
  classSources j.mixed.core p.packet.site.occurrence p

theorem headReady_frame {j : Journal rs} {p : Plan rs} {a b : Assignment}
    (same : Agree (headGuard j p) a b) (ready : HeadReady j p a) : HeadReady j p b := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (head_models_iff p.packet (fun n h => same n (by simp [headGuard,h]))).mp ready.head
  · exact (site_iff p.input (fun n h => same n (by simp [headGuard,h]))).mp ready.input
  · intro n needed
    exact (captures_iff p (fun name h => same name (by simp [headGuard,h])) n needed).mp (ready.captures n needed)
  · exact (GeneralNominalVersionedHeadFrame236.schema_iff p p.headSchema
      (fun n h => same n (by simp [headGuard,h]))).mp ready.schema
  · exact (GeneralNominalVersionedJournalFrame236.class_iff j.mixed.core p.packet.site.occurrence p
      (fun n h => same n (by simp [headGuard,h]))).mp ready.effects

/-- A passed partition extends a single model while preserving the entire
old journal and the actual current head, captures, output class and all
materialized versioned rows. Successor raw snapshots and recursive child
certificates remain separate obligations. -/
theorem preinstall_semantics {j : Journal rs} (checked : (boundary rs).Checked r)
    (trace : Trace r j) (frame : Frame (Compiled r) j.mixed.core focus key p)
    (pass : allClassified j p (headGuard j p) = true)
    (m : Assignment) (valid : Models j m) (ready : HeadReady j p m) :
    ∃ n, Models j n ∧ HeadReady j p n ∧ Agree (journalSources j ++ headGuard j p) m n ∧
      ∀ c : Cell p, c.row.Holds (variables p n) n := by
  obtain ⟨n,prior,agree,solve⟩ := checked_batch checked trace frame (headGuard j p) pass m valid
  exact ⟨n,prior,headReady_frame (fun name h => agree name (List.mem_append_right _ h)) ready,agree,solve⟩

end Yulang.GeneralWhereOriginReady318
