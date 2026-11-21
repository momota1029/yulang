import Yulang.GeneralWhereOriginSchema318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralWhereOriginAssemble318
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalCenteredHeadMatSchemas (Equation RequestsCovered emissionRequests generated_complete emitted_covered)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)
open GeneralWhereVersionCompiler317 (schema emissions allocation child)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereOriginReady318 (HeadReady headGuard headReady_frame)
open GeneralWhereOriginSchema318 (exact_schema)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereOriginPartition318 (checked_batch allClassified)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalMaterialization (rootRequests)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedExpressionFrame236 (equationSources equation_iff)

def ActualRows (p : Plan rs) (m : Assignment) : Prop :=
  ∀ row ∈ (schema p).equations, row.mode = .actual → row.Holds (variables p m) m

def actualSources (p : Plan rs) : List Nat :=
  ((schema p).equations.filter fun row => decide (row.mode = .actual)).flatMap (equationSources p)

theorem actual_transport {p : Plan rs} (same : Agree (actualSources p) a b) (held : ActualRows p a) :
    ActualRows p b := by
  intro row found mode
  have filtered : row ∈ (schema p).equations.filter (fun e => decide (e.mode = .actual)) :=
    List.mem_filter.mpr ⟨found,by simp [mode]⟩
  apply (equation_iff p row (first := a) (last := b) _).mp (held row found mode)
  intro n used
  exact same n (List.mem_flatMap.mpr ⟨row,filtered,used⟩)

theorem all_rows {p : Plan rs} (actual : ActualRows p m) (cells : ∀ c : Cell p, c.row.Holds (variables p m) m) :
    (schema p).Holds (variables p m) m := by
  intro row found
  rcases exact_schema row found with output|taut|⟨cell,rfl⟩
  · exact actual row found output
  · exact taut m
  · exact cells cell

theorem compiler_complete {p : Plan rs}
    (cover : DeclarationCovered p.packet.registry.constructors p.packet.context.interpretation p.packet.declaration) :
    (schema p).unknown = false := by
  unfold schema
  apply generated_complete
  intro request found
  rcases List.mem_append.mp found with atRoot|atChild
  · unfold rootRequests at atRoot
    obtain ⟨out,_,outMember⟩ := List.mem_flatMap.mp atRoot
    obtain ⟨equation,hit,rfl⟩ := List.mem_map.mp outMember
    exact cover.2.2 equation (List.mem_of_find?_eq_some (Option.mem_toList.mp hit))
  · obtain ⟨emission,found,req⟩ := List.mem_flatMap.mp atChild
    have perm := GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity
      p.packet.declaration p.packet.checked (capture p.packet) (allocation p)
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp (perm.mem_iff.mpr found)
    exact emitted_covered (cover.2.1 clause.val clause.property).1
      (cover.2.1 clause.val clause.property).2 _ request req

noncomputable def guard (j : Journal rs) (p : Plan rs) := headGuard j p ++ actualSources p

theorem modeled_preinstall {j : Journal rs}
    (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus key p)
    (pass : allClassified j p (guard j p) = true)
    (cover : DeclarationCovered p.packet.registry.constructors p.packet.context.interpretation p.packet.declaration)
    (m : Assignment) (valid : Models j m) (ready : HeadReady j p m) (actual : ActualRows p m) :
    ∃ n, Models j n ∧ HeadReady j p n ∧ Agree (journalSources j ++ guard j p) m n ∧
      (schema p).unknown = false ∧ (schema p).Holds (variables p n) n := by
  obtain ⟨n,prior,agree,cells⟩ := checked_batch checked trace frame (guard j p) pass m valid
  have main : Agree (guard j p) m n := fun id used => agree id (List.mem_append_right _ used)
  exact ⟨n,prior,headReady_frame (fun name h => main name (List.mem_append_left _ h)) ready,
    agree,compiler_complete cover,all_rows (actual_transport (fun name h => main name (List.mem_append_right _ h)) actual) cells⟩

end Yulang.GeneralWhereOriginAssemble318
