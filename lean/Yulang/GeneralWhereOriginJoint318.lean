import Yulang.GeneralWhereOriginSuccessor318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralWhereOriginJoint318
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralWhereVersionCompiler317 (schema child)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereOriginReady318 (HeadReady headGuard headReady_frame)
open GeneralWhereOriginAssemble318 (ActualRows actualSources actual_transport compiler_complete all_rows)
open GeneralWhereOriginPartition318 (checked_batch allClassified)
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedExpressionFrame236 (schemaSources schema_iff)
open GeneralNominalExpressionIntervals237 (reads)

def ChildRows (p : Plan rs) (m : Assignment) : Prop :=
  ∀ c ∈ p.packet.declaration.requirements, ∀ sig : c.Signature rs,
    (childSchema p c sig).Holds (variables p m) m

def childGuard (p : Plan rs) : List Nat :=
  p.packet.declaration.requirements.attach.flatMap fun c =>
    schemaSources p (childSchema p c.val (p.packet.checked.signature.2.2.2 c.val c.property))

theorem child_rows_transport {p : Plan rs} {a b : Assignment}
    (agree : Agree (childGuard p) a b) (held : ChildRows p a) : ChildRows p b := by
  intro c listed sig
  apply (schema_iff p (childSchema p c sig) (first := a) (last := b) _).mp (held c listed sig)
  intro n seen
  exact agree n (List.mem_flatMap.mpr ⟨⟨c,listed⟩,by simp,seen⟩)

/-- The checked declaration scope is currently stated for normalized
patterns. This hypothesis is the exact raw interval-read premise
used here, and is intentionally not inferred for shadowed records. -/
def VisibleReads (p : Plan rs) : Prop :=
  ∀ c ∈ p.packet.declaration.requirements, ∀ i : Fin c.arguments.length,
    ∀ expr, translate p.packet.registry.constructors p.packet.context.interpretation c.arguments[i.val] = some expr →
      ∀ n ∈ reads expr, n ∈ p.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed p.packet n

noncomputable def guard (j : Journal rs) (p : Plan rs) :=
  headGuard j p ++ actualSources p ++ childGuard p

theorem new_certificate {j : Journal rs}
    (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus key p)
    (pass : allClassified j p (guard j p) = true)
    (cover : DeclarationCovered p.packet.registry.constructors p.packet.context.interpretation p.packet.declaration)
    (visibleReads : VisibleReads p)
    (m : Assignment) (valid : Models j m) (ready : HeadReady j p m)
    (actual : ActualRows p m) (childRows : ChildRows p m) :
    ∃ n, Models j n ∧ HeadReady j p n ∧ Holds p n ∧ Agree (journalSources j ++ guard j p) m n := by
  obtain ⟨n,prior,agree,cells⟩ := checked_batch checked trace frame (guard j p) pass m valid
  have kept : Agree (guard j p) m n := fun id used => agree id (List.mem_append_right _ used)
  have head : HeadReady j p n := headReady_frame (fun name h => kept name (by simp [guard,h])) ready
  have act := actual_transport (fun name h => kept name (by simp [guard,h])) actual
  have childRows := child_rows_transport (fun name h => kept name (by simp [guard,h])) childRows
  have rows := all_rows act cells
  refine ⟨n,prior,head,⟨head.head,head.input,head.captures,head.schema,compiler_complete cover,rows,?_⟩,agree⟩
  intro c listed sig
  have childRows := childRows c listed sig
  refine ⟨?_,childRows⟩
  intro i
  let index : Fin c.arguments.length := ⟨i.val,by rw [sig.1]; exact i.isLt⟩
  have supported := GeneralNominalCenteredHeadMatSchemas.patterns_member (cover.2.1 c listed).1
    (List.getElem_mem (l := c.arguments) (n := i.val) (by rw [sig.1]; exact i.isLt))
  obtain ⟨expr,code⟩ := GeneralNominalCenteredHeadMatExpressions.translate_complete supported
  apply GeneralWhereOriginChild318.argument_fits p n c listed sig i expr code _ rows childRows
  intro name used
  exact head.captures name (visibleReads c listed index expr code name used)

end Yulang.GeneralWhereOriginJoint318
