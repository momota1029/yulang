import Yulang.GeneralDeclarativeI65I74ProjectionCompilerFrame464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open PreparedDeclarations463
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

theorem batch_preserves_all_full_fits_with_independent_stored_frame
    {p : SnapshotPair} (h : ActualSuppliedBatch p.pre p.post)
    (frame : SameFitFrame p.before.state p.after.state) (m : I72.Model) :
    FitsFull p.before.state m ↔ FitsFull p.after.state m := by
  have raw := actual_supplied_batch_preserves_all_ordinary_models h m.assignment
  constructor
  · intro fit
    refine ⟨⟨⟨raw.mpr fit.1.1.1,?_⟩,?_⟩,(frame.retained m).mp fit.2⟩
    · intro row present
      exact fit.1.1.2 row (frame.visible ▸ present)
    · intro origin present
      exact fit.1.2 origin (frame.native ▸ present)
  · intro fit
    refine ⟨⟨⟨raw.mp fit.1.1.1,?_⟩,?_⟩,(frame.retained m).mpr fit.2⟩
    · intro row present
      exact fit.1.1.2 row (frame.visible ▸ present)
    · intro origin present
      exact fit.1.2 origin (frame.native ▸ present)

/-- End-to-end statement on already supplied inputs: the field result is
the original compiler occurrence, and its terminal raw K2 status already
held before. This is a receipt; it does not run before-state resolution
or add any new resolver Result case. -/
theorem checked_batch_source_and_models_are_the_same_but_raw_visit_is_post
    {p : SnapshotPair} (t : CheckedTable p.before.state.base.core.current)
    {w : ProjectionBatchWire p} {r : HeadFieldReceipt}
    (run : readProjectionBatchField p t w = some r) (cf : SameCompilerFrame p)
    (fitsFrame : SameFitFrame p.before.state p.after.state) :
    (∀ m, FitsFull p.before.state m ↔ FitsFull p.after.state m) ∧
    AliasCycle p.pre (observed p.pre) r.terminal ∧
    ∃ (old : PrecheckedHead (p := p.before.old) t) (now : PrecheckedHead (p := p.after.old) (p.afterTable t)),
      readPrecheckedHead (p := p.before.old) t r.authored = some old ∧
      old.orig.declaration = now.orig.declaration ∧
      old.orig.original = now.orig.original ∧
      old.orig.capture = now.orig.capture ∧ old.orig.code = now.orig.code := by
  have meaning := (exact_batch_field_iff_a_single_data_only_verification ..).mpr ⟨w,run⟩
  have raw := meaning.2.1.choose_spec.choose_spec.2.2.2.1
  refine ⟨batch_preserves_all_full_fits_with_independent_stored_frame meaning.1 fitsFrame,
    (GeneralDeclarativeK2Graph321.AddAtOneSource.accepted_batch_preserves_every_exact_original_k2
      meaning.1.1 _).mp raw,?_⟩
  obtain ⟨old,now,_,_,decl,orig,capture,code,run⟩ :=
    actual_batch_field_uses_the_same_prechecked_compiled_origin cf t meaning
  exact ⟨old,now,run,decl,orig,capture,code⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
