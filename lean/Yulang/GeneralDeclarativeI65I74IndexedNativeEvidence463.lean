import Yulang.GeneralDeclarativeI65I74IndexedStructuralTrail463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
open Yulang.GeneralDeclarativeI65
open WrittenPattern460
open RecordTraversal455.MixedQA (MixedPath Address ChildAt)
open RoutedInlineStructural458 (ModelOpening NewModelOpening)
open RecordTrail455 (routed_read_keeps_original_physical_owner_and_source_in_each_fit455)
open RecordTrail455.MixedNative456
open InlineStructuralPolicy458 (policy)
open RoutedNominalPoint456
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (shapeOf observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralDeclarativeK2Graph321 (Shape)

theorem existing_authorized_opening_preserves_the_very_same_raw_row
    {s : CoreState} {root row addr child stamp shape code next}
    (form : shapeOf row.right = some shape) (hop : ChildAt shape code addr child next)
    (ok : InlineStructuralPolicy458.allows s root row addr child stamp)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelOpening s m root row shape code addr child next stamp := by
  cases stamp with
  | true =>
    change InlineStructuralPolicy458.NewAuthority s root row addr child at ok
    change NewModelOpening s m root row addr child
    rcases ok with pair | field | nominal
    · exact .inl ⟨pair,InlinePair458.selected_original_payload_has_exact_same_model_native_receipt458 pair m fit⟩
    · obtain ⟨label,addr,auth⟩ := field
      exact .inr (.inl ⟨⟨label,addr,auth⟩,ClosedInlineField458.chosen_visible_field_is_the_same_native_receipt_in_every_fit458 auth m fit⟩)
    · exact .inr (.inr ⟨nominal,InlineNominalPoint458.inline_point_keeps_original_same_fit_and_declared_context458 nominal m fit⟩)
  | false =>
    obtain ⟨stamp,ok⟩ := ok
    refine ⟨stamp,?_⟩
    cases stamp with
    | true =>
      exact VariantInlinePolicy458.inline_meaning_keeps_the_same_raw_child_and_two_native_reads458
        ok.1 ok.2 m fit
    | false =>
      change (nominalOps s).allowed _ _ at ok
      rcases ok with ordinary | typed
      · left
        rcases ordinary with rec | other
        · obtain ⟨o,seen,route,owner,ty,native,rowEq⟩ :=
            routed_read_keeps_original_physical_owner_and_source_in_each_fit455 rec m fit
          exact ⟨o,seen,route,owner,ty,native,.inl rowEq⟩
        · obtain ⟨o,seen,route,owner,ty,original,equal⟩ := other
          exact ⟨o,seen,route,owner,ty,by simpa only [owner,original] using fit.2 o seen,.inr equal⟩
      · right
        obtain ⟨nominal⟩ := typed
        have actual := literal_covariant_point_child_is_only_original_ordinal456 nominal form hop
        exact ⟨nominal,(original_point_compares_in_the_same_model456 nominal m fit false).1,
          fun context => (original_point_compares_in_the_same_model456 nominal m fit context).2,form,actual⟩

inductive IndexedSourceFit (s : CoreState) (m : I72.Model) (keys : Nat → KeyRead) :
    Nat → Term → Expr → MixedPath → List Nat → Nat → Term → Bool → Prop where
  | stop : Inspects code → IndexedSourceFit s m keys root t code [] [] root t false
  | down : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) root →
      (∃ row shape, s.current.ordinary.equations[i]? = some row ∧
        GeneralDeclarativeLowerKnown321.Alias s.current.ordinary root row.left ∧
        shapeOf row.right = some shape ∧ ChildAt shape code a c next ∧
        ModelOpening s m root row shape code a c next mark) →
      Step (keys root) t (writtenAddress a) chosen →
      IndexedSourceFit s m keys c chosen next rest rows terminal last used →
      IndexedSourceFit s m keys root t code ((a,c)::rest) (i::rows) terminal last (mark || used)

theorem all_same_fits_preserve_native_proof_on_each_identical_physical_row
    {s : CoreState} {keys root t code path rows terminal last stamp}
    (route : IndexedJoint s.current.ordinary (policy s) keys root t code path rows terminal last stamp)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    IndexedSourceFit s m keys root t code path rows terminal last stamp := by
  induction route with
  | stop rigid => exact .stop rigid
  | down safe seen writes _ ih =>
    obtain ⟨row,shape,atRow,auth,form,hop,source⟩ := seen.actual
    exact .down safe ⟨row,shape,atRow,auth,form,hop,
      existing_authorized_opening_preserves_the_very_same_raw_row form hop source m fit⟩ writes ih

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
