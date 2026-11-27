import Yulang.GeneralDeclarativeI65I74NativeProducerInlineBoundary465
import Yulang.GeneralDeclarativeI65I74NativeProducerScopedField465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.InlineBoundary
open Yulang.GeneralDeclarativeI65 (Origin originalOfWrite)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeGraphRows321 (shapeOf)
open PreparedDeclarations463 PhysicalVisit463
open RecordTraversal455.MixedQA (Address ChildAt)
open RecordTrail455 (RoutedOpen closedRecordTerm)
open RecordTrail455.MixedNative456
open RoutedNominalPoint456
open Checker408 (Problem)

/-- Shape of a stipulated external origin list, not an assertion that
all current origins in the repository already come from this compiler. -/
def OnlyNative360 (s : Yulang.GeneralDeclarativeI65.State) : Prop :=
  ∀ o ∈ s.origins, ∃ w : Write, originalOfWrite w = o

private theorem external_ordinary_record_author_cannot_come_from_compound_free_native360
    {s : Yulang.GeneralDeclarativeI65.State} {site : Nat} {row : Equation}
    (old : OnlyNative360 s) (reads : RoutedOpen s site row) : False := by
  obtain ⟨o,seen,_,t,_,endpoint,records⟩ := reads
  obtain ⟨w,issued⟩ := old o seen
  have proper : ∀ n, t ≠ .var n := by
    intro n wrong
    rw [wrong] at records
    cases records
  exact concrete_nonvariable_ordinary_source_is_never_native360_emission w.code t proper
    ((congrArg Origin.endpoint issued).trans endpoint)

private theorem external_ordinary_pair_or_variant_author_needs_nonvariable_original
    {s : Yulang.GeneralDeclarativeI65.State} {site : Nat} {row : Equation}
    (old : OnlyNative360 s) (reads : AuthorizedExtra s site row) : False := by
  obtain ⟨o,seen,_,_,t,endpoint,literal⟩ := reads
  obtain ⟨w,issued⟩ := old o seen
  have proper : ∀ n, t ≠ .var n := by
    intro n wrong
    rw [wrong] at literal
    cases literal
  exact concrete_nonvariable_ordinary_source_is_never_native360_emission w.code t proper
    ((congrArg Origin.endpoint issued).trans endpoint)

theorem no_existing_field_hop_uses_only_origins_in_native360_image
    {s : Yulang.GeneralDeclarativeI65.State} (old : OnlyNative360 s)
    {root code idx l child next used}
    (hop : IndexedOpen s.current.ordinary (InlineStructuralPolicy458.policy s)
      root code idx (.field l) child next used) : False := by
  obtain ⟨row,shape,_,_,actual,chosen,auth⟩ := hop.actual
  cases used with
  | true =>
    exact a_state_whose_entire_origin_list_is_emitted_by_native360_cannot_enter_inline_lanes
      s root row (.field l) child old (.inr auth)
  | false =>
    obtain ⟨stamp,h⟩ := auth
    cases stamp with
    | true =>
      exact a_state_whose_entire_origin_list_is_emitted_by_native360_cannot_enter_inline_lanes
        s root row (.field l) child old (.inl h)
    | false =>
      change (extraOpenOps s).allowed root row ∨ Nonempty (Opened s root row) at h
      rcases h with native | nominal
      · rcases native with record | extra
        · exact external_ordinary_record_author_cannot_come_from_compound_free_native360 old record
        · exact external_ordinary_pair_or_variant_author_needs_nonvariable_original old extra
      · obtain ⟨n⟩ := nominal
        have picked := n.raw
        rw [picked] at actual
        have form : GeneralDeclarativeK2Graph321.Shape.nominal n.key [n.child] = shape :=
          Option.some.inj actual
        subst shape
        cases chosen

private theorem a_trail_with_native360_only_has_no_literal_field
    {s : Yulang.GeneralDeclarativeI65.State} (only : OnlyNative360 s)
    {keys root t code path rows terminal last flag}
    (trail : IndexedJoint s.current.ordinary (InlineStructuralPolicy458.policy s)
      keys root t code path rows terminal last flag) :
    ∀ l child, (.field l,child) ∉ path := by
  induction trail with
  | stop _ => simp
  | down safe opened _ _ ih =>
    intro l c mem
    rcases List.mem_cons.mp mem with same | tail
    · obtain ⟨a,b⟩ := Prod.mk.inj same
      cases a
      exact no_existing_field_hop_uses_only_origins_in_native360_image only opened
    · exact ih l c tail

theorem no_prechecked_field_receipt_on_a_sole_native360_origin_list
    {p : Problem} (only : OnlyNative360 p.state.core)
    (table : CheckedTable p.state.core.current) (w : HeadFieldWire p) :
    readHeadField (p := p) table w = none := by
  cases result : readHeadField (p := p) table w with
  | none => rfl
  | some r =>
    exfalso
    obtain ⟨_,_,_,trail,field,_,_⟩ :=
      (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨w,result⟩
    cases last : r.path.getLast? with
    | none => simp [RoutedMixed456.endsAtField,last] at field
    | some pair =>
      rcases pair with ⟨addr,n⟩
      cases addr <;> simp [RoutedMixed456.endsAtField,last] at field
      case field l =>
        obtain ⟨prefixRows,lastRow⟩ := List.getLast?_eq_some_iff.mp last
        apply a_trail_with_native360_only_has_no_literal_field only trail l n
        rw [lastRow]
        exact List.mem_append_right _ (List.mem_singleton_self _)

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.InlineBoundary
