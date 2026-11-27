import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields)
open GeneralDeclarativeNestedRun332 (run runArgs runFields tagId tailRun)
open GeneralDeclarativeNestedView332 (literalRows expand)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row)

def Agreement {rows} (xs : List (Opened rows)) (chosen : List StampedRead) : Prop :=
  ∀ e ∈ xs, first e.name chosen = some e.picked

private theorem agree_cat {rows} {a b : List (Opened rows)} {next}
    (whole : Agreement (a ++ b) next) : Agreement a next ∧ Agreement b next :=
  ⟨fun e h => whole e (List.mem_append_left _ h),fun e h => whole e (List.mem_append_right _ h)⟩

private theorem expose_replays_at_recorded_row
    (normal : GeneralDeclarativeHead320.State) {earlier next : List StampedRead} {input hit : Expr}
    (seen : (exposeStamped earlier input).1 = hit)
    (notVar : ∀ n, hit ≠ .variable n)
    (keep : Agreement (exposeStamped earlier input).2 next) :
    expand (stampedOld normal next) input = hit := by
  cases input with
  | «variable» n =>
    cases choose : first n earlier with
    | none =>
      have impossible : (exposeStamped earlier (.variable n)).1 = .variable n := by
        simp only [exposeStamped]
        split
        · rfl
        · rename_i _ eq
          rw [choose] at eq
          contradiction
      exact (notVar n (seen.symm.trans impossible)).elim
    | some source =>
      have earlier := expose_from_a_known_first choose
      rw [earlier] at keep seen
      have next : first n next = some source :=
        keep ⟨n,source,choose⟩ List.mem_cons_self
      rw [←expose_erases,expose_from_a_known_first next]
      exact seen
  | primitive | nominal | record | variant | join => exact seen

private theorem literal_spine_without_open_does_not_start_at_a_variable
    {e : Expr} {x} (listed : literalRows (fun _ => none) e = some x) :
    ∀ n, e ≠ .variable n := by
  intro n nope
  rw [nope] at listed
  cases listed

mutual
theorem replay_run_on_retained_marks (base : GeneralDeclarativeHead320.State)
    (rows next : List StampedRead) (mode : Mode) (input : Expr) (target : Node)
    (answer : Traced rows) (found : runMarked rows mode input target = some answer)
    (keep : Agreement answer.opened next) :
    run (stampedOld base next) mode input target = some answer.uses := by
  cases target with
  | capture n =>
    have same := Option.some.inj found
    subst answer
    rfl
  | primitive tag children =>
    simp only [runMarked] at found
    split at found
    · rename_i obs raw chosen
      split at found
      · rename_i matchTag
        obtain ⟨ran,reading,stamp⟩ := Option.map_eq_some_iff.mp found
        subst answer
        obtain ⟨atRoot,rest⟩ := agree_cat keep
        have child := replay_args_on_retained_marks base rows next mode raw children ran reading rest
        have expanded := expose_replays_at_recorded_row base chosen
          (fun n wrong => Expr.noConfusion wrong) atRoot
        simp [run,expanded,matchTag,child,Traced.prefix]
      · cases found
    · cases found
  | nominal tag children =>
    simp only [runMarked] at found
    split at found
    · rename_i obs raw chosen
      split at found
      · rename_i matchTag
        obtain ⟨ran,reading,stamp⟩ := Option.map_eq_some_iff.mp found
        subst answer
        obtain ⟨atRoot,rest⟩ := agree_cat keep
        have child := replay_args_on_retained_marks base rows next .actual raw children ran reading rest
        have expanded := expose_replays_at_recorded_row base chosen
          (fun n wrong => Expr.noConfusion wrong) atRoot
        simp [run,expanded,matchTag,child,Traced.prefix]
      · cases found
    · cases found
  | variant tag child =>
    simp only [runMarked] at found
    split at found
    · rename_i obs raw chosen
      split at found
      · rename_i matchTag
        obtain ⟨ran,reading,stamp⟩ := Option.map_eq_some_iff.mp found
        subst answer
        obtain ⟨atRoot,rest⟩ := agree_cat keep
        have nested := replay_run_on_retained_marks base rows next mode raw child ran reading rest
        have expanded := expose_replays_at_recorded_row base chosen
          (fun n wrong => Expr.noConfusion wrong) atRoot
        simp [run,expanded,matchTag,nested,Traced.prefix]
      · cases found
    · cases found
  | join first rest =>
    simp only [runMarked] at found
    split at found
    · rename_i a b chosen
      cases left : runMarked rows mode a first with
      | none => simp [left,bind,Option.bind] at found
      | some aRead =>
        cases right : runMarked rows mode b rest with
        | none => simp [left,right,bind,Option.bind] at found
        | some bRead =>
          simp only [left,right,bind,Option.bind,pure,Option.some.injEq] at found
          subst answer
          obtain ⟨atRoot,combined⟩ := agree_cat keep
          obtain ⟨goLeft,goRight⟩ := agree_cat combined
          have l := replay_run_on_retained_marks base rows next mode a first aRead left goLeft
          have r := replay_run_on_retained_marks base rows next mode b rest bRead right goRight
          have expanded := expose_replays_at_recorded_row base chosen
            (fun n wrong => Expr.noConfusion wrong) atRoot
          simp [run,expanded,l,r,Traced.cat,Traced.prefix,bind,Option.bind,pure]
    · cases found
  | record fields tail =>
    simp only [runMarked] at found
    split at found
    · rename_i keys
      cases spine : literalRows (fun _ => none) (exposeStamped rows input).1 with
      | none => simp [spine,bind,Option.bind] at found
      | some p =>
        obtain ⟨raw,last⟩ := p
        cases delim : order (CommonRoleCanonicalRows.normalize raw) fields.keys with
        | none => simp [spine,delim,bind,Option.bind] at found
        | some select =>
          cases reads : runMarkedFields rows mode select fields with
          | none => simp [spine,delim,reads,bind,Option.bind] at found
          | some beforeTail =>
            cases ending : tailRun mode (tailExpr raw fields.keys last) tail with
            | none => simp [spine,delim,reads,ending,bind,Option.bind] at found
            | some tailUses =>
              simp only [spine,delim,reads,ending,bind,Option.bind,pure,Option.some.injEq] at found
              subst answer
              obtain ⟨atRoot,others⟩ := agree_cat keep
              obtain ⟨covered,_⟩ := agree_cat others
              have read := replay_fields_on_retained_marks base rows next mode select fields
                beforeTail reads covered
              have expanded := expose_replays_at_recorded_row base rfl
                (literal_spine_without_open_does_not_start_at_a_variable spine) atRoot
              have noSpines : (stampedOld base next).spines = (fun _ => none) := rfl
              simp [run,expanded,keys,noSpines,spine,delim,read,ending,
                Traced.prefix,Traced.cat,bind,Option.bind,pure]
    · cases found

theorem replay_args_on_retained_marks (base : GeneralDeclarativeHead320.State)
    (rows next : List StampedRead) (mode : Mode) (input : List Expr) (target : Nodes)
    (answer : Traced rows) (found : runMarkedArgs rows mode input target = some answer)
    (keep : Agreement answer.opened next) :
    runArgs (stampedOld base next) mode input target = some answer.uses := by
  cases target with
  | nil =>
    cases input
    · have same := Option.some.inj found
      subst answer
      rfl
    · cases found
  | cons target more =>
    cases input with
    | nil => cases found
    | cons input rest =>
      simp only [runMarkedArgs] at found
      cases first : runMarked rows mode input target with
      | none => simp [first,bind,Option.bind] at found
      | some child =>
        cases later : runMarkedArgs rows mode rest more with
        | none => simp [first,later,bind,Option.bind] at found
        | some tail =>
          simp only [first,later,bind,Option.bind,pure,Option.some.injEq] at found
          subst answer
          obtain ⟨a,b⟩ := agree_cat keep
          have x := replay_run_on_retained_marks base rows next mode input target child first a
          have y := replay_args_on_retained_marks base rows next mode rest more tail later b
          simp [runArgs,x,y,Traced.cat,bind,Option.bind,pure]

theorem replay_fields_on_retained_marks (base : GeneralDeclarativeHead320.State)
    (rows next : List StampedRead) (mode : Mode) (input : Row Expr) (target : Fields)
    (answer : Traced rows) (found : runMarkedFields rows mode input target = some answer)
    (keep : Agreement answer.opened next) :
    runFields (stampedOld base next) mode input target = some answer.uses := by
  cases target with
  | nil =>
    cases input
    · have same := Option.some.inj found
      subst answer
      rfl
    · cases found
  | cons label target more =>
    cases input with
    | nil => cases found
    | cons elt rest =>
      obtain ⟨seen,input⟩ := elt
      simp only [runMarkedFields] at found
      split at found
      · rename_i key
        cases first : runMarked rows mode input target with
        | none => simp [first,bind,Option.bind] at found
        | some child =>
          cases later : runMarkedFields rows mode rest more with
          | none => simp [first,later,bind,Option.bind] at found
          | some tail =>
            simp only [first,later,bind,Option.bind,pure,Option.some.injEq] at found
            subst answer
            obtain ⟨a,b⟩ := agree_cat keep
            have x := replay_run_on_retained_marks base rows next mode input target child first a
            have y := replay_fields_on_retained_marks base rows next mode rest more tail later b
            simp [runFields,key,x,y,Traced.cat,bind,Option.bind,pure]
      · cases found
end

theorem first_is_retained_after_discarding_only_other_offered_rows
    {rows : List StampedRead} {n : Nat} {picked : StampedRead} (keep : StampedRead → Bool)
    (chosen : first n rows = some picked) (retained : keep picked = true) :
    first n (rows.filter keep) = some picked := by
  obtain ⟨matching,left,right,whole,earlier⟩ := first_is_exact.mp chosen
  refine first_is_exact.mpr ⟨matching,left.filter keep,right.filter keep,?_,?_⟩
  · simp [whole,retained]
  · intro x member
    exact earlier x (List.mem_filter.mp member).1

theorem every_recorded_mark_stays_the_same_first_when_kept
    {rows : List StampedRead} (answer : Traced rows) (keep : StampedRead → Bool)
    (stored : ∀ e ∈ answer.opened, keep e.picked = true) :
    ∀ e ∈ answer.opened, first e.name (rows.filter keep) = some e.picked :=
  fun e there => first_is_retained_after_discarding_only_other_offered_rows keep e.literalFirst (stored e there)

theorem two_marks_of_same_name_have_the_same_exact_old_rows {rows : List StampedRead}
    (a b : Opened rows) (same : a.name = b.name) : a.picked = b.picked := by
  have q := a.literalFirst
  rw [same] at q
  exact Option.some.inj (q.symm.trans b.literalFirst)

def keepOpened {rows : List StampedRead} (answer : Traced rows) (item : StampedRead) : Bool :=
  answer.opened.any fun e => e.picked.raw == item.raw && e.picked.author == item.author

theorem keep_only_actual_opened_ordinal_pairs_retains_each_mark
    {rows : List StampedRead} (answer : Traced rows) :
    ∀ e ∈ answer.opened, first e.name (rows.filter (keepOpened answer)) = some e.picked := by
  apply every_recorded_mark_stays_the_same_first_when_kept
  intro e member
  apply List.any_eq_true.mpr
  exact ⟨e,member,by simp⟩


theorem deleting_all_unread_offered_coordinates_preserves_the_old_capture
    (base : GeneralDeclarativeHead320.State) {rows : List StampedRead}
    {mode : Mode} {input : Expr} {target : Node} {answer : Traced rows}
    (got : runMarked rows mode input target = some answer) :
    run (stampedOld base (rows.filter (keepOpened answer))) mode input target =
      some answer.uses :=
  replay_run_on_retained_marks base rows _ mode input target answer got
    (keep_only_actual_opened_ordinal_pairs_retains_each_mark answer)

theorem deleting_all_unread_offered_coordinates_preserves_the_old_typing_derivation
    (base : GeneralDeclarativeHead320.State) {rows : List StampedRead}
    {mode : Mode} {input : Expr} {target : Node} {answer : Traced rows}
    (got : runMarked rows mode input target = some answer) :
    GeneralDeclarativeInlineTrace331.Read (stampedView base (rows.filter (keepOpened answer)))
      mode input target.code answer.uses :=
  GeneralDeclarativeNestedSound332.sound _ _
    (deleting_all_unread_offered_coordinates_preserves_the_old_capture base got)


open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeNestedDecode332 (decode)

theorem filtering_the_supplied_source_view_preserves_both_ordinal_tables
    {raw authored : List GeneralDeclarativeHead320.Equation} {rows : List StampedRead}
    (ok : valid raw authored rows = true) (keep : StampedRead → Bool) :
    valid raw authored (rows.filter keep) = true := by
  obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp ok
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkedSubsequence_exact.mpr
    intro pair there
    obtain ⟨item,inside,rfl⟩ := List.mem_map.mp there
    exact checkedSubsequence_exact.mp left _
      (List.mem_map.mpr ⟨item,(List.mem_filter.mp inside).1,rfl⟩)
  · apply checkedSubsequence_exact.mpr
    intro pair there
    obtain ⟨item,inside,rfl⟩ := List.mem_map.mp there
    exact checkedSubsequence_exact.mp right _
      (List.mem_map.mpr ⟨item,(List.mem_filter.mp inside).1,rfl⟩)

def clippedWire (w : BeforeCaptureWire) (trace : Traced w.offered) : BeforeCaptureWire :=
  { w with offered := w.offered.filter (keepOpened trace) }

theorem clipped_before_open_replays_when_root_is_actually_marked
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (trace : Traced w.offered)
    (selected : rootExposure trace = some (r.head.orig.capture.lower,r.picked.raw,r.picked.author)) :
    ∃ shorter : BeforeCapture a gd (clippedWire w trace),
      readBeforeCapture a gd (clippedWire w trace) = some shorter ∧
      shorter.head = r.head ∧ shorter.picked = r.picked := by
  have present : keepOpened trace r.picked = true := by
    unfold rootExposure at selected
    cases h : trace.opened with
    | nil => simp [h] at selected
    | cons first rest =>
      have addr : exposurePosition first = (r.head.orig.capture.lower,r.picked.raw,r.picked.author) := by
        exact Option.some.inj (by simpa [h] using selected)
      have places : first.picked.raw = r.picked.raw ∧ first.picked.author = r.picked.author :=
        ⟨congrArg (fun x => x.2.1) addr,congrArg (fun x => x.2.2) addr⟩
      unfold keepOpened
      exact List.any_eq_true.mpr ⟨first,h ▸ List.mem_cons_self,by simp [places.1,places.2]⟩
  let shorter : BeforeCapture a gd (clippedWire w trace) :=
    ⟨r.head,r.address,r.visibleOnce,r.frame,
     filtering_the_supplied_source_view_preserves_both_ordinal_tables r.checked _,
     r.picked,first_is_exact.mp
       (first_is_retained_after_discarding_only_other_offered_rows _ (first_is_exact.mpr r.firstAt) present)⟩
  exact ⟨shorter,exact_before_capture_replays shorter,rfl,rfl⟩

theorem old_quoted_run_is_exact_after_clipping_unvisited_offered_rows
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) {trace : Traced w.offered}
    (hit : readMarkedCapture r = some trace) :
    (decode r.head.orig.code).bind
      (fun d => run (oldInputIndex p (clippedWire w trace))
        .actual (.variable r.head.orig.capture.lower) d.val) = some trace.uses := by
  unfold readMarkedCapture at hit
  split at hit
  · cases d : decode r.head.orig.code with
    | none => simp [d,bind,Option.bind] at hit
    | some d =>
      simp only [d,bind,Option.bind] at *
      exact deleting_all_unread_offered_coordinates_preserves_the_old_capture (rawAt p) hit
  · cases hit



theorem actual_field_and_legacy_capture_replay_without_unvisited_offered_rows
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) {label : Nat} {path : List WrittenPattern460.PhysicalOrigin.Pose}
    {f} (field : readBoundField r label path = some f)
    {trace : Traced w.offered} (found : readMarkedCapture r = some trace) :
    ∃ next : BeforeCapture a gd (clippedWire w trace),
      readBeforeCapture a gd (clippedWire w trace) = some next ∧
      next.head = r.head ∧
      exactFieldWire (clippedWire w trace) next.picked label path =
        exactFieldWire w r.picked label path ∧
      (runAtBeforeCapture next).map PinnedCapture.uses = some trace.uses := by
  have mark := the_first_mark_is_the_same_old_authenticated_field_owner r field found
  have exactRow := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row r label path f).2
  rw [exactRow,r.firstAt.1] at mark
  obtain ⟨next,replayed,headSame,ownerSame⟩ :=
    clipped_before_open_replays_when_root_is_actually_marked r trace mark
  have codeOkay : legacyCodeMatches p r.head.orig = true := by
    by_cases codeOkay : legacyCodeMatches p r.head.orig = true
    · exact codeOkay
    · simp [readMarkedCapture,codeOkay] at found
  have legacy := (legacy_code_matches_exact ..).mp codeOkay
  have shorter : actualLegacyQuery p (GeneralDeclarationPatterns.normalize next.head.orig.original) =
      some next.head.orig.code := by simpa only [headSame] using legacy
  have executed := exact_old_capture_output_after_erasing_checked_stamp next shorter
  refine ⟨next,replayed,headSame,?_,?_⟩
  · simp [exactFieldWire,clippedWire,ownerSame]
  · rw [executed,headSame]
    exact old_quoted_run_is_exact_after_clipping_unvisited_offered_rows r found


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
