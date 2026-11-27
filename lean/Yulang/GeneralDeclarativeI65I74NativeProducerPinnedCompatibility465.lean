import Yulang.GeneralDeclarativeI65I74NativeProducerPinnedField465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open PreparedDeclarations463 PhysicalVisit463 WrittenPattern460
open PhysicalVisit463.IssuedProjection464 (logicalBeforeHop)
open RecordTraversal455.MixedQA (MixedPath)
open RoutedMixed456 (endsAtField)
open RecordK2412 (checkCycleAt412)

theorem taking_raw_ordinals_of_pinned_tickets_is_the_existing_projection
    {s : Yulang.GeneralDeclarativeI65.State}
    (w : JointWire (InlineStructuralPolicy458.policy s) inheritedCompilerPlacement) :
    (pinnedOrdinals w).map Prod.fst = indexedRows w := by
  induction w with
  | stop _ => rfl
  | down _ _ _ _ ih => simp [pinnedOrdinals,indexedRows,ih]

theorem successful_head_reports_have_exact_pinned_raw_row_projection
    {p : Problem} {tab : CheckedTable p.state.core.current}
    {w : HeadFieldWire p} {r : HeadFieldReceipt} (read : readHeadField (p := p) tab w = some r) :
    (pinnedOrdinals w.spine.visit).map Prod.fst = r.rows := by
  rw [taking_raw_ordinals_of_pinned_tickets_is_the_existing_projection]
  cases incoming : readPrecheckedHead (p := p) tab w.authored with
  | none => simp [readHeadField,incoming,Option.bind] at read
  | some a =>
    cases trail : readJoint p.state.core.current.ordinary (InlineStructuralPolicy458.policy p.state.core)
        (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.orig.capture.lower
        (normalized (readTerm a.orig.original)) a.orig.code w.spine.visit with
    | none => simp [readHeadField,incoming,trail,Option.bind] at read
    | some out =>
      obtain ⟨path,terminal,last,used⟩ := out
      by_cases yes : endsAtField path terminal = true ∧
          checkCycleAt412 p.state.core.current.ordinary terminal w.spine.cycle = true
      · simp [readHeadField,incoming,trail,yes,Option.bind] at read
        cases read
        rfl
      · simp [readHeadField,incoming,trail,yes,Option.bind] at read

private theorem unique_filtered_ordinal {l : List α} {b : α → Bool}
    {i j : Nat} {x y : α} (h : l[i]? = some x) (k : l[j]? = some y)
    (hx : b x = true) (hy : b y = true) (one : (l.filter b).length = 1) : i = j := by
  induction l generalizing i j with
  | nil => simp at h
  | cons a rest ih =>
    cases i <;> cases j
    · rfl
    · rename_i n
      simp only [List.getElem?_cons_zero,Option.some.injEq] at h
      simp only [List.getElem?_cons_succ] at k
      have mem : y ∈ rest.filter b := List.mem_filter.mpr ⟨List.mem_of_getElem? k,hy⟩
      have positive := List.length_pos_of_mem mem
      simp only [List.filter_cons,h,hx,ite_true,List.length_cons] at one
      omega
    · rename_i n
      simp only [List.getElem?_cons_zero,Option.some.injEq] at k
      simp only [List.getElem?_cons_succ] at h
      have mem : x ∈ rest.filter b := List.mem_filter.mpr ⟨List.mem_of_getElem? h,hx⟩
      have positive := List.length_pos_of_mem mem
      simp only [List.filter_cons,k,hy,ite_true,List.length_cons] at one
      omega
    · rename_i i j
      simp only [List.getElem?_cons_succ] at h k
      have restOne : (rest.filter b).length = 1 := by
        cases ba : b a
        · simpa [ba] using one
        · have mem : x ∈ rest.filter b := List.mem_filter.mpr ⟨List.mem_of_getElem? h,hx⟩
          have positive := List.length_pos_of_mem mem
          simp only [List.filter_cons,ba,ite_true,List.length_cons] at one
          omega
      exact congrArg Nat.succ (ih h k restOne)

theorem slot_unique_previous_phase_replays_at_the_exact_same_ticket
    {p : Problem} {phase : CheckedPhase p.state.core}
    {tab : CheckedTable p.state.core.current} {w : PhaseField p phase} {r : HeadFieldReceipt}
    (found : readSingleCandidatePhaseField tab w = some r) :
    readPinnedHeadField (phase := phase) tab ⟨w.existing,w.actual⟩ = some r := by
  by_cases one : (visible p.state.core p.root).length = 1
  · have direct : readFieldWithPhaseOwner tab w = some r := by
      simpa [readSingleCandidatePhaseField,one] using found
    obtain ⟨old,cap,logical,raw,row,args,actualLogical,atRows,atRaw,target,slotOne,exact⟩ :=
      phase_owner_reader_keeps_the_exact_existing_field_report.mp direct
    obtain ⟨a,source,trail⟩ := field_reader_pins_shared_literal_ticket_ordinals tab w.existing r old
    have aligned := a.orig.actualArgument
    rw [source] at aligned
    have capEq := Option.some.inj (args.symm.trans aligned)
    subst cap
    let ids := pinnedOrdinals w.existing.spine.visit
    have proj : ids.map Prod.fst = r.rows :=
      successful_head_reports_have_exact_pinned_raw_row_projection old
    cases kept : ids[w.actual.hop]? with
    | none =>
      have no : (ids.map Prod.fst)[w.actual.hop]? = none := by simp [List.getElem?_map,kept]
      rw [proj,atRows] at no
      contradiction
    | some pair =>
      obtain ⟨raw',native⟩ := pair
      have atIndex := congrArg (fun (l : List Nat) => l[w.actual.hop]?) proj
      have rawSame : raw' = raw := by
        simpa [List.getElem?_map,kept,atRows] using atIndex
      subst raw'
      obtain ⟨logical',row',o,near,saved,atOrigin,_routed,atSlot⟩ :=
        nth_ticket_pins_raw_and_native_ordinals_at_the_same_logical_occurrence trail kept
      have exactRow := Option.some.inj (atRaw.symm.trans saved)
      subst row'
      have index : native = w.actual.sourceOrdinal := by
        apply unique_filtered_ordinal (b := fun (o : Origin) => o.slot == row.left) atOrigin exact.1
        · simp [atSlot]
        · simp [originalOfWrite,target]
        · exact slotOne
      subst native
      apply (same_existing_report_checked_at_exact_ordinal ..).mpr
      exact ⟨old,one,a.orig.capture,args,raw,logical,kept,actualLogical,exact⟩
  · simp [readSingleCandidatePhaseField,one] at found

theorem pinned_phase_and_slot_unique_compatibility_is_exact
    {p : Problem} {phase : CheckedPhase p.state.core}
    {tab : CheckedTable p.state.core.current} (w : PhaseField p phase) (r : HeadFieldReceipt) :
    readSingleCandidatePhaseField tab w = some r ↔
      readPinnedHeadField (phase := phase) tab ⟨w.existing,w.actual⟩ = some r ∧
      (physicalOrigins p.state.core w.actual.write.address.target).length = 1 := by
  constructor
  · intro old
    refine ⟨slot_unique_previous_phase_replays_at_the_exact_same_ticket old,?_⟩
    have rel := (exact_single_candidate_phase_field_has_finite_wire ..).mpr ⟨w,rfl,old⟩
    obtain ⟨_,_,_,row,_,_,_,_,target,slotOne,_⟩ := rel.2.2
    simpa only [target] using slotOne
  · rintro ⟨same,slotOne⟩
    obtain ⟨old,one,cap,actual,selected⟩ := (same_existing_report_checked_at_exact_ordinal ..).mp same
    obtain ⟨source,whereAt,trail⟩ := field_reader_pins_shared_literal_ticket_ordinals tab w.existing r old
    have arg := source.orig.actualArgument
    rw [whereAt] at arg
    have eq := Option.some.inj (actual.symm.trans arg)
    subst cap
    have pass := (pinned_phase_check_is_exact ..).mpr selected
    obtain ⟨raw,logical,row,atPin,site,atRow,target,placed⟩ :=
      phase_at_the_literal_pinned_wire_cannot_substitute_a_same_slot_origin trail phase
        w.actual.write w.actual.hop w.actual.sourceOrdinal pass
    have rowEq := successful_head_reports_have_exact_pinned_raw_row_projection old
    have rawAt := congrArg (fun (l : List Nat) => l[w.actual.hop]?) rowEq
    have indexed : r.rows[w.actual.hop]? = some raw := by
      simpa [List.getElem?_map,atPin] using rawAt.symm
    have bind : LiteralPhaseOwnerAtHop phase r w.actual :=
      ⟨source.orig.capture,logical,raw,row,actual,site,indexed,atRow,target,target.symm ▸ slotOne,placed⟩
    have read : readFieldWithPhaseOwner tab w = some r :=
      phase_owner_reader_keeps_the_exact_existing_field_report.mpr ⟨old,bind⟩
    simpa [readSingleCandidatePhaseField,one] using read

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
