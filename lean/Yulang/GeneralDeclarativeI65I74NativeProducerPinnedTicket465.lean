import Yulang.GeneralDeclarativeI65I74IndexedLogicalSource464
import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
open Yulang.GeneralDeclarativeI65 (State Origin OriginRoute Fits)
open Yulang.GeneralDeclarativeI65.I72
open Yulang.GeneralDeclarativeI65.I72.RecordTrail455
open Yulang.GeneralDeclarativeI65.I72.RecordTrail455.MixedNative456
open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeGraphRows321 (fields)
open Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.MixedQA (Address)
open Yulang.GeneralDeclarativeI65.I72.InlineStructuralPolicy458 (Ticket checks)
open Yulang.GeneralDeclarativeI65.I72.RoutedNominalPoint456 (atNominal nominalOps)

def ownerOrdinal : Ticket → Nat
  | .older (.old i) => i
  | .older (.variantInline v) => v.parent
  | .pair v => v.parent
  | .field v => v.owner
  | .nominal v => v.parent

def OwnedAt (s : Yulang.GeneralDeclarativeI65.State) (logical : Nat) (row : Equation)
    (i : Nat) : Prop :=
  ∃ o, s.origins[i]? = some o ∧ OriginRoute s o logical ∧ o.slot = row.left

private theorem named_record_owner {s logical row i}
    (h : checkRoutedOpen s logical row i = true) : OwnedAt s logical row i := by
  unfold checkRoutedOpen at h
  cases live : s.origins[i]? with
  | none => simp [checkSourceOpen,live] at h
  | some o =>
    cases endpoint : o.endpoint with
    | nominal => simp [checkSourceOpen,live,endpoint] at h
    | ordinary t =>
      have data : (o.slot = row.left ∧ closedRecordTerm t = some row.right) ∧
          checkOriginalRoute s o logical = true := by
        simpa [checkSourceOpen,live,endpoint] using h
      exact ⟨o,live,(original_route_iff_data455 ..).mp data.2,data.1.1⟩

private theorem named_pair_or_variant_owner {s logical row i}
    (h : checkAuthExtra s logical row i = true) : OwnedAt s logical row i := by
  cases live : s.origins[i]? with
  | none => simp [checkAuthExtra,live] at h
  | some o =>
    cases endpoint : o.endpoint with
    | nominal => simp [checkAuthExtra,live,endpoint] at h
    | ordinary t =>
      have data : (o.slot = row.left ∧ checkOriginalRoute s o logical = true) ∧
          checkExtra t row.right = true := by simpa [checkAuthExtra,live,endpoint] using h
      exact ⟨o,live,(original_route_iff_data455 ..).mp data.1.2,data.1.1⟩

private theorem named_nominal_owner {s logical row i}
    (h : (atNominal s logical row i).isSome = true) : OwnedAt s logical row i := by
  unfold atNominal at h
  split at h
  next =>
    split at h
    next => cases h
    next o live =>
      split at h
      next ok => exact ⟨o,live,(original_route_iff_data455 ..).mp ok.1,ok.2.1⟩
      next => cases h
  next => cases h

private theorem old_owner {s logical row i}
    (h : (nominalOps s).check logical row i = true) : OwnedAt s logical row i := by
  change ((checkRoutedOpen s logical row i || checkAuthExtra s logical row i) ||
    (atNominal s logical row i).isSome) = true at h
  rcases Bool.or_eq_true_iff.mp h with older | point
  · rcases Bool.or_eq_true_iff.mp older with record | mixed
    · exact named_record_owner record
    · exact named_pair_or_variant_owner mixed
  · exact named_nominal_owner point

private theorem inline_pair_owner {s logical row address child w}
    (ok : InlinePair458.check s logical row address child w = true) :
    OwnedAt s logical row w.parent := by
  cases pRead : s.origins[w.parent]? with
  | none => simp [InlinePair458.check,pRead,Option.bind] at ok
  | some parent =>
    cases oRead : s.origins[w.child]? with
    | none => simp [InlinePair458.check,pRead,oRead,Option.bind] at ok
    | some selected =>
      cases read : InlinePair458.readAt address parent.endpoint with
      | none => simp [InlinePair458.check,pRead,oRead,read,Option.bind] at ok
      | some term =>
        cases oTerm : InlineVariant458.readOrdinaryPayload selected.endpoint with
        | none => simp [InlinePair458.check,pRead,oRead,read,oTerm,Option.bind] at ok
        | some picked =>
          simp only [InlinePair458.check,pRead,oRead,read,oTerm,Bind.bind,Option.bind,Pure.pure,
            Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at ok
          obtain ⟨⟨⟨⟨⟨⟨⟨_,slot,_⟩,_⟩,_⟩,_⟩,parentRoute⟩,_⟩,_⟩ := ok
          exact ⟨parent,pRead,(original_route_iff_data455 ..).mp parentRoute,slot⟩

private theorem inline_record_owner {s logical row address child w}
    (h : InlineStructuralPolicy458.checkRecord s logical row address child w = true) :
    OwnedAt s logical row w.owner := by
  cases address <;> try cases h
  rename_i label
  change ClosedInlineField458.checkInlineField s logical row label child w = true at h
  cases raw : fields row.right <;> simp [ClosedInlineField458.checkInlineField,raw,Option.bind] at h
  rename_i rs
  cases lhs : s.origins[w.owner]? <;> simp [lhs] at h
  rename_i parent
  cases rhs : s.origins[w.payload]? <;> simp [rhs] at h
  rename_i payload
  cases pWords : InlineVariant458.readOrdinaryPayload parent.endpoint <;> simp [pWords] at h
  rename_i words
  cases parsed : ClosedInlineField458.authoredFields words <;> simp [parsed] at h
  rename_i src
  cases entry : src[w.fieldOrdinal]? <;> simp [entry] at h
  rename_i item
  obtain ⟨key,t⟩ := item
  cases cWords : InlineVariant458.readOrdinaryPayload payload.endpoint <;> simp [cWords] at h
  obtain ⟨⟨⟨⟨⟨_,_,_,owner,_,_⟩,_⟩,parentRoute⟩,_⟩,_⟩ := h
  exact ⟨parent,lhs,(original_route_iff_data455 ..).mp parentRoute,owner⟩

private theorem inline_nominal_owner {s logical row address child w}
    (ok : InlineNominalPoint458.check s logical row address child w = true) :
    OwnedAt s logical row w.parent := by
  cases raw : InlineNominalPoint458.readRaw row.right <;>
    simp [InlineNominalPoint458.check,raw,Option.bind] at ok
  rename_i r
  obtain ⟨key,n⟩ := r
  cases a : s.origins[w.parent]? <;> simp [a] at ok
  rename_i p
  cases b : s.origins[w.child]? <;> simp [b] at ok
  rename_i o
  cases markerRead : InlineNominalPoint458.readMarker p.endpoint <;> simp [markerRead] at ok
  rename_i query
  obtain ⟨source,t⟩ := query
  cases sourceRead : InlineVariant458.readOrdinaryPayload o.endpoint <;> simp [sourceRead] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨_,_,_,_,slot,_⟩,_⟩,_⟩,_⟩,pRoute⟩,_⟩,_⟩ := ok
  exact ⟨p,a,(original_route_iff_data455 ..).mp pRoute,slot⟩

private theorem inline_variant_owner {s logical row w}
    (h : InlineVariant458.check s logical row w = true) : OwnedAt s logical row w.parent := by
  cases raw : InlineVariant458.readRawVariant row.right with
  | none => simp [InlineVariant458.check,raw,Option.bind] at h
  | some choice =>
    rcases choice with ⟨tag,child⟩
    cases lhs : s.origins[w.parent]? with
    | none => simp [InlineVariant458.check,raw,lhs,Option.bind] at h
    | some parent =>
      cases rhs : s.origins[w.payload]? with
      | none => simp [InlineVariant458.check,raw,lhs,rhs,Option.bind] at h
      | some payload =>
        cases first : InlineVariant458.readVariantPayload parent.endpoint with
        | none => simp [InlineVariant458.check,raw,lhs,rhs,first,Option.bind] at h
        | some pair =>
          rcases pair with ⟨sourceTag,ws⟩
          cases last : InlineVariant458.readOrdinaryPayload payload.endpoint with
          | none => simp [InlineVariant458.check,raw,lhs,rhs,first,last,Option.bind] at h
          | some words =>
            simp only [InlineVariant458.check,raw,lhs,rhs,first,last,Bind.bind,Option.bind,Pure.pure,
              Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨⟨_,_,owner,_⟩,_⟩,_⟩,pRoute⟩,_⟩,_⟩ := h
            exact ⟨parent,lhs,(original_route_iff_data455 ..).mp pRoute,owner⟩

/-- Retroactively extract the precise same stored ordinal from the *given*
replaying data, not any equivalent origin found by proof existence. -/
theorem every_accepted_ticket_selects_its_literal_original_owner
    {s logical row address child} (t : Ticket)
    (ok : checks s logical row address child t = true) :
    OwnedAt s logical row (ownerOrdinal t) := by
  cases t with
  | older raw =>
    cases raw with
    | old i => exact old_owner ok
    | variantInline w =>
      have actual : (VariantInlinePolicy458.checkVariantAt row address child &&
        InlineVariant458.check s logical row w) = true := ok
      exact inline_variant_owner (Bool.and_eq_true_iff.mp actual).2
  | pair w => exact inline_pair_owner ok
  | field w => exact inline_record_owner ok
  | nominal w => exact inline_nominal_owner ok


open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarativeI65.I72.RecordTraversal455 (termInspects)
open Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.MixedQA (MixedPath readChild)
open Yulang.GeneralDeclarativeI65.I72.SplitEscape446 (splitCheck446)
open Yulang.GeneralDeclarativeGraphRows321 (shapeOf)
open Yulang.GeneralNominalCenteredHeadMatExpressions (Expr)

theorem a_real_raw_wire_uses_its_pinned_author_at_same_exact_raw_ordinal
    (s : Yulang.GeneralDeclarativeI65.State) (root : Nat) (query : Expr)
    (hop : AuthenticatedHop458.HopWire (InlineStructuralPolicy458.policy s)) (out)
    (h : AuthenticatedHop458.readStep s.current.ordinary (InlineStructuralPolicy458.policy s)
      root query hop = some out) :
    ∃ row, s.current.ordinary.equations[hop.row]? = some row ∧
      OwnedAt s root row (ownerOrdinal hop.author) := by
  cases row : s.current.ordinary.equations[hop.row]? with
  | none => simp [AuthenticatedHop458.readStep,row,Option.bind] at h
  | some r =>
    cases shape : shapeOf r.right with
    | none => simp [AuthenticatedHop458.readStep,row,shape,Option.bind] at h
    | some sh =>
      cases child : readChild hop.child sh query with
      | none => simp [AuthenticatedHop458.readStep,row,shape,child,Option.bind] at h
      | some selected =>
        by_cases pass : Yulang.GeneralDeclarativeWitnessCycle350.checksLink s.current.ordinary root r.left hop.alias = true ∧
          checks s root r selected.address selected.child hop.author = true
        · exact ⟨r,rfl,every_accepted_ticket_selects_its_literal_original_owner hop.author pass.2⟩
        · simp [AuthenticatedHop458.readStep,row,shape,child,Option.bind,InlineStructuralPolicy458.policy,
            Bool.and_eq_true,pass] at h

def pinnedOrdinals {s : Yulang.GeneralDeclarativeI65.State} {frame : Alignment} :
    JointWire (InlineStructuralPolicy458.policy s) frame → List (Nat × Nat)
  | .stop _ => []
  | .down _ hop _ rest => (hop.row,ownerOrdinal hop.author) :: pinnedOrdinals rest

/-- Performs no choice among multiple same-slot origins. Literal original
ordinal identifies the observation in the exact ticket. -/
inductive PinnedTrail (s : Yulang.GeneralDeclarativeI65.State) :
    Nat → MixedPath → List (Nat × Nat) → Prop where
  | stop : PinnedTrail s root [] []
  | down :
      (∃ row, s.current.ordinary.equations[physical]? = some row ∧
        OwnedAt s root row ordinal) →
      PinnedTrail s child rest ords →
      PinnedTrail s root ((address,child)::rest) ((physical,ordinal)::ords)

theorem a_real_joint_wire_pins_the_entire_sequence_without_unique_slot
    {s : Yulang.GeneralDeclarativeI65.State} {keys : Nat → KeyRead} {frame : Alignment}
    {w : JointWire (InlineStructuralPolicy458.policy s) frame}
    {root term code path terminal final used}
    (read : readJoint s.current.ordinary (InlineStructuralPolicy458.policy s) keys frame root term code w =
      some (path,terminal,final,used)) :
    PinnedTrail s root path (pinnedOrdinals w) := by
  induction w generalizing root term code path terminal final used with
  | stop placement =>
    by_cases yes : frame.checks root term code placement = true ∧ termInspects code = true
    · simp [readJoint,yes.1,yes.2] at read
      obtain ⟨rfl,rfl,rfl,rfl⟩ := read
      exact .stop
    · simp [readJoint,Bool.and_eq_true,yes] at read
  | down placement hop cut rest ih =>
    by_cases yes : frame.checks root term code placement = true ∧
        splitCheck446 s.current.ordinary root cut = true
    · cases first : AuthenticatedHop458.readStep s.current.ordinary
          (InlineStructuralPolicy458.policy s) root code hop with
      | none => simp [readJoint,yes.1,yes.2,first,Option.bind] at read
      | some out =>
        obtain ⟨a,c,q,one⟩ := out
        cases located : readStep (keys root) term (writtenAddress a) with
        | none => simp [readJoint,yes.1,yes.2,first,located,Option.bind] at read
        | some u =>
          cases next : readJoint s.current.ordinary
              (InlineStructuralPolicy458.policy s) keys frame c u q rest with
          | none => simp [readJoint,yes.1,yes.2,first,located,next,Option.bind] at read
          | some out =>
            obtain ⟨path',n,last,other⟩ := out
            simp [readJoint,yes.1,yes.2,first,located,next,Option.bind] at read
            obtain ⟨rfl,rfl,rfl,rfl⟩ := read
            exact .down (a_real_raw_wire_uses_its_pinned_author_at_same_exact_raw_ordinal _ _ _ _ _ first) (ih next)
    · simp [readJoint,Bool.and_eq_true,yes] at read


open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.Checker408 (Problem)
open Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
open Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463.IssuedProjection464 (logicalBeforeHop)
open Yulang.GeneralDeclarativeI65.I72.RoutedMixed456 (endsAtField)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (locateRoute)
open Yulang.GeneralDeclarativeI65.I72.RecordK2412 (checkCycleAt412)
open Yulang.GeneralDeclarationPatterns (normalize)

theorem nth_ticket_pins_raw_and_native_ordinals_at_the_same_logical_occurrence
    {s : Yulang.GeneralDeclarativeI65.State} {head path ids}
    (read : PinnedTrail s head path ids) {index raw ordinal : Nat}
    (picked : ids[index]? = some (raw,ordinal)) :
    ∃ logical row o,
      logicalBeforeHop head path index = some logical ∧
      s.current.ordinary.equations[raw]? = some row ∧ s.origins[ordinal]? = some o ∧
      OriginRoute s o logical ∧ o.slot = row.left := by
  induction read generalizing index with
  | stop => simp at picked
  | down owned rest ih =>
    cases index with
    | zero =>
      have eq := Prod.mk.inj (Option.some.inj picked)
      rcases eq with ⟨rfl,rfl⟩
      obtain ⟨row,stored,o,origin,route,slot⟩ := owned
      exact ⟨_,row,o,rfl,stored,origin,route,slot⟩
    | succ index => cases index <;> simpa [logicalBeforeHop] using ih picked

theorem field_reader_pins_shared_literal_ticket_ordinals
    {p : Problem} (tab : CheckedTable p.state.core.current)
    (w : HeadFieldWire p) (r : HeadFieldReceipt) (success : readHeadField tab w = some r) :
    ∃ a : PrecheckedHead (p := p) tab,
      a.orig.location = r.authored ∧
      PinnedTrail p.state.core a.orig.capture.lower r.path (pinnedOrdinals w.spine.visit) := by
  cases anchor : readPrecheckedHead (p := p) tab w.authored with
  | none => simp [readHeadField,anchor,Option.bind] at success
  | some a =>
    cases trail : readJoint p.state.core.current.ordinary (InlineStructuralPolicy458.policy p.state.core)
        (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.orig.capture.lower
        (normalized (readTerm a.orig.original)) a.orig.code w.spine.visit with
    | none => simp [readHeadField,anchor,trail,Option.bind] at success
    | some out =>
      obtain ⟨path,terminal,last,used⟩ := out
      by_cases yes : endsAtField path terminal = true ∧
          checkCycleAt412 p.state.core.current.ordinary terminal w.spine.cycle = true
      · have eq : ⟨a.orig.location,path,terminal,used,indexedRows w.spine.visit,
              locateRoute (fun _ => queryKeys p.state.core) a.orig.original a.orig.capture.lower path⟩ = r :=
            Option.some.inj (by simpa [readHeadField,anchor,trail,yes,Option.bind] using success)
        subst r
        exact ⟨a,rfl,a_real_joint_wire_pins_the_entire_sequence_without_unique_slot trail⟩
      · simp [readHeadField,anchor,trail,yes,Option.bind] at success


open Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeWitnessNativeValue360 (Write)
open Yulang.GeneralDeclarativeI65 (originalOfWrite)

def checkPinnedPhaseAt {s : Yulang.GeneralDeclarativeI65.State}
    (phase : CheckedPhase s) (w : Write) (head : Nat) (path : MixedPath)
    (ids : List (Nat × Nat)) (index requested : Nat) : Bool :=
  (do
    let (_raw,ordinal) ← ids[index]?
    let logical ← logicalBeforeHop head path index
    pure (decide (ordinal = requested) && checkPhaseOrigin phase w logical ordinal)).getD false

theorem phase_at_the_literal_pinned_wire_cannot_substitute_a_same_slot_origin
    {s : Yulang.GeneralDeclarativeI65.State} {head path ids}
    (pin : PinnedTrail s head path ids) (phase : CheckedPhase s) (w : Write)
    (index requested : Nat) (ok : checkPinnedPhaseAt phase w head path ids index requested = true) :
    ∃ raw logical row, ids[index]? = some (raw,requested) ∧
      logicalBeforeHop head path index = some logical ∧
      s.current.ordinary.equations[raw]? = some row ∧
      row.left = w.address.target ∧ PhaseOriginAt phase w logical requested := by
  cases h : ids[index]? with
  | none => simp [checkPinnedPhaseAt,h,Option.bind] at ok
  | some data =>
    obtain ⟨raw,original⟩ := data
    cases site : logicalBeforeHop head path index with
    | none => simp [checkPinnedPhaseAt,h,site,Option.bind] at ok
    | some logical =>
      have exactAt : original = requested ∧ PhaseOriginAt phase w logical original := by
        simpa [checkPinnedPhaseAt,h,site,Option.bind,
          finite_phase_origin_check_iff_literal_placed_active_row] using ok
      obtain ⟨rfl, released⟩ := exactAt
      obtain ⟨actual,row,o,site',physical,occupied,routed,owner⟩ :=
        nth_ticket_pins_raw_and_native_ordinals_at_the_same_logical_occurrence pin h
      have place : o = originalOfWrite w := Option.some.inj (occupied.symm.trans released.1)
      refine ⟨raw,logical,row,rfl,rfl,physical,?_ ,released⟩
      rw [←owner,place]
      rfl


def ExactSelectedPhase {s : Yulang.GeneralDeclarativeI65.State}
    (phase : CheckedPhase s) (w : Write) (head : Nat) (path : MixedPath)
    (ids : List (Nat × Nat)) (k ordinal : Nat) : Prop :=
  ∃ raw logical, ids[k]? = some (raw,ordinal) ∧
    logicalBeforeHop head path k = some logical ∧ PhaseOriginAt phase w logical ordinal

theorem pinned_phase_check_is_exact
    {s : Yulang.GeneralDeclarativeI65.State}
    (phase : CheckedPhase s) (w : Write) (head : Nat) (path : MixedPath)
    (ids : List (Nat × Nat)) (k ordinal : Nat) :
    checkPinnedPhaseAt phase w head path ids k ordinal = true ↔
    ExactSelectedPhase phase w head path ids k ordinal := by
  constructor
  · intro ok
    cases pair : ids[k]? with
    | none => simp [checkPinnedPhaseAt,pair,Option.bind] at ok
    | some both =>
      obtain ⟨raw,picked⟩ := both
      cases near : logicalBeforeHop head path k with
      | none => simp [checkPinnedPhaseAt,pair,near,Option.bind] at ok
      | some logical =>
        have tested : picked = ordinal ∧ PhaseOriginAt phase w logical picked := by
          simpa [checkPinnedPhaseAt,pair,near,Option.bind,
            finite_phase_origin_check_iff_literal_placed_active_row] using ok
        obtain ⟨rfl,exactSeen⟩ := tested
        exact ⟨raw,logical,pair,near,exactSeen⟩
  · rintro ⟨raw,logical,pair,near,exactSeen⟩
    simp [checkPinnedPhaseAt,pair,near,Option.bind,
      finite_phase_origin_check_iff_literal_placed_active_row,exactSeen]

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
