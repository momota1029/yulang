import Yulang.GeneralDeclarativeI65I74AuthoredFullReadMeaning482
import Yulang.GeneralDeclarativeI65I74AuthoredIssueOrder479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ArchiveValidation482
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open Producer479 (PriorPhase TypedInput)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open InputCoordinates475 (rawAt SourceIndexPair478 StampedRead recoverOldStamps478
  PairedOldRows478 ordered_old_stamp_recovery_has_independent_exact_replay478 first FirstIs first_is_exact)
open SourceExposure481 (authoredView AuthoredBranch)
open SourceExposure481.ClosedBank (ReadCard runReadCard runReadCard_sound authored_read_card_iff)

def checkOccurrences : List Occurrence → List Occurrence → Bool
  | [],[] => true
  | a::as,b::bs =>
    (a.binder == b.binder) && decide (a.mode = b.mode) && eqExpr a.term b.term && checkOccurrences as bs
  | _,_ => false

theorem checkOccurrences_exact (a b : List Occurrence) :
    checkOccurrences a b = true ↔ a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp [checkOccurrences]
  | cons first rest ih =>
    cases b with
    | nil => simp [checkOccurrences]
    | cons other more =>
      cases first
      cases other
      simp [checkOccurrences,Bool.and_eq_true,eq_expr,ih,and_assoc]

private def recordedOption {T : Type} (o : Option T) : Option {x // o = some x} :=
  match o with
  | none => none
  | some x => some ⟨x,rfl⟩

private theorem recordedOption_none {T : Type} {o : Option T} (h : o = none) :
    recordedOption o = none := by
  subst o
  rfl

private theorem recordedOption_some {T : Type} {o : Option T} {a : T} (h : o = some a) :
    recordedOption o = some ⟨a,h⟩ := by
  subst o
  rfl

/-- Project only the literal rows of an already recovered ordered typing
packet. The local card refers to this smaller table, never reissues a
native output or edits the original source ordinal table. -/
def packetView (rows : List StampedRead) : Table := ⟨rows.map StampedRead.row,[],[]⟩

structure VerifiedArchivedTyping (p : FullProblem) (basis : PriorPhase)
    (lower : Nat) (code : Expr) (root : SourceIndexPair478) (uses : List Occurrence) where
  archived : List SourceIndexPair478
  recorded : basis.recordedReads = some archived
  rows : List StampedRead
  original : PairedOldRows478 (rawAt p).equations basis.authors.authored archived rows
  firstActual : StampedRead
  headIs : FirstIs lower rows firstActual
  exactFirst : firstActual.indexPair478 = root
  realTyping : Read (authoredView (rawAt p) (packetView rows)) .actual (.variable lower) code uses

/-- Consume the original packet from the prior, not from the wire. This
is a typing archive validation, not a pass over the separate geometric
K2 visit sequence. -/
def readArchivedTyping (p : FullProblem) (basis : PriorPhase) (lower : Nat)
    (code : Expr) (root : SourceIndexPair478) (uses : List Occurrence) (card : ReadCard) :
    Option (VerifiedArchivedTyping p basis lower code root uses) := do
  let packet ← recordedOption basis.recordedReads
  let rows ← recordedOption (recoverOldStamps478 (rawAt p).equations basis.authors.authored packet.val)
  let head ← recordedOption (first lower rows.val)
  if exactRoot : head.val.indexPair478 = root then
    let result ← recordedOption (runReadCard (rawAt p) (packetView rows.val) .actual (.variable lower) code card)
    if exactUses : checkOccurrences result.val uses = true then
      let equal := (checkOccurrences_exact ..).mp exactUses
      some ⟨packet.val,packet.property,rows.val,
        ordered_old_stamp_recovery_has_independent_exact_replay478.mp rows.property,
        head.val,first_is_exact.mp head.property,exactRoot,equal ▸ runReadCard_sound result.property⟩
    else none
  else none

theorem none_when_archive_is_missing (p : FullProblem) (basis : PriorPhase)
    (absent : basis.recordedReads = none) (l : Nat) (c : Expr) (r : SourceIndexPair478)
    (u : List Occurrence) (w : ReadCard) : readArchivedTyping p basis l c r u w = none := by
  simp [readArchivedTyping,recordedOption_none absent,bind,Option.bind]

theorem packet_view_only_contains_literal_original_rows
    {p : FullProblem} {basis : PriorPhase} {packet : List SourceIndexPair478} {rows : List StampedRead}
    (read : PairedOldRows478 (rawAt p).equations basis.authors.authored packet rows) :
    Nonempty (Attached (rawAt p) (packetView rows)) := by
  refine ⟨⟨?_,?_⟩⟩
  · intro e member
    change e ∈ rows.map StampedRead.row at member
    induction read with
    | nil => cases member
    | cons _ raw _ _ ih =>
      rcases List.mem_cons.mp member with equal | later
      · exact equal ▸ List.mem_of_getElem? raw
      · exact ih later
  · intro pair present
    cases present

theorem qualified_recorded_source_has_its_own_finite_archive_checker
    {n p gd} {pos : Positions n} {rel}
    (event : TypedInput p gd pos rel) (basis : PriorPhase)
    (known : basis.ExactFor event) (authored : AuthoredBranch event)
    (packet : List SourceIndexPair478) (recorded : basis.recordedReads = some packet) :
    ∃ (head : StampedRead) (w : ReadCard),
      head.raw = event.rawOrdinal ∧
      (readArchivedTyping p basis event.head.orig.capture.lower event.head.orig.code
        head.indexPair478 event.uses w).isSome = true := by
  have exactPacket : ∃ rows : List StampedRead,
      recoverOldStamps478 (rawAt p).equations basis.authors.authored packet = some rows ∧
      (∃ start, FirstIs event.head.orig.capture.lower rows start ∧ start.raw = event.rawOrdinal) ∧
      Read ⟨(rawAt p).normal,rows.map StampedRead.row⟩ .actual
        (.variable event.head.orig.capture.lower) event.head.orig.code event.uses := by
    unfold AuthoredBranch at authored
    unfold PriorPhase.ExactFor at known
    cases which : event.backing with
    | source =>
      simp only [which] at known
      exact known.2.2.2 packet recorded
    | released => simp only [which] at authored
  obtain ⟨rows,recovery,⟨head,headIs,index⟩,real⟩ := exactPacket
  obtain ⟨view⟩ := packet_view_only_contains_literal_original_rows
    (ordered_old_stamp_recovery_has_independent_exact_replay478.mp recovery)
  obtain ⟨card,ran⟩ := (authored_read_card_iff view).mpr real
  refine ⟨head,card,index,?_⟩
  have hhead := first_is_exact.mpr headIs
  have eq : checkOccurrences event.uses event.uses = true := (checkOccurrences_exact ..).mpr rfl
  simp [readArchivedTyping,recordedOption_some recorded,recordedOption_some recovery,
    recordedOption_some hhead,recordedOption_some ran,eq,bind,Option.bind]

theorem the_archived_root_reference_is_one_of_the_literally_recovered_pairs
    {p : FullProblem} {basis : PriorPhase} {lower : Nat} {code : Expr}
    {root : SourceIndexPair478} {uses : List Occurrence}
    (out : VerifiedArchivedTyping p basis lower code root uses) :
    root ∈ out.archived := by
  have pairs := InputCoordinates475.recovery_never_reorders_original_pairs478
    (ordered_old_stamp_recovery_has_independent_exact_replay478.mpr out.original)
  have headMember : out.firstActual ∈ out.rows := by
    obtain ⟨_,pre,post,seq,_⟩ := out.headIs
    rw [seq]
    exact List.mem_append_right _ List.mem_cons_self
  rw [←pairs]
  exact List.mem_map.mpr ⟨out.firstActual,headMember,out.exactFirst⟩

theorem packet_rows_are_always_from_original_authors
    {raw authors : List GeneralDeclarativeHead320.Equation}
    {packet : List SourceIndexPair478} {rows : List StampedRead}
    (read : PairedOldRows478 raw authors packet rows) :
    rows.map StampedRead.row ⊆ authors := by
  intro row mem
  induction read with
  | nil => cases mem
  | cons _ _ author _ ih =>
    rcases List.mem_cons.mp mem with equal | tail
    · exact equal ▸ List.mem_of_getElem? author
    · exact ih tail

theorem verified_archived_typing_has_same_meaning_in_every_original_fit
    {p : FullProblem} {basis : PriorPhase} {lower : Nat} {code : Expr}
    {root : SourceIndexPair478} {uses : List Occurrence}
    {done : Nat → Prop} {source : GeneralDeclarativeOrigins321.Supported (rawAt p) done}
    (sourceAuthority : ∀ row ∈ basis.authors.authored, source.derivesFrom row .source)
    (out : VerifiedArchivedTyping p basis lower code root uses) :
    ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable lower) rebuilt) ∧
      GeneralDeclarativeTermWalk322.Walk .actual rebuilt code uses := by
  have authorized : ∀ row ∈ (packetView out.rows).authored, source.derivesFrom row .source :=
    fun row mem => sourceAuthority row (packet_rows_are_always_from_original_authors out.original mem)
  have read := SourceExposure481.genuine_authored_reads_transport_into_same_support481
    authorized out.realTyping
  obtain ⟨rebuilt,means,walk⟩ := GeneralDeclarativeInlineTrace331.realize read
  exact ⟨rebuilt,fun m fit => means m.assignment fit.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.ArchiveValidation482
