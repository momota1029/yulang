import Yulang.GeneralDeclarativeI65I74SourceExposure481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeInlineSpine331 (Closed)

private abbrev Raw := GeneralDeclarativeHead320.State
def authored_spine_lookup_code : Expr := .primitive .emptyRecord []

def terminalBit : Expr → Bool
  | .primitive .emptyRecord [] => true
  | .primitive .exactEmpty [] => true
  | _ => false

theorem terminalBit_exact (input : Expr) : terminalBit input = true ↔ Terminal input := by
  constructor
  · intro read
    cases input <;> try cases read
    case primitive tag args =>
      cases tag <;> cases args <;> try cases read
      · exact .width
      · exact .exactEnd
  · intro endOf
    cases endOf <;> rfl

def splitLiteral : Expr → Row Expr × Expr
  | .record key value rest =>
    let (front,tail) := splitLiteral rest
    ((key,value)::front,tail)
  | term => ([],term)

theorem split_literal_assembles_exact_input (term : Expr) :
    withTail (splitLiteral term).1 (splitLiteral term).2 = term := by
  induction term using Expr.rec
    (motive_2 := fun _ => True) with
  | record key value rest _ ih => simp [splitLiteral,withTail,ih]
  | _ => first | trivial | rfl

theorem split_literal_keeps_exact_front_of_a_nonrecord_tail
    (front : Row Expr) (tail : Expr) (notRecord : ∀ k v e, tail ≠ .record k v e) :
    splitLiteral (withTail front tail) = (front,tail) := by
  induction front with
  | nil =>
    cases tail <;> try rfl
    exact False.elim (notRecord _ _ _ rfl)
  | cons one rest ih =>
    obtain ⟨key,v⟩ := one
    simp [withTail,splitLiteral,ih]

def readSpine (s : Raw) (known : Table) (name : Nat) :
    List ExposureWire → Option (Row Expr × Expr)
  | [] => none
  | current :: after => do
    let row ← readExposure s known name authored_spine_lookup_code current
    let (front,tail) := splitLiteral row.right
    match after with
    | [] => if terminalBit tail then some (front,tail) else none
    | later :: rest =>
      match tail with
      | .variable next => do
        let (suffix,finish) ← readSpine s known next (later::rest)
        pure (front ++ suffix,finish)
      | _ => none

termination_by wire => wire.length

theorem readSpine_sound (s : Raw) (known : Table) (wire : List ExposureWire) (name : Nat)
    (out : Row Expr) (endAt : Expr)
    (read : readSpine s known name wire = some (out,endAt)) :
    Spine (authoredView s known) name out endAt := by
  induction wire generalizing name out endAt with
  | nil => rw [readSpine] at read; cases read
  | cons current rest ih =>
    rw [readSpine] at read
    cases exposed : readExposure s known name authored_spine_lookup_code current with
    | none => simp [exposed,bind,Option.bind] at read
    | some row =>
      obtain ⟨_,stored,_,linked⟩ := exposure_read_reflects_literal_origin _ _ _ _ _ _ exposed
      have mem : row ∈ (authoredView s known).equations := List.mem_of_getElem? stored
      cases parts : splitLiteral row.right with
      | mk firstFields last =>
        have same : withTail firstFields last = row.right := by
          have assemble := split_literal_assembles_exact_input row.right
          rw [parts] at assemble
          exact assemble
        have stored : (⟨row.left,withTail firstFields last⟩ : Equation) ∈ (authoredView s known).equations := by
          rw [same]
          cases row
          exact mem
        cases rest with
        | nil =>
          simp only [exposed,bind,Option.bind,parts] at read
          split at read
          · rename_i b
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
            exact .inline linked ((terminalBit_exact _).mp b) stored
          · cases read
        | cons later its =>
          simp only [exposed,bind,Option.bind,parts] at read
          cases last <;> try cases read
          case «variable» next =>
            cases recursive : readSpine s known next (later::its) with
            | none => simp [recursive] at read
            | some pair =>
              obtain ⟨suffix,ends⟩ := pair
              simp only [recursive,pure] at read
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
              exact .prefixed linked stored (ih next suffix ends recursive)


private theorem record_end_is_not_record (t : Expr) (done : Terminal t) :
    ∀ k v e, t ≠ .record k v e := by
  cases done <;> intro k v e nope <;> cases nope

private theorem record_end_reifies
    {s : Raw} {table : Table} (attached : Attached s table)
    {name owner : Nat} {front : Row Expr} {tail : Expr}
    (near : GeneralDeclarativeLowerKnown321.Alias (authoredView s table) name owner)
    (done : Terminal tail)
    (present : (⟨owner,withTail front tail⟩ : Equation) ∈ (authoredView s table).equations) :
    ∃ w, readSpine s table name [w] = some (front,tail) := by
  obtain ⟨w,chosen⟩ := every_independent_authored_alias_exposure_has_finite_index_data
    (site := name) (code := authored_spine_lookup_code) attached present ((notBinder_exact _).mp rfl) near
  refine ⟨w,?_⟩
  rw [readSpine]
  simp [chosen,bind,Option.bind,split_literal_keeps_exact_front_of_a_nonrecord_tail front tail
    (record_end_is_not_record tail done),(terminalBit_exact _).mpr done]

private theorem record_name_step_reifies
    {s : Raw} {table : Table} (attached : Attached s table)
    {name owner next : Nat} {front suffix : Row Expr} {tail : Expr} {later : List ExposureWire}
    (near : GeneralDeclarativeLowerKnown321.Alias (authoredView s table) name owner)
    (present : (⟨owner,withTail front (.variable next)⟩ : Equation) ∈ (authoredView s table).equations)
    (rest : readSpine s table next later = some (suffix,tail)) :
    ∃ w, readSpine s table name (w::later) = some (front++suffix,tail) := by
  obtain ⟨w,chosen⟩ := every_independent_authored_alias_exposure_has_finite_index_data
    (site := name) (code := authored_spine_lookup_code) attached present ((notBinder_exact _).mp rfl) near
  cases later with
  | nil => rw [readSpine] at rest; cases rest
  | cons a b =>
    refine ⟨w,?_⟩
    rw [readSpine]
    simp [chosen,bind,Option.bind,split_literal_keeps_exact_front_of_a_nonrecord_tail front (.variable next)
      (by intro k v e nope; cases nope),rest]

theorem every_old_authored_closed_name_spine_has_exact_data
    {s : Raw} {table : Table} (attached : Attached s table)
    {name : Nat} {out : Row Expr} {last : Expr}
    (input : Spine (authoredView s table) name out last) :
    ∃ wire, readSpine s table name wire = some (out,last) := by
  induction input with
  | width near present =>
    obtain ⟨w,read⟩ := record_end_reifies (front := []) attached near .width present
    exact ⟨[w],read⟩
  | exactEnd near present =>
    obtain ⟨w,read⟩ := record_end_reifies (front := []) attached near .exactEnd present
    exact ⟨[w],read⟩
  | @cons name owner key field next out last near present _ ih =>
    obtain ⟨later,rest⟩ := ih
    have raw : (⟨owner,withTail [(key,.variable field)] (.variable next)⟩ : Equation) ∈
      (authoredView s table).equations := present
    obtain ⟨w,passed⟩ := record_name_step_reifies attached near raw rest
    exact ⟨w :: later,passed⟩
  | inline near terminal present =>
    obtain ⟨w,read⟩ := record_end_reifies attached near terminal present
    exact ⟨[w],read⟩
  | prefixed near present old ih =>
    obtain ⟨later,rest⟩ := ih
    obtain ⟨w,read⟩ := record_name_step_reifies attached near present rest
    exact ⟨w::later,read⟩

def readClosed (s : Raw) (table : Table) (input : Expr) (wire : List ExposureWire) :
    Option (Row Expr × Expr) :=
  match input with
  | .record label value next => (readClosed s table next wire).map
      (fun out => ((label,value)::out.1,out.2))
  | .variable name => readSpine s table name wire
  | other => if wire.isEmpty && terminalBit other then some ([],other) else none

private theorem closed_nonrecord_read (wire : List ExposureWire) (term : Expr)
    (notRecord : ∀ k v e, term ≠ .record k v e) (notVar : ∀ n, term ≠ .variable n)
    (s : Raw) (table : Table) :
    readClosed s table term wire = (if wire.isEmpty && terminalBit term then some ([],term) else none) := by
  cases term <;> try rfl
  · exact False.elim (notVar _ rfl)
  · exact False.elim (notRecord _ _ _ rfl)

theorem readClosed_sound (s : Raw) (table : Table) (input : Expr) (wire : List ExposureWire)
    (out : Row Expr) (endAt : Expr) (ok : readClosed s table input wire = some (out,endAt)) :
    Closed (authoredView s table) input out endAt := by
  induction input using Expr.rec (motive_2 := fun _ => True) generalizing out endAt with
  | «variable» label => exact readSpine_sound s table wire label out endAt ok |> Closed.name
  | record label value next _ ih =>
    rw [readClosed] at ok
    cases child : readClosed s table next wire with
    | none => simp [child] at ok
    | some row =>
      rcases row with ⟨tail,finish⟩
      simp only [child,Option.map_some] at ok
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ok)
      exact .field (ih _ _ child)
  | _ =>
    first
    | trivial
    | rw [closed_nonrecord_read _ _ (by intro k v e bad; cases bad)
        (by intro n bad; cases bad)] at ok
      split at ok
      · rename_i yes
        have endProof := (terminalBit_exact _).mp (Bool.and_eq_true_iff.mp yes).2
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ok)
        exact .terminal endProof
      · cases ok

theorem every_old_authored_closed_spine_has_exact_data
    {s : Raw} {table : Table} (attached : Attached s table)
    {input : Expr} {out : Row Expr} {endAt : Expr}
    (proper : Closed (authoredView s table) input out endAt) :
    ∃ wire, readClosed s table input wire = some (out,endAt) := by
  induction proper with
  | terminal done =>
    cases done <;> exact ⟨[],rfl⟩
  | field _ ih =>
    obtain ⟨w,got⟩ := ih
    exact ⟨w,by simp [readClosed,got]⟩
  | name named =>
    obtain ⟨w,seen⟩ := every_old_authored_closed_name_spine_has_exact_data attached named
    exact ⟨w,seen⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
