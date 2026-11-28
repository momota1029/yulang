import Yulang.GeneralDeclarativeI65I74AuthoredClosedSpine482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row normalize)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeInlineTrace331 (Read Args Fields TailCode)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
private abbrev ObsRaw := GeneralDeclarativeHead320.State

mutual
inductive ReadCard where
  | capture
  | expose (row : ExposureWire) (next : ReadCard)
  | primitive (next : ReadCards)
  | nominal (next : ReadCards)
  | variant (next : ReadCard)
  | join (left right : ReadCard)
  | record (spine : List ExposureWire) (keys : List Nat)
      (written : Row Expr) (endCode : Expr) (each : ReadCards) (after : ReadCard)
inductive ReadCards where
  | nil
  | cons (head : ReadCard) (rest : ReadCards)
end

def tailCodeBit : Expr → Bool
  | .variable _ => true
  | .primitive .emptyRecord [] => true
  | .primitive .exactEmpty [] => true
  | _ => false

theorem tailCodeBit_exact (code : Expr) : tailCodeBit code = true ↔ TailCode code := by
  constructor
  · intro read
    cases code <;> try cases read
    case variable.refl => exact .binder
    case primitive tag args =>
      cases tag <;> cases args <;> try cases read
      · exact .width
      · exact .exactEnd
  · intro known
    cases known <;> rfl

structure ReadRun (s : ObsRaw) (table : Table) (mode : Mode) (raw code : Expr) where
  seen : List Occurrence
  valid : Read (authoredView s table) mode raw code seen

structure ArgsRun (s : ObsRaw) (table : Table) (mode : Mode) (raw code : List Expr) where
  seen : List Occurrence
  valid : Args (authoredView s table) mode raw code seen

structure FieldsRun (s : ObsRaw) (table : Table) (mode : Mode) (raw code : Row Expr) where
  seen : List Occurrence
  valid : Fields (authoredView s table) mode raw code seen

private def checkedOption {A : Type} (o : Option A) : Option {a // o = some a} :=
  match o with
  | none => none
  | some a => some ⟨a,rfl⟩

private theorem checkedOption_is_some {A : Type} {o : Option A} {a : A}
    (read : o = some a) : checkedOption o = some ⟨a,read⟩ := by
  subst o
  rfl

mutual
def checkedRead (s : ObsRaw) (t : Table) (m : Mode) (raw code : Expr) (wire : ReadCard) :
    Option (ReadRun s t m raw code) :=
  match wire with
  | .capture =>
    match code with
    | .variable binder => some ⟨[⟨binder,m,raw⟩],.capture⟩
    | _ => none
  | .expose row next =>
    match raw with
    | .variable name => do
      let equation ← checkedOption (readExposure s t name code row)
      let after ← checkedRead s t m equation.val.right code next
      pure ⟨after.seen,one_source_exposure_reads_in_the_same_authored_view equation.property after.valid⟩
    | _ => none
  | .primitive next =>
    match raw,code with
    | .primitive f args,.primitive g query =>
      if same : f = g then by
        subst g
        exact (checkedArgs s t m args query next).map (fun got => ⟨got.seen,.primitive got.valid⟩)
      else none
    | _,_ => none
  | .nominal next =>
    match raw,code with
    | .nominal f args,.nominal g query =>
      if same : f = g then by
        subst g
        exact (checkedArgs s t .actual args query next).map (fun got => ⟨got.seen,.nominal got.valid⟩)
      else none
    | _,_ => none
  | .variant next =>
    match raw,code with
    | .variant f a,.variant g b =>
      if same : f = g then by
        subst g
        exact (checkedRead s t m a b next).map (fun got => ⟨got.seen,.variant got.valid⟩)
      else none
    | _,_ => none
  | .join left right =>
    match raw,code with
    | .join a b,.join qa qb => do
      let taken ← checkedRead s t m a qa left
      let more ← checkedRead s t m b qb right
      pure ⟨taken.seen ++ more.seen,.join taken.valid more.valid⟩
    | _,_ => none
  | .record spine keys written endCode each after =>
    if bits : keys.Nodup ∧ keys ≠ [] ∧ tailCodeBit endCode = true ∧ eqExpr code (withTail written endCode) = true then
      do
        let closed ← checkedOption (readClosed s t raw spine)
        let picked ← checkedOption (order (normalize closed.val.1) keys)
        let fields ← checkedFields s t m picked.val written each
        let tail ← checkedRead s t m (tailExpr closed.val.1 keys closed.val.2) endCode after
        pure ⟨fields.seen ++ tail.seen,((eq_expr _ _).mp bits.2.2.2).symm ▸
          Read.record (readClosed_sound s t raw spine _ _ closed.property)
            bits.1 bits.2.1 picked.property fields.valid ((tailCodeBit_exact _).mp bits.2.2.1) tail.valid⟩
    else none
termination_by structural wire

def checkedArgs (s : ObsRaw) (t : Table) (m : Mode) (raw code : List Expr) (wire : ReadCards) :
    Option (ArgsRun s t m raw code) :=
  match raw,code,wire with
  | [],[],.nil => some ⟨[],.nil⟩
  | a::as,b::bs,.cons w ws => do
    let first ← checkedRead s t m a b w
    let rest ← checkedArgs s t m as bs ws
    pure ⟨first.seen ++ rest.seen,.cons first.valid rest.valid⟩
  | _,_,_ => none
termination_by structural wire

def checkedFields (s : ObsRaw) (t : Table) (m : Mode) (raw code : Row Expr) (wire : ReadCards) :
    Option (FieldsRun s t m raw code) :=
  match raw,code,wire with
  | [],[],.nil => some ⟨[],.nil⟩
  | (key,a)::as,(same,b)::bs,.cons w ws =>
    if equal : key = same then by
      subst same
      exact do
        let first ← checkedRead s t m a b w
        let rest ← checkedFields s t m as bs ws
        pure ⟨first.seen ++ rest.seen,.cons first.valid rest.valid⟩
    else none
  | _,_,_ => none
termination_by structural wire
end

def runReadCard (s : ObsRaw) (t : Table) (m : Mode) (raw code : Expr) (w : ReadCard) :
    Option (List Occurrence) := (checkedRead s t m raw code w).map ReadRun.seen

theorem runReadCard_sound {s : ObsRaw} {t : Table} {m : Mode} {raw code : Expr} {w : ReadCard}
    {seen} (ran : runReadCard s t m raw code w = some seen) :
    Read (authoredView s t) m raw code seen := by
  cases exactRun : checkedRead s t m raw code w with
  | none => simp [runReadCard,exactRun] at ran
  | some x =>
    simp only [runReadCard,exactRun,Option.map_some,Option.some.injEq] at ran
    exact ran ▸ x.valid


private def ResultExists {P : Type} {W : Type} (run : W → Option P)
    (meaning : P → List Occurrence) (seen : List Occurrence) : Prop :=
  ∃ w value, run w = some value ∧ meaning value = seen

theorem full_c331_authored_read_has_finite_card
    {s : ObsRaw} {t : Table} (attached : Attached s t) {m : Mode} {raw code : Expr}
    {seen : List Occurrence} (theRead : Read (authoredView s t) m raw code seen) :
    ∃ wire, runReadCard s t m raw code wire = some seen := by
  have reconstructed : ResultExists (checkedRead s t m raw code) ReadRun.seen seen := by
    refine Read.rec
      (motive_1 := fun mode raw code seen _ =>
        ResultExists (checkedRead s t mode raw code) ReadRun.seen seen)
      (motive_2 := fun mode raws codes seen _ =>
        ResultExists (checkedArgs s t mode raws codes) ArgsRun.seen seen)
      (motive_3 := fun mode raws codes seen _ =>
        ResultExists (checkedFields s t mode raws codes) FieldsRun.seen seen)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ theRead
    · intro mode raw binder
      exact ⟨.capture,⟨_,.capture⟩,rfl,rfl⟩
    · intro code name owner raw seen mode notBinder near stored _ ih
      obtain ⟨row,readRow⟩ := every_independent_authored_alias_exposure_has_finite_index_data
        (row := ⟨owner,raw⟩) attached stored notBinder near
      obtain ⟨wire,got,read,seenEq⟩ := ih
      refine ⟨.expose row wire,⟨got.seen,?_⟩,?_,seenEq⟩
      · exact .expose notBinder near stored got.valid
      · simp [checkedRead,checkedOption_is_some readRow,read,bind,Option.bind,pure]
    · intro mode raw codes seen tag _ ih
      obtain ⟨wire,got,read,seenEq⟩ := ih
      exact ⟨.primitive wire,⟨got.seen,.primitive got.valid⟩,
        by simp [checkedRead,read],seenEq⟩
    · intro raw codes seen mode tag _ ih
      obtain ⟨wire,got,read,seenEq⟩ := ih
      exact ⟨.nominal wire,⟨got.seen,.nominal got.valid⟩,by simp [checkedRead,read],seenEq⟩
    · intro mode raw code seen tag _ ih
      obtain ⟨wire,got,read,seenEq⟩ := ih
      exact ⟨.variant wire,⟨got.seen,.variant got.valid⟩,by simp [checkedRead,read],seenEq⟩
    · intro mode a qa ah b qb bh _ _ left right
      obtain ⟨wl,l,ar,as_⟩ := left
      obtain ⟨wr,r,br,bs⟩ := right
      exact ⟨.join wl wr,⟨l.seen++r.seen,.join l.valid r.valid⟩,
        by simp [checkedRead,ar,br,bind,Option.bind,pure],by change l.seen ++ r.seen = _; rw [as_,bs]⟩
    · intro input raw terminal keys selected mode written first endCode last spine distinct nonempty
        selectedEq _ legalTail _ left right
      obtain ⟨rw,rawEq⟩ := every_old_authored_closed_spine_has_exact_data attached spine
      obtain ⟨wl,l,ar,as_⟩ := left
      obtain ⟨wr,r,br,bs⟩ := right
      refine ⟨.record rw keys written endCode wl wr,
        ⟨l.seen++r.seen,.record spine distinct nonempty selectedEq l.valid legalTail r.valid⟩,
        ?_,by change l.seen ++ r.seen = _; rw [as_,bs]⟩
      simp [checkedRead,distinct,nonempty,(tailCodeBit_exact _).mpr legalTail,(eq_expr _ _).mpr rfl,
        checkedOption_is_some rawEq,checkedOption_is_some selectedEq,ar,br,bind,Option.bind,pure]
    · intro mode
      exact ⟨.nil,⟨[],.nil⟩,rfl,rfl⟩
    · intro mode a b seen rest codes later _ _ left right
      obtain ⟨wl,l,ar,as_⟩ := left
      obtain ⟨wr,r,br,bs⟩ := right
      exact ⟨.cons wl wr,⟨l.seen++r.seen,.cons l.valid r.valid⟩,
        by simp [checkedArgs,ar,br,bind,Option.bind,pure],by change l.seen ++ r.seen = _; rw [as_,bs]⟩
    · intro mode
      exact ⟨.nil,⟨[],.nil⟩,rfl,rfl⟩
    · intro mode a b seen rest codes later key _ _ left right
      obtain ⟨wl,l,ar,as_⟩ := left
      obtain ⟨wr,r,br,bs⟩ := right
      exact ⟨.cons wl wr,⟨l.seen++r.seen,.cons l.valid r.valid⟩,
        by simp [checkedFields,ar,br,bind,Option.bind,pure],by change l.seen ++ r.seen = _; rw [as_,bs]⟩
  obtain ⟨w,val,ran,exactSeen⟩ := reconstructed
  exact ⟨w,by simp [runReadCard,ran,exactSeen]⟩

theorem authored_read_card_iff {s : ObsRaw} {t : Table} (attached : Attached s t)
    {m : Mode} {raw code : Expr} {seen : List Occurrence} :
    (∃ wire, runReadCard s t m raw code wire = some seen) ↔
      Read (authoredView s t) m raw code seen :=
  ⟨fun ⟨_,read⟩ => runReadCard_sound read,full_c331_authored_read_has_finite_card attached⟩


def readNamedCardRoot (s : ObsRaw) (t : Table) (name : Nat) (code : Expr) :
    ReadCard → Option (ExposureWire × Equation)
  | .expose entry _ => (readExposure s t name code entry).map (fun row => (entry,row))
  | .record (entry::_) _ _ _ _ _ =>
    (readExposure s t name (.primitive .emptyRecord []) entry).map (fun row => (entry,row))
  | _ => none

private theorem checkedOption_is_none {α : Type} {x : Option α} (nil : x = none) :
    checkedOption x = none := by
  subst x
  rfl

theorem recorded_root_is_a_real_ordinal_read
    {s : ObsRaw} {t : Table} {name : Nat} {code : Expr}
    {card : ReadCard} {w : ExposureWire} {row : Equation}
    (good : readNamedCardRoot s t name code card = some (w,row)) :
    s.equations[w.ordinals.raw]? = some row ∧ t.authored[w.ordinals.author]? = some row ∧
    GeneralDeclarativeLowerKnown321.Alias (authoredView s t) name row.left := by
  have extract {forCode : Expr} (r : readExposure s t name forCode w = some row) :
      s.equations[w.ordinals.raw]? = some row ∧ t.authored[w.ordinals.author]? = some row ∧
      GeneralDeclarativeLowerKnown321.Alias (authoredView s t) name row.left := by
    obtain ⟨a,b,_,c⟩ := exposure_read_reflects_literal_origin _ _ _ _ _ _ r
    exact ⟨a,b,c⟩
  cases card
  case expose one next =>
    simp only [readNamedCardRoot] at good
    cases localRead : readExposure s t name code one with
    | none => simp [localRead] at good
    | some actual =>
      simp only [localRead,Option.map_some,Option.some.injEq,Prod.mk.injEq] at good
      obtain ⟨rfl,rfl⟩ := good
      exact extract localRead
  case record spine keys written endCode each after =>
    cases spine with
    | nil => cases good
    | cons one rest =>
      simp only [readNamedCardRoot] at good
      cases localRead : readExposure s t name (.primitive .emptyRecord []) one with
      | none => simp [localRead] at good
      | some actual =>
        simp only [localRead,Option.map_some,Option.some.injEq,Prod.mk.injEq] at good
        obtain ⟨rfl,rfl⟩ := good
        exact extract localRead
  all_goals cases good

theorem nonbinder_read_on_a_name_exposes_a_root_ordinal
    {s : ObsRaw} {t : Table} {m : Mode} {name : Nat} {code : Expr}
    {card : ReadCard} {out : ReadRun s t m (.variable name) code}
    (notVariable : notBinder code = true)
    (ok : checkedRead s t m (.variable name) code card = some out) :
    ∃ w row, readNamedCardRoot s t name code card = some (w,row) := by
  cases card
  case capture =>
    cases code <;> simp [notBinder] at notVariable <;> cases ok
  case expose one next =>
    cases localRead : readExposure s t name code one with
    | none => simp [checkedRead,checkedOption_is_none localRead,bind,Option.bind] at ok
    | some raw =>
      exact ⟨one,raw,by simp [readNamedCardRoot,localRead]⟩
  case record rows keys written endCode each next =>
    rw [checkedRead] at ok
    split at ok
    · cases rows with
      | nil =>
        have no : readClosed s t (.variable name) [] = none := by simp [readClosed,readSpine]
        simp [checkedOption_is_none no,bind,Option.bind] at ok
      | cons w more =>
        cases exposed : readExposure s t name (.primitive .emptyRecord []) w with
        | none =>
          have no : readClosed s t (.variable name) (w::more) = none := by
            rw [readClosed,readSpine]
            simp only [show authored_spine_lookup_code = .primitive .emptyRecord [] from rfl,
              exposed,bind,Option.bind]
          simp [checkedOption_is_none no,bind,Option.bind] at ok
        | some raw =>
          exact ⟨w,raw,by simp [readNamedCardRoot,exposed]⟩
    · cases ok
  all_goals cases ok

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
