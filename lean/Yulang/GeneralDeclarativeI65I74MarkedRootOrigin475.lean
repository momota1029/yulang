import Yulang.GeneralDeclarativeI65I74MarkedBeforeCapture475
import Yulang.GeneralDeclarativeI65I74BeforeCaptureField475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeNestedDecode332 (decode)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationSyntax471 (FieldOrigin readFieldOrigin ReadsDescription
  AttachedFieldWire472 gateFromAttachedAuthor472)
open WrittenPattern460.PhysicalOrigin (Pose)

def exposurePosition {rows} (item : Opened rows) : Nat × Nat × Nat :=
  (item.name,item.picked.raw,item.picked.author)

def rootExposure {rows} (answer : Traced rows) : Option (Nat × Nat × Nat) :=
  answer.opened.head?.map exposurePosition

theorem expose_from_a_known_first {rows : List StampedRead} {n : Nat} {stamp : StampedRead}
    (known : first n rows = some stamp) :
    exposeStamped rows (.variable n) = (stamp.row.right,[⟨n,stamp,known⟩]) := by
  simp only [exposeStamped]
  split
  · rename_i gone
    rw [known] at gone
    contradiction
  · rename_i got chosen
    have same := Option.some.inj (chosen.symm.trans known)
    subst got
    rfl

private theorem inline_prefix_is_root {rows : List StampedRead} {n : Nat} {stamp : StampedRead}
    (known : first n rows = some stamp) (r : Traced rows) :
    rootExposure (r.prefix [⟨n,stamp,known⟩]) = some (n,stamp.raw,stamp.author) := rfl

theorem actual_marked_nonbinder_run_starts_at_its_exact_first_source_row
    {rows : List StampedRead} {mode : Mode} {n : Nat} {stamp : StampedRead}
    {target : Node} {answer : Traced rows} (known : first n rows = some stamp)
    (nonbinder : ∀ binder, target.code ≠ .variable binder)
    (answered : runMarked rows mode (.variable n) target = some answer) :
    rootExposure answer = some (n,stamp.raw,stamp.author) := by
  have atRoot := expose_from_a_known_first known
  cases target with
  | capture key => exact (nonbinder key rfl).elim
  | primitive tag children =>
    simp only [runMarked,atRoot] at answered
    split at answered
    · split at answered
      · rename_i observed data shapeEq selection
        cases h : runMarkedArgs rows mode data children with
        | none => simp [h] at answered
        | some read =>
          simp only [h,Option.map_some,Option.some.injEq] at answered
          subst answer
          exact inline_prefix_is_root known read
      · cases answered
    · cases answered
  | nominal tag children =>
    simp only [runMarked,atRoot] at answered
    split at answered
    · split at answered
      · rename_i observed data shapeEq selection
        cases h : runMarkedArgs rows .actual data children with
        | none => simp [h] at answered
        | some read =>
          simp only [h,Option.map_some,Option.some.injEq] at answered
          subst answer
          exact inline_prefix_is_root known read
      · cases answered
    · cases answered
  | variant tag child =>
    simp only [runMarked,atRoot] at answered
    split at answered
    · split at answered
      · rename_i observed data shapeEq selection
        cases h : runMarked rows mode data child with
        | none => simp [h] at answered
        | some read =>
          simp only [h,Option.map_some,Option.some.injEq] at answered
          subst answer
          exact inline_prefix_is_root known read
      · cases answered
    · cases answered
  | join left right =>
    simp only [runMarked,atRoot] at answered
    split at answered
    · rename_i a b hit
      cases h₁ : runMarked rows mode a left with
      | none => simp [h₁,bind,Option.bind] at answered
      | some x =>
        cases h₂ : runMarked rows mode b right with
        | none => simp [h₁,h₂,bind,Option.bind] at answered
        | some y =>
          simp only [h₁,h₂,bind,Option.bind,pure,Option.some.injEq] at answered
          subst answer
          exact inline_prefix_is_root known (x.cat y)
    · cases answered
  | record fields tail =>
    simp only [runMarked,atRoot] at answered
    split at answered
    · cases h : GeneralDeclarativeNestedView332.literalRows (fun _ => none) stamp.row.right with
      | none => simp [h,bind,Option.bind] at answered
      | some entry =>
        obtain ⟨raw,last⟩ := entry
        cases c : GeneralDeclarativeOrderedRecord326.order (CommonRoleCanonicalRows.normalize raw) fields.keys with
        | none => simp [h,c,bind,Option.bind] at answered
        | some chose =>
          cases ran : runMarkedFields rows mode chose fields with
          | none => simp [h,c,ran,bind,Option.bind] at answered
          | some children =>
            cases done : GeneralDeclarativeNestedRun332.tailRun mode
                (GeneralDeclarativeRecordMaterial330.tailExpr raw fields.keys last) tail with
            | none => simp [h,c,ran,done,bind,Option.bind] at answered
            | some rest =>
              simp only [h,c,ran,done,bind,Option.bind,pure,Option.some.injEq] at answered
              subst answer
              exact inline_prefix_is_root known (children.cat ⟨rest,[]⟩)
    · cases answered

private theorem described_head_is_not_a_variable {s term label children}
    (real : ReadsDescription s term label children) : ∀ name, term ≠ .variable name := by
  cases real <;> intro name bad <;> cases bad

theorem the_first_mark_is_the_same_old_authenticated_field_owner
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) {label : Nat} {path : List Pose}
    {field : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
      ((exactFieldWire w r.picked label path).atGate a)}
    (_fieldRead : readBoundField r label path = some field)
    {answer : Traced w.offered} (good : readMarkedCapture r = some answer) :
    rootExposure answer = some (field.row.left,r.picked.raw,r.picked.author) := by
  obtain ⟨sameHead,sameRow⟩ := forwarded_old_read_uses_the_very_same_prechecked_head_and_row r label path field
  have constructor : ∀ name, r.head.orig.code ≠ .variable name :=
    sameHead ▸ described_head_is_not_a_variable field.actualHeadQuery
  unfold readMarkedCapture at good
  split at good
  · cases ready : decode r.head.orig.code with
    | none => simp [ready,bind,Option.bind] at good
    | some target =>
      simp only [ready,bind,Option.bind] at good
      have notVar : ∀ binder, target.val.code ≠ .variable binder := by
        intro n
        rw [target.property]
        exact constructor n
      have marked := actual_marked_nonbinder_run_starts_at_its_exact_first_source_row
        (first_is_exact.mpr r.firstAt) notVar good
      rw [marked,sameRow,r.firstAt.1]
  · cases good

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
