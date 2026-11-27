import Yulang.GeneralDeclarativeI65I74MarkedCaptureTree475

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

private theorem erasePrefix {rows} (xs : List (Opened rows)) (v : Option (Traced rows)) :
    (v.map (Traced.prefix xs)).map Traced.uses = v.map Traced.uses := by
  cases v <;> rfl

private theorem eraseAppend {rows} (xs : List (Opened rows)) (a b : Option (Traced rows)) :
    ((do
      let x ← a
      let y ← b
      pure (Traced.prefix xs (x.cat y)) : Option (Traced rows))).map Traced.uses =
    (do
      let x ← a.map Traced.uses
      let y ← b.map Traced.uses
      pure (x ++ y)) := by
  cases a <;> cases b <;> rfl

private theorem eraseTail {rows} (xs : List (Opened rows)) (a : Option (Traced rows))
    (b : Option (List Occurrence)) :
    ((do
      let x ← a
      let y ← b
      pure (Traced.prefix xs (x.cat ⟨y,[]⟩)) : Option (Traced rows))).map Traced.uses =
    (do
      let x ← a.map Traced.uses
      let y ← b
      pure (x ++ y)) := by
  cases a <;> cases b <;> rfl

mutual
theorem marked_run_erases (base : GeneralDeclarativeHead320.State) (rows : List StampedRead)
    (mode : Mode) (input : Expr) (target : Node) :
    (runMarked rows mode input target).map Traced.uses = run (stampedOld base rows) mode input target := by
  cases target with
  | capture => rfl
  | primitive tag args =>
    simp only [runMarked,run,expose_erases (normal := base)]
    generalize expand (stampedOld base rows) input = raw
    cases raw <;> try rfl
    rename_i seen children
    change (if tagId seen = tagId tag then
      (runMarkedArgs rows mode children args).map (Traced.prefix (exposeStamped rows input).2) else none).map Traced.uses =
        (if tagId seen = tagId tag then runArgs (stampedOld base rows) mode children args else none)
    by_cases test : tagId seen = tagId tag
    · rw [ite_eq_left test,ite_eq_left test,erasePrefix,marked_args_erase base rows mode children args]
    · simp only [test,ite_false,Option.map_none]
  | nominal tag args =>
    simp only [runMarked,run,expose_erases (normal := base)]
    generalize expand (stampedOld base rows) input = raw
    cases raw <;> try rfl
    rename_i seen children
    change (if seen = tag then
      (runMarkedArgs rows .actual children args).map (Traced.prefix (exposeStamped rows input).2) else none).map Traced.uses =
        (if seen = tag then runArgs (stampedOld base rows) .actual children args else none)
    by_cases test : seen = tag
    · rw [ite_eq_left test,ite_eq_left test,erasePrefix,marked_args_erase base rows .actual children args]
    · simp only [test,ite_false,Option.map_none]
  | variant tag payload =>
    simp only [runMarked,run,expose_erases (normal := base)]
    generalize expand (stampedOld base rows) input = raw
    cases raw <;> try rfl
    rename_i seen child
    change (if seen = tag then
      (runMarked rows mode child payload).map (Traced.prefix (exposeStamped rows input).2) else none).map Traced.uses =
        (if seen = tag then run (stampedOld base rows) mode child payload else none)
    by_cases test : seen = tag
    · rw [ite_eq_left test,ite_eq_left test,erasePrefix,marked_run_erases base rows mode child payload]
    · simp only [test,ite_false,Option.map_none]
  | join first last =>
    simp only [runMarked,run,expose_erases (normal := base)]
    generalize expand (stampedOld base rows) input = raw
    cases raw <;> try rfl
    rename_i a b
    rw [eraseAppend,marked_run_erases base rows mode a first,marked_run_erases base rows mode b last]
  | record fields tail =>
    simp only [runMarked,run,expose_erases (normal := base)]
    split
    · change (Option.bind (literalRows (fun _ => none) (expand (stampedOld base rows) input)) _).map Traced.uses =
        Option.bind (literalRows (fun _ => none) (expand (stampedOld base rows) input)) _
      simp only [Option.map_bind]
      congr 1
      funext found
      obtain ⟨raw,last⟩ := found
      simp only
      change (Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _).map Traced.uses =
        Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _
      simp only [Option.map_bind]
      congr 1
      funext selected
      simp only [Function.comp_apply]
      rw [eraseTail,marked_fields_erase base rows mode selected fields]
    · rfl

theorem marked_args_erase (base : GeneralDeclarativeHead320.State) (rows : List StampedRead)
    (mode : Mode) (input : List Expr) (target : Nodes) :
    (runMarkedArgs rows mode input target).map Traced.uses = runArgs (stampedOld base rows) mode input target := by
  cases target with
  | nil =>
    cases input <;> rfl
  | cons first rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      simp only [runMarkedArgs,runArgs]
      change ((do
        let x ← runMarked rows mode head first
        let y ← runMarkedArgs rows mode tail rest
        pure (Traced.prefix [] (x.cat y)) : Option (Traced rows))).map Traced.uses = _
      rw [eraseAppend,marked_run_erases base rows mode head first,
        marked_args_erase base rows mode tail rest]

theorem marked_fields_erase (base : GeneralDeclarativeHead320.State) (rows : List StampedRead)
    (mode : Mode) (input : Row Expr) (target : Fields) :
    (runMarkedFields rows mode input target).map Traced.uses = runFields (stampedOld base rows) mode input target := by
  cases target with
  | nil =>
    cases input <;> rfl
  | cons key payload rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      obtain ⟨label,rhs⟩ := head
      simp only [runMarkedFields,runFields]
      split
      · change ((do
          let x ← runMarked rows mode rhs payload
          let y ← runMarkedFields rows mode tail rest
          pure (Traced.prefix [] (x.cat y)) : Option (Traced rows))).map Traced.uses = _
        rw [eraseAppend,marked_run_erases base rows mode rhs payload,
          marked_fields_erase base rows mode tail rest]
      · rfl
end

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
