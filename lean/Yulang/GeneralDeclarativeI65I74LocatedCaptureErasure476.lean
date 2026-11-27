import Yulang.GeneralDeclarativeI65I74LocatedCaptureTree476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields)
open GeneralDeclarativeNestedRun332 (tagId tailRun)
open GeneralDeclarativeNestedView332 (literalRows)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row)

@[simp] theorem located_combine_erases {rows} (a b : LocatedCapture476 rows) :
    (a.combine b).erase = a.erase.cat b.erase := by
  simp [LocatedCapture476.combine,LocatedCapture476.erase,Traced.cat]

@[simp] theorem located_prefix_erases {rows} (p : List QueryStep476) (marks : List (Opened rows))
    (out : LocatedCapture476 rows) : (LocatedCapture476.prefix p marks out).erase = out.erase.prefix marks := by
  have m : List.map LocatedMark476.exposure (List.map (fun mark => ⟨p,mark⟩) marks) = marks := by
    induction marks <;> simp_all
  simp [LocatedCapture476.prefix,LocatedCapture476.erase,Traced.prefix,m]

private theorem marked_prefix_map {rows} (p : List QueryStep476) (marks : List (Opened rows))
    (out : Option (LocatedCapture476 rows)) :
    (out.map (LocatedCapture476.prefix p marks)).map LocatedCapture476.erase =
      (out.map LocatedCapture476.erase).map (Traced.prefix marks) := by
  cases out <;> simp

private theorem marked_combine_map {rows} (a b : Option (LocatedCapture476 rows)) :
    ((do
      let x ← a
      let y ← b
      pure (x.combine y) : Option (LocatedCapture476 rows))).map LocatedCapture476.erase =
      (do
        let x ← a.map LocatedCapture476.erase
        let y ← b.map LocatedCapture476.erase
        pure (x.cat y)) := by
  cases a <;> cases b <;> simp [bind,Option.bind,pure]

private theorem marked_guarded_combine_map {rows} (p : List QueryStep476) (e : List (Opened rows))
    (a b : Option (LocatedCapture476 rows)) :
    ((do
      let x ← a
      let y ← b
      pure (LocatedCapture476.prefix p e (x.combine y)) : Option (LocatedCapture476 rows))).map LocatedCapture476.erase =
      (do
        let x ← a.map LocatedCapture476.erase
        let y ← b.map LocatedCapture476.erase
        pure (Traced.prefix e (x.cat y))) := by
  cases a <;> cases b <;> simp [bind,Option.bind,pure]

private theorem marked_tailed_combine_map {rows} (p : List QueryStep476) (e : List (Opened rows))
    (a : Option (LocatedCapture476 rows)) (b : Option (List Occurrence)) :
    ((do
      let x ← a
      let y ← b
      pure (LocatedCapture476.prefix p e (x.combine ⟨y,[]⟩)) :
        Option (LocatedCapture476 rows))).map LocatedCapture476.erase =
      (do
        let x ← a.map LocatedCapture476.erase
        let y ← b
        pure (Traced.prefix e (x.cat ⟨y,[]⟩))) := by
  cases a <;> cases b <;> simp only [bind,Option.bind,pure,Option.map_none,Option.map_some,
    located_prefix_erases,located_combine_erases] <;> rfl

mutual
theorem located_capture_erases_all_options476 (rows : List StampedRead) (p : List QueryStep476)
    (mode : Mode) (input : Expr) (query : Node) :
    (runLocated476 rows p mode input query).map LocatedCapture476.erase =
      runMarked rows mode input query := by
  cases query with
  | capture => rfl
  | primitive tag children =>
    simp only [runLocated476,runMarked]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    change (if tagId seen = tagId tag then
        (runLocatedArgs476 rows p 0 mode data children).map
          (LocatedCapture476.prefix p (exposeStamped rows input).2) else none).map LocatedCapture476.erase =
      (if tagId seen = tagId tag then
        (runMarkedArgs rows mode data children).map (Traced.prefix (exposeStamped rows input).2) else none)
    by_cases test : tagId seen = tagId tag
    · rw [ite_eq_left test,ite_eq_left test,marked_prefix_map,located_arguments_erase_all_options476]
    · simp only [test,ite_false,Option.map_none]
  | nominal tag children =>
    simp only [runLocated476,runMarked]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    change (if seen = tag then
        (runLocatedArgs476 rows p 0 .actual data children).map
          (LocatedCapture476.prefix p (exposeStamped rows input).2) else none).map LocatedCapture476.erase =
      (if seen = tag then
        (runMarkedArgs rows .actual data children).map (Traced.prefix (exposeStamped rows input).2) else none)
    by_cases test : seen = tag
    · rw [ite_eq_left test,ite_eq_left test,marked_prefix_map,located_arguments_erase_all_options476]
    · simp only [test,ite_false,Option.map_none]
  | variant tag child =>
    simp only [runLocated476,runMarked]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    change (if seen = tag then
        (runLocated476 rows (p ++ [.variantPayload]) mode data child).map
          (LocatedCapture476.prefix p (exposeStamped rows input).2) else none).map LocatedCapture476.erase =
      (if seen = tag then
        (runMarked rows mode data child).map (Traced.prefix (exposeStamped rows input).2) else none)
    by_cases test : seen = tag
    · rw [ite_eq_left test,ite_eq_left test,marked_prefix_map,located_capture_erases_all_options476]
    · simp only [test,ite_false,Option.map_none]
  | join left right =>
    simp only [runLocated476,runMarked]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    dsimp only
    rw [marked_guarded_combine_map,located_capture_erases_all_options476,located_capture_erases_all_options476]
  | record fields edge =>
    simp only [runLocated476,runMarked]
    split
    · change (Option.bind (literalRows (fun _ => none) (exposeStamped rows input).1) _).map LocatedCapture476.erase =
        Option.bind (literalRows (fun _ => none) (exposeStamped rows input).1) _
      simp only [Option.map_bind]
      congr 1
      funext found
      obtain ⟨raw,last⟩ := found
      simp only
      change (Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _).map LocatedCapture476.erase =
        Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _
      simp only [Option.map_bind]
      congr 1
      funext selected
      simp only [Function.comp_apply]
      rw [marked_tailed_combine_map,located_fields_erase_all_options476]
    · rfl

theorem located_arguments_erase_all_options476 (rows : List StampedRead) (p : List QueryStep476)
    (i : Nat) (mode : Mode) (input : List Expr) (query : Nodes) :
    (runLocatedArgs476 rows p i mode input query).map LocatedCapture476.erase =
      runMarkedArgs rows mode input query := by
  cases query with
  | nil => cases input <;> rfl
  | cons first rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      simp only [runLocatedArgs476,runMarkedArgs]
      rw [marked_combine_map,located_capture_erases_all_options476,located_arguments_erase_all_options476]

theorem located_fields_erase_all_options476 (rows : List StampedRead) (p : List QueryStep476)
    (mode : Mode) (input : Row Expr) (query : Fields) :
    (runLocatedFields476 rows p mode input query).map LocatedCapture476.erase =
      runMarkedFields rows mode input query := by
  cases query with
  | nil => cases input <;> rfl
  | cons key first rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      obtain ⟨label,value⟩ := head
      simp only [runLocatedFields476,runMarkedFields]
      split
      · rw [marked_combine_map,located_capture_erases_all_options476,located_fields_erase_all_options476]
      · rfl
end

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
