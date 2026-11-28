import Yulang.GeneralDeclarativeI65I74LocatedCaptureErasure476

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

def prependPath476 {rows} (pre : List QueryStep476) (a : LocatedCapture476 rows) :
    LocatedCapture476 rows :=
  ⟨a.uses,a.marks.map fun m => ⟨pre ++ m.path,m.exposure⟩⟩

@[simp] theorem prepend_combines476 {rows} (pre : List QueryStep476) (a b : LocatedCapture476 rows) :
    prependPath476 pre (a.combine b) = (prependPath476 pre a).combine (prependPath476 pre b) := by
  simp [prependPath476,LocatedCapture476.combine]

@[simp] theorem prepend_extends_inserted_locations476 {rows} (pre p : List QueryStep476)
    (e : List (Opened rows)) (a : LocatedCapture476 rows) :
    prependPath476 pre (LocatedCapture476.prefix p e a) =
      LocatedCapture476.prefix (pre ++ p) e (prependPath476 pre a) := by
  simp [prependPath476,LocatedCapture476.prefix,List.map_map,Function.comp_def]

private theorem opt_prepend_prefix476 {rows} (pre p : List QueryStep476)
    (e : List (Opened rows)) (a : Option (LocatedCapture476 rows)) :
    (a.map (LocatedCapture476.prefix p e)).map (prependPath476 pre) =
      (a.map (prependPath476 pre)).map (LocatedCapture476.prefix (pre ++ p) e) := by
  cases a <;> simp

private theorem opt_prepend_combine476 {rows} (pre : List QueryStep476)
    (a b : Option (LocatedCapture476 rows)) :
    ((do let x ← a; let y ← b; pure (x.combine y) :
      Option (LocatedCapture476 rows))).map (prependPath476 pre) =
      (do let x ← a.map (prependPath476 pre); let y ← b.map (prependPath476 pre); pure (x.combine y)) := by
  cases a <;> cases b <;> simp [bind,Option.bind,pure]

private theorem opt_prepend_join476 {rows} (pre p : List QueryStep476)
    (e : List (Opened rows)) (a b : Option (LocatedCapture476 rows)) :
    ((do let x ← a; let y ← b; pure (LocatedCapture476.prefix p e (x.combine y)) :
      Option (LocatedCapture476 rows))).map (prependPath476 pre) =
      (do let x ← a.map (prependPath476 pre); let y ← b.map (prependPath476 pre)
          pure (LocatedCapture476.prefix (pre ++ p) e (x.combine y))) := by
  cases a <;> cases b <;> simp [bind,Option.bind,pure]

private theorem opt_prepend_record476 {rows} (pre p : List QueryStep476)
    (e : List (Opened rows)) (a : Option (LocatedCapture476 rows)) (b : Option (List Occurrence)) :
    ((do let x ← a; let y ← b; pure (LocatedCapture476.prefix p e (x.combine ⟨y,[]⟩)) :
      Option (LocatedCapture476 rows))).map (prependPath476 pre) =
      (do let x ← a.map (prependPath476 pre); let y ← b
          pure (LocatedCapture476.prefix (pre ++ p) e (x.combine ⟨y,[]⟩))) := by
  cases a <;> cases b <;> simp only [bind,Option.bind,pure,Option.map_none,Option.map_some,prepend_extends_inserted_locations476,prepend_combines476] <;> rfl

mutual
theorem located_capture_before_any_prefix476 (rows : List StampedRead) (pre p : List QueryStep476)
    (mode : Mode) (input : Expr) (query : Node) :
    (runLocated476 rows p mode input query).map (prependPath476 pre) =
      runLocated476 rows (pre ++ p) mode input query := by
  cases query with
  | capture => rfl
  | primitive tag children =>
    simp only [runLocated476]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    by_cases test : tagId seen = tagId tag
    · simp only [test,ite_true,opt_prepend_prefix476,located_arguments_before_any_prefix476]
    · simp only [test,ite_false,Option.map_none]
  | nominal tag children =>
    simp only [runLocated476]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    by_cases test : seen = tag
    · simp only [test,ite_true,opt_prepend_prefix476,located_arguments_before_any_prefix476]
    · simp only [test,ite_false,Option.map_none]
  | variant tag child =>
    simp only [runLocated476]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    rename_i seen data
    by_cases test : seen = tag
    · simp only [test,ite_true,opt_prepend_prefix476,located_capture_before_any_prefix476,List.append_assoc]
    · simp only [test,ite_false,Option.map_none]
  | join left right =>
    simp only [runLocated476]
    generalize (exposeStamped rows input).1 = body
    cases body <;> try rfl
    dsimp only
    rw [opt_prepend_join476,located_capture_before_any_prefix476,located_capture_before_any_prefix476]
    simp only [List.append_assoc]
  | record fields edge =>
    simp only [runLocated476]
    split
    · change (Option.bind (literalRows (fun _ => none) (exposeStamped rows input).1) _).map (prependPath476 pre) =
        Option.bind (literalRows (fun _ => none) (exposeStamped rows input).1) _
      simp only [Option.map_bind]
      congr 1
      funext found
      obtain ⟨raw,last⟩ := found
      simp only
      change (Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _).map (prependPath476 pre) =
        Option.bind (order (CommonRoleCanonicalRows.normalize raw) fields.keys) _
      simp only [Option.map_bind]
      congr 1
      funext selected
      simp only [Function.comp_apply]
      rw [opt_prepend_record476,located_fields_before_any_prefix476]
    · rfl

theorem located_arguments_before_any_prefix476 (rows : List StampedRead) (pre p : List QueryStep476)
    (i : Nat) (mode : Mode) (input : List Expr) (query : Nodes) :
    (runLocatedArgs476 rows p i mode input query).map (prependPath476 pre) =
      runLocatedArgs476 rows (pre ++ p) i mode input query := by
  cases query with
  | nil => cases input <;> rfl
  | cons first rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      simp only [runLocatedArgs476]
      rw [opt_prepend_combine476,located_capture_before_any_prefix476,located_arguments_before_any_prefix476]
      simp only [List.append_assoc]

theorem located_fields_before_any_prefix476 (rows : List StampedRead) (pre p : List QueryStep476)
    (mode : Mode) (input : Row Expr) (query : Fields) :
    (runLocatedFields476 rows p mode input query).map (prependPath476 pre) =
      runLocatedFields476 rows (pre ++ p) mode input query := by
  cases query with
  | nil => cases input <;> rfl
  | cons key first rest =>
    cases input with
    | nil => rfl
    | cons head tail =>
      obtain ⟨label,value⟩ := head
      simp only [runLocatedFields476]
      split
      · rw [opt_prepend_combine476,located_capture_before_any_prefix476,located_fields_before_any_prefix476]
        simp only [List.append_assoc]
      · rfl
end

theorem every_located_mark_extends_the_exact_starting_prefix476
    {rows : List StampedRead} {p : List QueryStep476}
    {mode : Mode} {input : Expr} {query : Node} {out : LocatedCapture476 rows}
    (ok : runLocated476 rows p mode input query = some out)
    {x : LocatedMark476 rows} (inside : x ∈ out.marks) :
    ∃ tail, x.path = p ++ tail := by
  have same := located_capture_before_any_prefix476 rows p [] mode input query
  rw [List.append_nil,ok] at same
  cases he : runLocated476 rows [] mode input query with
  | none => simp [he] at same
  | some b =>
    have ob : prependPath476 p b = out := by simpa [he] using same
    rw [←ob] at inside
    change x ∈ b.marks.map (fun m => ⟨p ++ m.path,m.exposure⟩) at inside
    obtain ⟨old,_,rfl⟩ := List.mem_map.mp inside
    exact ⟨old.path,rfl⟩

theorem located_argument_mark_is_strictly_below_start476
    {rows : List StampedRead} {p : List QueryStep476} {i : Nat}
    {mode : Mode} {inputs : List Expr} {q : Nodes} {out : LocatedCapture476 rows}
    (ok : runLocatedArgs476 rows p i mode inputs q = some out)
    {x : LocatedMark476 rows} (inside : x ∈ out.marks) :
    p.length < x.path.length := by
  cases q with
  | nil =>
    cases inputs with
    | nil => cases ok; cases inside
    | cons => cases ok
  | cons a as =>
    cases inputs with
    | nil => cases ok
    | cons t ts =>
      simp only [runLocatedArgs476] at ok
      cases h0 : runLocated476 rows (p ++ [.argument i]) mode t a with
      | none => simp [h0] at ok
      | some first =>
        cases h1 : runLocatedArgs476 rows p (i+1) mode ts as with
        | none => simp [h0,h1] at ok
        | some rest =>
          have ho : first.combine rest = out := by simpa [h0,h1] using ok
          rw [←ho] at inside
          rcases List.mem_append.mp inside with h | h
          · obtain ⟨after,eq⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 h
            rw [eq]
            simp
          · exact located_argument_mark_is_strictly_below_start476 h1 h

theorem located_field_mark_is_strictly_below_start476
    {rows : List StampedRead} {p : List QueryStep476}
    {mode : Mode} {inputs : Row Expr} {q : Fields} {out : LocatedCapture476 rows}
    (ok : runLocatedFields476 rows p mode inputs q = some out)
    {x : LocatedMark476 rows} (inside : x ∈ out.marks) :
    p.length < x.path.length := by
  cases q with
  | nil =>
    cases inputs with
    | nil => cases ok; cases inside
    | cons => cases ok
  | cons k a as =>
    cases inputs with
    | nil => cases ok
    | cons entry ts =>
      obtain ⟨lab,t⟩ := entry
      simp only [runLocatedFields476] at ok
      split at ok
      · cases h0 : runLocated476 rows (p ++ [.field k]) mode t a with
        | none => simp [h0] at ok
        | some first =>
          cases h1 : runLocatedFields476 rows p mode ts as with
          | none => simp [h0,h1] at ok
          | some rest =>
            have ho : first.combine rest = out := by simpa [h0,h1] using ok
            rw [←ho] at inside
            rcases List.mem_append.mp inside with h | h
            · obtain ⟨after,eq⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 h
              rw [eq]
              simp
            · exact located_field_mark_is_strictly_below_start476 h1 h
      · cases ok


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
