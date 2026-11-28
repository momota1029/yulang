import Yulang.GeneralDeclarativeI65I74LocatedPathPrefix477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields)
open GeneralDeclarativeNestedRun332 (tagId tailRun)
open GeneralDeclarativeNestedView332 (literalRows)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row)

private theorem next_step_eq477 {p after other : List QueryStep476} {k l : QueryStep476}
    (h : (p ++ [k]) ++ after = (p ++ [l]) ++ other) :
    k = l := by
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h
  exact (List.cons.inj (List.append_cancel_left h)).1

private theorem path_of_argument477 {rows p i mode raw q out}
    (ok : runLocatedArgs476 rows p i mode raw q = some out)
    {m : LocatedMark476 rows} (mem : m ∈ out.marks) :
    ∃ j after, i ≤ j ∧ m.path = (p ++ [.argument j]) ++ after := by
  cases q with
  | nil => cases raw <;> cases ok; cases mem
  | cons a as =>
    cases raw with
    | nil => cases ok
    | cons e es =>
      simp only [runLocatedArgs476] at ok
      cases h0 : runLocated476 rows (p ++ [.argument i]) mode e a with
      | none => simp [h0] at ok
      | some first =>
        cases h1 : runLocatedArgs476 rows p (i+1) mode es as with
        | none => simp [h0,h1] at ok
        | some rest =>
          have eq : first.combine rest = out := by simpa [h0,h1] using ok
          rw [←eq] at mem
          rcases List.mem_append.mp mem with h | h
          · obtain ⟨after,he⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 h
            exact ⟨i,after,by omega,he⟩
          · obtain ⟨j,after,hj,he⟩ := path_of_argument477 h1 h
            exact ⟨j,after,by omega,he⟩

private theorem path_of_field477 {rows p mode raw q out}
    (ok : runLocatedFields476 rows p mode raw q = some out)
    {m : LocatedMark476 rows} (mem : m ∈ out.marks) :
    ∃ j after, j ∈ q.keys ∧ m.path = (p ++ [.field j]) ++ after := by
  cases q with
  | nil => cases raw <;> cases ok; cases mem
  | cons k a as =>
    cases raw with
    | nil => cases ok
    | cons entry es =>
      obtain ⟨l,e⟩ := entry
      simp only [runLocatedFields476] at ok
      split at ok
      · cases h0 : runLocated476 rows (p ++ [.field k]) mode e a with
        | none => simp [h0] at ok
        | some first =>
          cases h1 : runLocatedFields476 rows p mode es as with
          | none => simp [h0,h1] at ok
          | some rest =>
            have eq : first.combine rest = out := by simpa [h0,h1] using ok
            rw [←eq] at mem
            rcases List.mem_append.mp mem with h | h
            · obtain ⟨after,he⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 h
              exact ⟨k,after,by change k ∈ k::as.keys; simp,he⟩
            · obtain ⟨j,after,hj,he⟩ := path_of_field477 h1 h
              exact ⟨j,after,by change j ∈ k::as.keys; exact List.mem_cons_of_mem _ hj,he⟩
      · cases ok

private theorem combine_nodup477 {rows} {a b : LocatedCapture476 rows}
    (ha : (a.marks.map LocatedMark476.path).Nodup)
    (hb : (b.marks.map LocatedMark476.path).Nodup)
    (disjoint : ∀ x ∈ a.marks, ∀ y ∈ b.marks, x.path ≠ y.path) :
    ((a.combine b).marks.map LocatedMark476.path).Nodup := by
  change ((a.marks ++ b.marks).map LocatedMark476.path).Nodup
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨ha,hb,?_⟩
  intro p hpA pp hpB same
  subst pp
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hpA
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hpB
  exact disjoint x hx y hy he.symm

private theorem prefix_nodup477 {rows p input} {a : LocatedCapture476 rows}
    (ha : (a.marks.map LocatedMark476.path).Nodup)
    (below : ∀ m ∈ a.marks, p.length < m.path.length) :
    (((LocatedCapture476.prefix p (exposeStamped rows input).2 a).marks).map LocatedMark476.path).Nodup := by
  unfold LocatedCapture476.prefix
  simp only [List.map_append,List.map_map,Function.comp_def]
  refine List.nodup_append.mpr ⟨?_,ha,?_⟩
  · cases input <;> simp [exposeStamped]
    split <;> simp
  · intro q hq qq hqa same
    subst qq
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp hqa
    have z := below y hy
    rw [eq] at z
    exact (Nat.lt_irrefl _ z)


private theorem marks_below_child477 {rows p k mode input q out}
    (ok : runLocated476 rows (p++[k]) mode input q=some out) :
    ∀ m ∈ out.marks, p.length < m.path.length := by
  intro m hm
  obtain ⟨rest,eq⟩ := every_located_mark_extends_the_exact_starting_prefix476 ok hm
  rw [eq]
  simp

mutual
theorem exact_path_once_in_every_structural_capture477 {rows p mode input q out}
    (ok : runLocated476 rows p mode input q=some out) :
    (out.marks.map LocatedMark476.path).Nodup := by
  cases q with
  | capture binder =>
    cases ok
    simp
  | primitive tag sub =>
    simp only [runLocated476] at ok
    generalize he : (exposeStamped rows input).1 = body at ok
    cases body <;> try cases ok
    rename_i got data
    change (if tagId got = tagId tag then (runLocatedArgs476 rows p 0 mode data sub).map
      (LocatedCapture476.prefix p (exposeStamped rows input).2) else none)=some out at ok
    by_cases hz : tagId got = tagId tag
    · rw [ite_eq_left hz] at ok
      cases h : runLocatedArgs476 rows p 0 mode data sub with
      | none => simp [h] at ok
      | some a =>
        have e : LocatedCapture476.prefix p (exposeStamped rows input).2 a=out := by simpa [h] using ok
        rw [←e]
        exact prefix_nodup477 (exact_argument_paths_once477 h)
          (fun _ m => located_argument_mark_is_strictly_below_start476 h m)
    · simp [hz] at ok
  | nominal tag sub =>
    simp only [runLocated476] at ok
    generalize he : (exposeStamped rows input).1 = body at ok
    cases body <;> try cases ok
    rename_i got data
    change (if got = tag then (runLocatedArgs476 rows p 0 .actual data sub).map
      (LocatedCapture476.prefix p (exposeStamped rows input).2) else none)=some out at ok
    by_cases hz : got = tag
    · rw [ite_eq_left hz] at ok
      cases h : runLocatedArgs476 rows p 0 .actual data sub with
      | none => simp [h] at ok
      | some a =>
        have e : LocatedCapture476.prefix p (exposeStamped rows input).2 a=out := by simpa [h] using ok
        rw [←e]
        exact prefix_nodup477 (exact_argument_paths_once477 h)
          (fun _ m => located_argument_mark_is_strictly_below_start476 h m)
    · simp [hz] at ok
  | variant tag sub =>
    simp only [runLocated476] at ok
    generalize he : (exposeStamped rows input).1 = body at ok
    cases body <;> try cases ok
    rename_i got data
    change (if got = tag then (runLocated476 rows (p++[.variantPayload]) mode data sub).map
      (LocatedCapture476.prefix p (exposeStamped rows input).2) else none)=some out at ok
    by_cases hz : got = tag
    · rw [ite_eq_left hz] at ok
      cases h : runLocated476 rows (p++[.variantPayload]) mode data sub with
      | none => simp [h] at ok
      | some a =>
        have e : LocatedCapture476.prefix p (exposeStamped rows input).2 a=out := by simpa [h] using ok
        rw [←e]
        exact prefix_nodup477 (exact_path_once_in_every_structural_capture477 h) (marks_below_child477 h)
    · simp [hz] at ok
  | join left right =>
    simp only [runLocated476] at ok
    generalize he : (exposeStamped rows input).1 = body at ok
    cases body <;> try cases ok
    rename_i x y
    cases hl : runLocated476 rows (p++[.legacyJoinLeft]) mode x left with
    | none => simp [hl] at ok
    | some a =>
      cases hr : runLocated476 rows (p++[.legacyJoinRight]) mode y right with
      | none => simp [hl,hr] at ok
      | some b =>
        have e : LocatedCapture476.prefix p (exposeStamped rows input).2 (a.combine b)=out := by
          simpa [hl,hr] using ok
        rw [←e]
        apply prefix_nodup477
        · apply combine_nodup477 (exact_path_once_in_every_structural_capture477 hl)
            (exact_path_once_in_every_structural_capture477 hr)
          intro m hm n hn same
          obtain ⟨rest,hx⟩ := every_located_mark_extends_the_exact_starting_prefix476 hl hm
          obtain ⟨other,hy⟩ := every_located_mark_extends_the_exact_starting_prefix476 hr hn
          rw [hx,hy] at same
          cases next_step_eq477 same
        · intro m hm
          rcases List.mem_append.mp hm with h|h
          · exact marks_below_child477 hl _ h
          · exact marks_below_child477 hr _ h
  | record fs tail =>
    simp only [runLocated476] at ok
    by_cases good : fs.keys ≠ [] ∧ fs.keys.Nodup
    · rw [ite_eq_left good] at ok
      cases h0 : literalRows (fun _ => none) (exposeStamped rows input).1 with
      | none => simp [h0] at ok
      | some r =>
        obtain ⟨r,z⟩ := r
        cases h1 : order (CommonRoleCanonicalRows.normalize r) fs.keys with
        | none => simp [h0,h1] at ok
        | some selected =>
          cases h2 : runLocatedFields476 rows p mode selected fs with
          | none => simp [h0,h1,h2] at ok
          | some a =>
            cases h3 : tailRun mode (tailExpr r fs.keys z) tail with
            | none => simp [h0,h1,h3] at ok
            | some b =>
              have e : LocatedCapture476.prefix p (exposeStamped rows input).2
                  (a.combine ⟨b,[]⟩)=out := by simpa [h0,h1,h2,h3] using ok
              rw [←e]
              apply prefix_nodup477
              · simpa [LocatedCapture476.combine] using exact_field_paths_once477 good.2 h2
              · intro m hm
                exact located_field_mark_is_strictly_below_start476 h2 (by simpa [LocatedCapture476.combine] using hm)
    · simp [good] at ok

theorem exact_argument_paths_once477 {rows p i mode raw q out}
    (ok : runLocatedArgs476 rows p i mode raw q=some out) :
    (out.marks.map LocatedMark476.path).Nodup := by
  cases q with
  | nil => cases raw <;> cases ok; simp
  | cons a as =>
    cases raw with
    | nil => cases ok
    | cons e es =>
      simp only [runLocatedArgs476] at ok
      cases h0 : runLocated476 rows (p++[.argument i]) mode e a with
      | none => simp [h0] at ok
      | some first =>
        cases h1 : runLocatedArgs476 rows p (i+1) mode es as with
        | none => simp [h0,h1] at ok
        | some rest =>
          have eq : first.combine rest=out := by simpa [h0,h1] using ok
          rw [←eq]
          apply combine_nodup477 (exact_path_once_in_every_structural_capture477 h0) (exact_argument_paths_once477 h1)
          intro m hm n hn same
          obtain ⟨left,hx⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 hm
          obtain ⟨j,right,hj,hy⟩ := path_of_argument477 h1 hn
          rw [hx,hy] at same
          have ij := QueryStep476.argument.inj (next_step_eq477 same)
          omega

theorem exact_field_paths_once477 {rows p mode raw q out}
    (unique : q.keys.Nodup)
    (ok : runLocatedFields476 rows p mode raw q=some out) :
    (out.marks.map LocatedMark476.path).Nodup := by
  cases q with
  | nil => cases raw <;> cases ok; simp
  | cons k a as =>
    change (k::as.keys).Nodup at unique
    obtain ⟨absent,nodup⟩ := List.nodup_cons.mp unique
    cases raw with
    | nil => cases ok
    | cons entry es =>
      obtain ⟨l,e⟩ := entry
      simp only [runLocatedFields476] at ok
      split at ok
      · cases h0 : runLocated476 rows (p++[.field k]) mode e a with
        | none => simp [h0] at ok
        | some first =>
          cases h1 : runLocatedFields476 rows p mode es as with
          | none => simp [h0,h1] at ok
          | some rest =>
            have eq : first.combine rest=out := by simpa [h0,h1] using ok
            rw [←eq]
            apply combine_nodup477 (exact_path_once_in_every_structural_capture477 h0) (exact_field_paths_once477 nodup h1)
            intro m hm n hn same
            obtain ⟨left,hx⟩ := every_located_mark_extends_the_exact_starting_prefix476 h0 hm
            obtain ⟨j,right,hj,hy⟩ := path_of_field477 h1 hn
            rw [hx,hy] at same
            have kj := QueryStep476.field.inj (next_step_eq477 same)
            exact absent (kj ▸ hj)
      · cases ok
end

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

