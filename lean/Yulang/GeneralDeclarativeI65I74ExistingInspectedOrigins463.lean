import Yulang.GeneralDeclarativeI65I74OriginalPhysicalPositions463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
open Yulang.GeneralDeclarationPatterns
open AuthoredInspectQuery456 (AuthoredQuery)
open GeneralDeclarativeInspect321 (Inspects)
open RecordTraversal455.MixedQA (MixedPath)

private abbrev VRow := List (Nat × Pattern)
private abbrev merged (xs : VRow) : VRow := (Variants.Merged.normalize mergePayload xs).entries
private abbrev sorted (xs : VRow) : VRow := (merged xs).mergeSort (fun a b => a.1 ≤ b.1)

private theorem variant_row_nonempty {p : Pattern} {xs : VRow}
    (h : variantRow p = some xs) : xs ≠ [] := by
  cases p with
  | var | app | record => simp [variantRow] at h
  | variant => simp [variantRow] at h; subst xs; simp
  | join p q =>
    cases hp : variantRow p <;> cases hq : variantRow q <;>
      simp [variantRow,hp,hq,Option.bind] at h
    case some.some a b =>
      subst xs
      exact fun ep => variant_row_nonempty hp (List.append_eq_nil_iff.mp ep).1

private theorem same_sorted_tags (xs : VRow) {k : Nat} :
    k ∈ (sorted xs).map Prod.fst ↔ k ∈ xs.map Prod.fst := by
  exact ((List.mergeSort_perm (merged xs) _).map Prod.fst).mem_iff.trans
    (Variants.Merged.tags_normalize mergePayload k xs)

private theorem variant_row_reconstructs (xs : VRow) (nonempty : xs ≠ []) :
    variantRow (rowPattern xs) = some xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨k,q⟩ := x
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [rowPattern,variantRow,ih (by simp)]
      rfl

private theorem variant_row_is_singleton_shape {p : Pattern} {k : Nat} {q : Pattern}
    (h : variantRow p = some [(k,q)]) : p = .variant k q := by
  cases p with
  | var | app | record => simp [variantRow] at h
  | variant => simpa [variantRow] using h
  | join p q =>
    cases hp : variantRow p <;> cases hq : variantRow q <;>
      simp [variantRow,hp,hq,Option.bind] at h
    case some.some a b =>
      have na := variant_row_nonempty hp
      have nb := variant_row_nonempty hq
      cases a <;> cases b <;> simp_all

private theorem normalized_variant_row_unique (p : Pattern) (xs : VRow)
    (h : variantRow (normalize p) = some xs) : (xs.map Prod.fst).Nodup := by
  cases p with
  | var | app | record => simp [normalize,variantRow] at h
  | variant => simp [normalize,variantRow] at h; subst xs; simp
  | join p q =>
    by_cases same : normalize p = normalize q
    · apply normalized_variant_row_unique p xs
      simpa [normalize,merge,same] using h
    · cases hp : variantRow (normalize p) <;> cases hq : variantRow (normalize q) <;>
        simp [normalize,merge,same,variantRow,hp,hq,Option.bind] at h
      case some.some a b =>
        have nonempty : sorted (a ++ b) ≠ [] := by
          intro bad
          have na := variant_row_nonempty hp
          cases a with
          | nil => contradiction
          | cons hd xs =>
            have yes : hd.1 ∈ ((hd :: xs) ++ b).map Prod.fst := by simp
            have impossible := (same_sorted_tags ((hd :: xs) ++ b)).mpr yes
            rw [bad] at impossible
            cases impossible
        rw [variant_row_reconstructs _ nonempty] at h
        cases h
        exact ((List.mergeSort_perm (merged (a ++ b)) _).map Prod.fst).nodup_iff.mpr
          (Variants.Merged.normalize_unique mergePayload _)

private theorem singleton_if_one_key (xs : VRow) (nonempty : xs ≠ [])
    (nodup : (xs.map Prod.fst).Nodup) (only : ∀ k ∈ xs.map Prod.fst, k = tag) :
    ∃ v, xs = [(tag,v)] := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    obtain ⟨k,v⟩ := x
    have eq := only k (by simp)
    subst k
    cases xs with
    | nil => exact ⟨v,rfl⟩
    | cons y ys =>
      have eq := only y.1 (by simp)
      have no : tag ∉ (y :: ys).map Prod.fst := by
        exact (List.nodup_cons.mp nodup).1
      exact False.elim (no (by simp [eq]))

private theorem row_pattern_variant_singleton (xs : VRow) {tag : Nat} {v : Pattern}
    (h : rowPattern xs = .variant tag v) : xs = [(tag,v)] := by
  cases xs with
  | nil => cases h
  | cons x xs =>
    obtain ⟨k,p⟩ := x
    cases xs <;> cases h
    rfl

/-- A distinct merge constructing one exact tag necessarily places a residual
join at its payload. The proof uses that each normalized arm is tag-unique.
No semantic choice about how to inspect this join has been made. -/
theorem distinct_normalized_join_single_tag_keeps_residual
    (p q : Pattern) (tag : Nat) (u : Pattern) (ne : normalize p ≠ normalize q)
    (result : normalize (.join p q) = .variant tag u) :
    ∃ a b, u = .join a b := by
  simp only [normalize,merge,ne,ite_false] at result
  cases hp : variantRow (normalize p) <;> cases hq : variantRow (normalize q) <;>
    simp [hp,hq] at result
  case some.some xs ys =>
    have one := row_pattern_variant_singleton _ result
    have allKeys : ∀ k ∈ (xs ++ ys).map Prod.fst, k = tag := by
      intro k member
      have before := (same_sorted_tags (xs ++ ys)).mpr member
      simpa [one] using before
    obtain ⟨a,ha⟩ := singleton_if_one_key xs (variant_row_nonempty hp)
      (normalized_variant_row_unique p xs hp) (fun k h => allKeys k (by simp [h]))
    obtain ⟨b,hb⟩ := singleton_if_one_key ys (variant_row_nonempty hq)
      (normalized_variant_row_unique q ys hq) (fun k h => allKeys k (by simp [h]))
    have hp' := variant_row_is_singleton_shape (ha ▸ hp)
    have hq' := variant_row_is_singleton_shape (hb ▸ hq)
    have diff : a ≠ b := by
      intro eq
      apply ne
      rw [hp',hq',eq]
    have mergedOut : sorted (xs ++ ys) = [(tag, .join a b)] := by
      subst xs; subst ys
      simp [sorted,merged,Variants.Merged.normalize,Variants.Merged.Raw.insert,mergePayload,diff]
    change rowPattern (sorted (xs ++ ys)) = .variant tag u at result
    rw [mergedOut] at result
    cases result
    exact ⟨a,b,rfl⟩

/-- If existing traversal can actually inspect the next tag payload, the
literal original tag provenance is available in the same G04 grammar. -/
theorem inspected_normalized_tag_has_literal_origin (p : Pattern) (tag : Nat) (u : Pattern)
    (shape : normalize p = .variant tag u) (notJoin : ∀ a b, u ≠ .join a b) :
    ∃ poses q, Origin p (.tag tag) poses q ∧ normalize q = u := by
  cases p with
  | var | app | record => simp [normalize] at shape
  | variant k q =>
    simp only [normalize,Pattern.variant.injEq] at shape
    obtain ⟨rfl,h⟩ := shape
    exact ⟨[.variant],q,.tag,h⟩
  | join p q =>
    by_cases same : normalize p = normalize q
    · have fit : normalize p = .variant tag u := by simpa [normalize,merge,same] using shape
      obtain ⟨poses,x,orig,h⟩ := inspected_normalized_tag_has_literal_origin p tag u fit notJoin
      exact ⟨.left :: poses,x,.left same orig,h⟩
    · obtain ⟨a,b,h⟩ := distinct_normalized_join_single_tag_keeps_residual p q tag u same shape
      exact (notJoin a b h).elim


open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem compiled_trail_has_no_residual_join_at_start {s n a b e path terminal last used}
    (h : CompiledTrail s n (.join a b) e path terminal last used) : False := by
  cases h with
  | stop authored rigid =>
    change AuthoredQuery s (.join (writeTerm a) (writeTerm b)) _ at authored
    cases authored
    cases rigid
  | down _ _ _ first _ => cases first

private theorem normalized_argument_shape {keys t i u} (h : Step keys t (.arg i) u) :
    ∃ k ps, writeTerm t = .app k ps ∧ ps[i]? = some (writeTerm u) := by
  cases h with
  | pair0 _ | pair1 _ | point _ =>
    exact ⟨_,_,rfl,rfl⟩

private theorem normalized_tag_shape {keys t k u} (h : Step keys t (.tag k) u) :
    writeTerm t = .variant k (writeTerm u) := by
  cases h
  rfl

/-- The exact existing follow-up trail (including its stop test) rules out a
residual join payload. Thus the three selectable address forms have a literal
source origin on every actual compiled trail in the existing scope. -/
theorem followed_compiled_step_has_original_origin {s c q path terminal last used k p addr u}
    (step : Step k (readTerm (normalize p)) addr u)
    (followed : CompiledTrail s c u q path terminal last used) :
    ∃ poses x, Origin p addr poses x ∧ readTerm (normalize x) = u := by
  cases addr with
  | field l =>
    obtain ⟨poses,x,member,same,_⟩ := every_existing_normalized_field_step_has_finite_original_position step
    exact ⟨poses,x,(selected_occurrence_iff.mp member).1,same⟩
  | arg i =>
    obtain ⟨key,args,shape,hit⟩ := normalized_argument_shape step
    rw [write_read_term] at shape
    obtain ⟨poses,x,orig,same⟩ := actual_normalized_argument_has_literal_origin p key i
      args (writeTerm u) shape hit
    exact ⟨poses,x,orig,by rw [same,read_write_term]⟩
  | tag l =>
    have shape := normalized_tag_shape step
    rw [write_read_term] at shape
    have notJoin : ∀ a b, writeTerm u ≠ .join a b := by
      intro a b alleged
      have e : u = .join (readTerm a) (readTerm b) := by
        rw [← read_write_term u,alleged,readTerm]
      rw [e] at followed
      exact compiled_trail_has_no_residual_join_at_start followed
    obtain ⟨poses,x,orig,same⟩ := inspected_normalized_tag_has_literal_origin
      p l (writeTerm u) shape notJoin
    exact ⟨poses,x,orig,by rw [same,read_write_term]⟩

/-- Every existing compiled trail, not merely every proposed spelling route,
reifies into a finite physical original position. The raw route and endpoint
are unchanged; duplicate origins are not collapsed into a display choice. -/
theorem existing_compiled_trail_has_finite_literal_origin
    {s n t e path terminal last used} (trail : CompiledTrail s n t e path terminal last used)
    (p : Pattern) (authored : readTerm (normalize p) = t) :
    ∃ poses x, OriginalWalk (fun _ => queryKeys s) p n path poses x ∧
      readTerm (normalize x) = last := by
  induction trail generalizing p with
  | stop _ _ => exact ⟨[],p,.stop,authored⟩
  | down _ _ _ step followed ih =>
    rw [← authored] at step
    obtain ⟨first,x,orig,same⟩ := followed_compiled_step_has_original_origin step followed
    obtain ⟨rest,y,route,last⟩ := ih x same
    exact ⟨first ++ rest,y,.down orig (same.symm ▸ step) route,last⟩

theorem existing_scoped_raw_route_has_finite_literal_origin
    {s n e path terminal last used} (p : Pattern)
    (a : AuthoredQuery s (normalize p) e)
    (actual : ScopedRaw s n (readTerm (normalize p)) e path terminal last used) :
    ∃ poses x, (poses,x) ∈ locateRoute (fun _ => queryKeys s) p n path ∧
      atSource p poses = some x ∧ readTerm (normalize x) = last := by
  have aa : AuthoredQuery s (writeTerm (readTerm (normalize p))) e := by simpa using a
  have trail := exact_scope_reifies_full_trace_by_descent aa actual
  obtain ⟨poses,x,walk,last⟩ := existing_compiled_trail_has_finite_literal_origin trail p rfl
  exact ⟨poses,x,route_occurrences_exact.mpr walk,
    (whole_route_is_literal_and_preserves_exact_coordinates walk).1,last⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
