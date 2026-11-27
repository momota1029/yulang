import Yulang.GeneralDeclarativeI65I74OriginalReportAnchor460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery AuthoredQueries AuthoredApplication legacyApply)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralDeclarativeInspect321 (fieldPatterns)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)

inductive CompiledClosedSpine : Expr → Prop
  | empty : CompiledClosedSpine (.primitive .emptyRecord [])
  | next : CompiledClosedSpine tail → CompiledClosedSpine (.record l p tail)

theorem closed_written_spine_compiles_closed {s t e}
    (spine : ClosedSpine (queryKeys s) t)
    (compiled : AuthoredQuery s (writeTerm t) e) :
    CompiledClosedSpine e := by
  induction spine generalizing e with
  | @empty key proof =>
    change AuthoredQuery s (.app key []) e at compiled
    cases compiled with
    | app args app =>
      cases args
      cases app with
      | legacy seen =>
        have same := Option.some.inj (seen.symm.trans (query_empty_key_exact.mp proof))
        subst e
        exact .empty
  | @next tail label item proof ih =>
    change AuthoredQuery s (.record label (writeTerm item) (writeTerm tail)) e at compiled
    cases compiled with
    | record _ tail => exact .next (ih tail)

theorem closed_compiled_spine_has_closed_original {s t e}
    (compiled : AuthoredQuery s (writeTerm t) e)
    (spine : CompiledClosedSpine e) :
    ClosedSpine (queryKeys s) t := by
  induction spine generalizing t with
  | empty =>
    cases t
    case var | variant | record | join => cases compiled
    case app key args =>
      change AuthoredQuery s (.app key (writeArgs args)) (.primitive .emptyRecord []) at compiled
      cases compiled with
      | app written applied =>
        have shape := authored_application_keeps_ordered_args applied
        rcases shape with ⟨op,same⟩ | ⟨k,same⟩
        · obtain ⟨rfl,rfl⟩ := Expr.primitive.inj same
          cases args with
          | nil =>
            cases written
            cases applied with
            | legacy actual => exact .empty (query_empty_key_exact.mpr actual)
          | cons => cases written
        · cases same
  | @next tail label payload sub ih =>
    cases t
    case var | variant | join => cases compiled
    case record l p t =>
      change AuthoredQuery s (.record l (writeTerm p) (writeTerm t))
        (.record label payload tail) at compiled
      cases compiled with
      | record _ right => exact .next (ih right)
    case app k q =>
      change AuthoredQuery s (.app k (writeArgs q)) (.record label payload tail) at compiled
      cases compiled with
      | app _ op =>
        rcases authored_application_keeps_ordered_args op with ⟨_,h⟩ | ⟨_,h⟩ <;> cases h

theorem compiled_record_spine_exact {s t e}
    (compiled : AuthoredQuery s (writeTerm t) e) :
    ClosedSpine (queryKeys s) t ↔ CompiledClosedSpine e :=
  ⟨fun h => closed_written_spine_compiles_closed h compiled,closed_compiled_spine_has_closed_original compiled⟩

theorem authored_first_visible_field_recovered {s t e label q}
    (compiled : AuthoredQuery s (writeTerm t) e)
    (child : (label,q) ∈ fieldPatterns e) :
    ∃ u, FirstField label t u ∧ AuthoredQuery s (writeTerm u) q := by
  cases t with
  | var name => cases compiled; simp [fieldPatterns] at child
  | variant tag p => cases compiled; simp [fieldPatterns] at child
  | join a b => cases compiled; simp [fieldPatterns] at child
  | app k as =>
    change AuthoredQuery s (.app k (writeArgs as)) e at compiled
    cases compiled with
    | app _ apply =>
      rcases authored_application_keeps_ordered_args apply with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [fieldPatterns] at child
  | record k p t =>
    change AuthoredQuery s (.record k (writeTerm p) (writeTerm t)) e at compiled
    cases compiled with
    | record body tail =>
      simp only [fieldPatterns,List.mem_cons,List.mem_filter] at child
      rcases child with h | ⟨there,other⟩
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        exact ⟨p,.here,body⟩
      · obtain ⟨u,first,written⟩ := authored_first_visible_field_recovered tail there
        exact ⟨u,.later (of_decide_eq_true other) first,written⟩

theorem existing_field_address_reflects_original_closed_step {s t l q payload tail}
    (compiled : AuthoredQuery s (writeTerm t) (.record l payload tail))
    (closed : CompiledClosedSpine tail)
    (found : (label,q) ∈ fieldPatterns (.record l payload tail)) :
    ∃ u, Step (queryKeys s) t (.field label) u ∧ AuthoredQuery s (writeTerm u) q := by
  obtain ⟨u,field,child⟩ := authored_first_visible_field_recovered compiled found
  have whole := closed_compiled_spine_has_closed_original compiled (.next closed)
  cases field with
  | here =>
    cases whole with | next can => exact ⟨_,.field can .here,child⟩
  | later ne inner =>
    cases whole with | next can => exact ⟨_,.field can (.later ne inner),child⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
