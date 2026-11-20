import Yulang.GeneralSourceRoleCstMinimalCatalog296

/-! An observed absence is evidence of failed resolution, not the
required-without-default marker of the old associated slot. -/
namespace Yulang.GeneralSourceRoleCstKnownOnSuccess296
open GeneralSourceRoleSpelling292 (Environment Role Body Output ResolvedBody)
open GeneralSourceRoleCstNamingRequests295 (Query reply bodyQueries outputQueries queryList)
open GeneralSourceRoleExport292 (OutputWitness RowWitness role_exact)
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup environment known_reply)
open GeneralSourceRoleCstCatalogExport296 (Exported run run_exact)
open GeneralSourceRoleCstCatalogFootprint296 (produced_member_exact)
open GeneralSourceRoleCstTrackedRow296 (tracked_row_exact)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

def FoundAll (e : Environment) (keys : List Query) : Prop :=
  ∀ q ∈ keys, ∃ n, reply e q = some n

theorem resolved_body_keys_found {e : Environment} {xs : List String} {b : Body}
    {v : Option Roles.Term} (h : ResolvedBody e xs b v) : FoundAll e (bodyQueries b) := by
  cases h with
  | required => simp [FoundAll,bodyQueries]
  | binder _ => simp [FoundAll,bodyQueries]
  | nullary saw =>
    intro q m
    have e := List.mem_singleton.mp m
    subst q
    exact ⟨_,saw⟩

theorem resolved_output_keys_found {e : Environment} {xs : List String}
    {r : Nat} {o : Output} {field : Nat × Option Roles.Term}
    (h : OutputWitness e r xs o field) : FoundAll e (outputQueries e r o) := by
  unfold outputQueries
  rw [h.1]
  intro q mem
  rcases List.mem_cons.mp mem with rfl | body
  · exact ⟨_,h.1⟩
  · exact resolved_body_keys_found h.2 q body

theorem lowered_role_keys_found {e : Environment} {r : Role} {row : BareRow}
    (h : RowWitness e r row) : FoundAll e (queryList e r) := by
  obtain ⟨_,head,_,outputs⟩ := h
  unfold queryList
  rw [head]
  intro q mem
  rcases List.mem_cons.mp mem with rfl | body
  · exact ⟨_,head⟩
  · obtain ⟨o,inRole,atOutput⟩ := List.mem_flatMap.mp body
    obtain ⟨field,_,p⟩ := GeneralSourceRoleManifest292.aligned_left outputs inRole
    exact resolved_output_keys_found p q atOutput

theorem success_has_no_absent_replies {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (wire : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (ok : run policy scope wire brand a sealed c fallback = .ok out)
    (q : Query) (v : Option Nat) (member : (q,v) ∈ out.trace) : ∃ n, v = some n := by
  obtain ⟨p,r,found,sym,trace,attached⟩ := (run_exact ..).mp ok
  obtain ⟨r',row,sym',_,_,_,lowered⟩ := (tracked_row_exact ..).mp attached
  cases Option.some.inj (sym'.symm.trans sym)
  obtain ⟨asked,actually⟩ := (produced_member_exact c r.role out.trace trace q v).mp member
  obtain ⟨n,yes⟩ := lowered_role_keys_found ((role_exact ..).mp lowered) q asked
  exact ⟨n,(known_reply _ q v actually).symm.trans yes⟩

end Yulang.GeneralSourceRoleCstKnownOnSuccess296
