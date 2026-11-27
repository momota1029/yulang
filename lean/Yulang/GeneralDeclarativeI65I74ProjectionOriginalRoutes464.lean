import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open PreparedDeclarations463

private theorem origin_route_depends_only_on_the_exact_stored_routes
    (s t : GeneralDeclarativeI65.State) (same : s.routes = t.routes) (o : Origin) (slot : Nat) :
    OriginRoute s o slot ↔ OriginRoute t o slot := by
  constructor
  · intro h
    cases h with
    | direct => exact .direct
    | authored seen => exact .authored (same ▸ seen)
  · intro h
    cases h with
    | direct => exact .direct
    | authored seen => exact .authored (same.symm ▸ seen)

/-- Cut/same-fit evidence alone does not identify the old source route.
Under separately supplied identical stored origins and routes, the actual
selected post-visit owner was already authoritative in the earlier snapshot.
The earlier graph still need not contain that visit. -/
theorem post_visit_uses_the_very_same_original_issuer_route_under_explicit_route_frame
    {p : SnapshotPair} {t : CheckedTable p.before.state.base.core.current}
    {site : Nat} {r : ProjectionFieldReceipt}
    (h : ExactProjectedField p t site r)
    (fitFrame : SameFitFrame p.before.state p.after.state)
    (routeFrame : p.before.state.base.core.routes = p.after.state.base.core.routes)
    (m : I72.Model) (fit : FitsFull p.before.state m) :
    r.field.literal ≠ [] ∧ AliasCycle p.pre (observed p.pre) r.field.terminal ∧
      ∃ (owner : Origin) (logical : Nat) (row : GeneralDeclarativeHead320.Equation),
        owner ∈ p.before.state.base.core.origins ∧
        OriginRoute p.before.state.base.core owner logical ∧ owner.slot = site ∧
        GeneralDeclarativeLowerKnown321.Alias p.pre logical site ∧
        p.post.equations[p.pre.equations.length]? = some row ∧ row.left = site ∧
        m.nativeSyntax owner.slot = some owner.endpoint := by
  have transferred := (exact_projection_transfers_full_fits_under_same_stored_frame h.1 fitFrame m).mp fit
  obtain ⟨literal,cycle,logical,query,row,shape,a,c,next,used,o,selected,stored,ownerEq,aliasAfter,
    parsed,position,registered,route,slot,readNative,model⟩ :=
    literal_post_visit_keeps_an_old_cycle_and_the_exact_issued_native_site h m transferred
  have preRegistered := fitFrame.native.symm ▸ registered
  have preRoute := (origin_route_depends_only_on_the_exact_stored_routes _ _ routeFrame o logical).mpr route
  have preAlias : GeneralDeclarativeLowerKnown321.Alias p.pre logical site := by
    obtain ⟨term,form,eq,found,_,_,_⟩ := h.1
    have noAlias : ∀ n, term ≠ .variable n := by
      intro n bad
      rw [bad] at found
      cases found
    rw [eq] at aliasAfter
    exact (GeneralDeclarativeK2Graph321.AddAtOneSource.adding_a_non_alias_row_preserves_actual_aliases
      p.pre ⟨site,term⟩ noAlias logical site).mp aliasAfter
  exact ⟨literal,cycle,o,logical,row,preRegistered,preRoute,slot,preAlias,stored,ownerEq,readNative⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
