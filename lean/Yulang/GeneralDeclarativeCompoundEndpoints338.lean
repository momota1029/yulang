import Yulang.GeneralDeclarativeExactSupport337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundEndpoints338
open CommonRoleCanonicalRows (Row lookup normalize normalize_unique)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_mono)
open GeneralDeclarativeRecordSpine330 (Spine Terminal tail_append)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeOrderedRecord326 (order exact_order lookup_unique)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeEndpointSupport336 (Certified)
open GeneralDeclarativeExactSupport337 (authorize endpointRows from_projection)
open GeneralDeclarativeDemand320 (Bounds)

theorem order_iff {raw : Row α} (unique : (raw.map Prod.fst).Nodup) (keys : List Nat) :
    (∃ taken, order raw keys = some taken) ↔ ∀ k ∈ keys, ∃ x, (k,x) ∈ raw := by
  constructor
  · rintro ⟨taken,computed⟩ k found
    have properties := exact_order unique computed
    have known : k ∈ taken.map Prod.fst := properties.1.symm ▸ found
    obtain ⟨⟨tag,entry⟩,present,eq⟩ := List.mem_map.mp known
    change tag = k at eq
    subst tag
    exact ⟨entry,((properties.2 _).mp present).1⟩
  · induction keys with
    | nil => exact fun _ => ⟨[],rfl⟩
    | cons k ks ih =>
      intro visible
      obtain ⟨head,present⟩ := visible k List.mem_cons_self
      obtain ⟨tail,selected⟩ := ih (fun key included => visible key (List.mem_cons_of_mem _ included))
      exact ⟨(k,head)::tail,by simp [order,lookup_unique unique present,selected]⟩

/-- Compute both exact ordered endpoint lists from source head
visibility alone. Neither an ordinary center row nor a model is used. -/
theorem from_visible {s : State} {p : Supported s done}
    (valid : Bounds s arg) (distinct : keys.Nodup)
    (lo : Spine (restriction p) arg.lower lower loEnd)
    (hi : Spine (restriction p) arg.upper upper hiEnd)
    (lkeys : ∀ key ∈ keys, ∃ x, (key,x) ∈ normalize lower)
    (hkeys : ∀ key ∈ keys, ∃ x, (key,x) ∈ normalize upper) :
    ∃ first last, Read p arg keys lower upper first last loEnd hiEnd := by
  obtain ⟨first,seq⟩ := (order_iff (normalize_unique lower) keys).mpr lkeys
  obtain ⟨last,seq'⟩ := (order_iff (normalize_unique upper) keys).mpr hkeys
  exact ⟨first,last,valid,distinct,lo,hi,seq,seq'⟩

theorem spine_mono {s t : State} (same : s.normal = t.normal)
    (rows : s.equations ⊆ t.equations) (seen : Spine s n ls terminal) :
    Spine t n ls terminal := by
  induction seen with
  | width link row => exact .width (alias_mono same rows link) (rows row)
  | exactEnd link row => exact .exactEnd (alias_mono same rows link) (rows row)
  | cons link row _ ih => exact .cons (alias_mono same rows link) (rows row) ih
  | inline link ends row => exact .inline (alias_mono same rows link) ends (rows row)
  | prefixed link row _ ih => exact .prefixed (alias_mono same rows link) (rows row) ih

theorem closed_mono {s t : State} (same : s.normal = t.normal)
    (rows : s.equations ⊆ t.equations) (seen : Closed s term ls terminal) :
    Closed t term ls terminal := by
  induction seen with
  | terminal ends => exact .terminal ends
  | field _ ih => exact .field ih
  | name spine => exact .name (spine_mono same rows spine)

theorem old_backed {s : State} {p : Supported s done} (rs : List Entry) :
    (restriction p).equations ⊆ (restriction (authorize p rs)).equations := by
  intro row present
  obtain ⟨o,source,known⟩ := (backed_iff p row).mp present
  exact (backed_iff _ row).mpr ⟨o,.inl source,known⟩

open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Independent inline spine extraction retains the exact original
terminal syntax (including a named tail); not a guessed normal RHS. -/
theorem closed_literal {s : State} {term : Expr} (seen : Closed s term ls terminal) :
    (term = withTail ls terminal ∧ Terminal terminal) ∨
      ∃ front n suffix, term = withTail front (.variable n) ∧ ls = front ++ suffix ∧
        Spine s n suffix terminal := by
  induction seen with
  | terminal endSyntax => exact .inl ⟨rfl,endSyntax⟩
  | @field next rest terminal key payload _ ih =>
    rcases ih with ⟨equal,ending⟩|⟨front,n,suffix,shape,all,known⟩
    · exact .inl ⟨congrArg (Expr.record key payload) equal,ending⟩
    · refine .inr ⟨(key,payload)::front,n,suffix,?_,?_,known⟩
      · exact congrArg (Expr.record key payload) shape
      · exact congrArg ((key,payload)::·) all
  | name spine => exact .inr ⟨[],_,_,rfl,rfl,spine⟩

theorem from_row {s : State} (stored : (⟨name,term⟩ : Equation) ∈ s.equations)
    (seen : Closed s term ls terminal) : Spine s name ls terminal := by
  rcases closed_literal seen with ⟨rfl,ending⟩|⟨front,n,suffix,rfl,rfl,current⟩
  · exact .inline (alias_refl _) ending stored
  · exact .prefixed (alias_refl _) stored current

/-- Rebase after a real field/remainder projection. The two projected
spines may finish through *different* original supported aliases.
No projected actual-center equality is added. -/
theorem projected {s : State} {p : Supported s done} {e : Entry}
    (listed : e ∈ rs) (source : Certified p e) (valid : Bounds s e.2)
    (wroteLow : (⟨e.2.lower,lterm⟩ : Equation) ∈ endpointRows e)
    (wroteHigh : (⟨e.2.upper,uterm⟩ : Equation) ∈ endpointRows e)
    (hasLow : Closed (restriction p) lterm lower loEnd)
    (hasHigh : Closed (restriction p) uterm upper hiEnd)
    (distinct : keys.Nodup)
    (lkeys : ∀ key ∈ keys, ∃ x, (key,x) ∈ normalize lower)
    (hkeys : ∀ key ∈ keys, ∃ x, (key,x) ∈ normalize upper) :
    ∃ first last, Read (authorize p rs) e.2 keys lower upper first last loEnd hiEnd := by
  have one := from_row (from_projection listed source wroteLow)
    (closed_mono (s := restriction p) (t := restriction (authorize p rs)) rfl (old_backed rs) hasLow)
  have two := from_row (from_projection listed source wroteHigh)
    (closed_mono (s := restriction p) (t := restriction (authorize p rs)) rfl (old_backed rs) hasHigh)
  exact from_visible (GeneralDeclarativeGrowth327.fits (GeneralDeclarativeGrowth327.facts _ _) valid)
    distinct one two lkeys hkeys

end Yulang.GeneralDeclarativeCompoundEndpoints338
