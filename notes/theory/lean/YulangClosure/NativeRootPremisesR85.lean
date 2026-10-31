import YulangClosure.ConstructedPhysicalRootR84

/-!
R85 candidate: source-drain publication keeps the Origin-attached receipt
pending; completion retains a distinct completed clone. The finite lifecycle
below preserves the full R57 Native inventory, including every competing
Origin and relation. It is an overapproximation of the admitted producer
operations, not an authenticated Rust execution or a whole-language model.

Source: candidate_context.rs 2284–2292, 3850–3875; lib.rs 14272–14320,
14960–15031; candidate_context.rs 3183–3218. No selector uniqueness,
ancestry, Root, Primitive, or completed attached receipt is assumed.
Construction only: execution/audits require the primary's separate gate.
-/
namespace YulangClosure.NativeRootPremisesR85

open ProviderNativeContextR57

variable {S T : Type} [DecidableEq S] [DecidableEq T]

/-- This is an invariant of the receipt lifecycle, not a typing definition. -/
def Pending (origins : List (Origin S T)) : Prop :=
  ∀ o, o ∈ origins → ∀ d, o.drain = some d → d.completed = false

theorem pending_nil : Pending ([] : List (Origin S T)) := by
  intro o member
  cases member

theorem pending_cons (o : Origin S T) (os : List (Origin S T)) :
    Pending (o :: os) ↔
      (∀ d, o.drain = some d → d.completed = false) ∧ Pending os := by
  constructor
  · intro h
    exact ⟨fun d hd => h o (by simp) d hd,
      fun x hx d hd => h x (by simp only [List.mem_cons]; exact Or.inr hx) d hd⟩
  · rintro ⟨head, tail⟩ x member d hd
    rcases List.mem_cons.mp member with equal | member
    · subst x
      exact head d hd
    · exact tail x member d hd

theorem pending_append_seed (os : List (Origin S T)) (h : Pending os)
    (state relation : Nat) (occurrence : S) (slot : Nat) :
    Pending (os ++ [⟨state, relation, occurrence, slot, none⟩]) := by
  intro o member d hd
  rcases List.mem_append.mp member with old | fresh
  · exact h o old d hd
  · have equal : o = (⟨state, relation, occurrence, slot, none⟩ : Origin S T) := by
      simpa only [List.mem_singleton] using fresh
    subst o
    cases hd

/-- Exact indexed Origin publication shape: missing index/identity/empty-slot
checks retain the old list. The published receipt starts completed=false.
The state/slot coordinates are retained from the source encoding. -/
def attachAt : List (Origin S T) → Nat → Drain S T → List (Origin S T)
  | [], _, _ => []
  | o :: os, 0, d =>
      if o.relation = d.createdSeed ∧ o.occurrence = d.cause ∧ o.drain = none then
        {o with drain := some {d with completed := false}} :: os
      else o :: os
  | o :: os, index + 1, d => o :: attachAt os index d

theorem pending_attachAt (os : List (Origin S T)) (index : Nat)
    (d : Drain S T) (h : Pending os) : Pending (attachAt os index d) := by
  revert index d h
  induction os with
  | nil => intro index d h; exact pending_nil
  | cons o os ih =>
      intro index d h
      obtain ⟨head, tail⟩ := (pending_cons o os).mp h
      cases index with
      | zero =>
          simp only [attachAt]
          split
          · apply (pending_cons _ os).mpr
            refine ⟨?_, tail⟩
            intro receipt equal
            have same : {d with completed := false} = receipt := Option.some.inj equal
            subst receipt
            rfl
          · exact (pending_cons o os).mpr ⟨head, tail⟩
      | succ index =>
          exact (pending_cons o (attachAt os index d)).mpr ⟨head, ih index d tail⟩

theorem pending_take (os : List (Origin S T)) (index : Nat)
    (h : Pending os) : Pending (os.take index) := by
  revert os h
  induction index with
  | zero => intro os h; exact pending_nil
  | succ index ih =>
      intro os h
      cases os with
      | nil => exact pending_nil
      | cons o os =>
          obtain ⟨head, tail⟩ := (pending_cons o os).mp h
          exact (pending_cons o (os.take index)).mpr ⟨head, ih os tail⟩

structure Producer (S T : Type) where
  native : Native S T
  completions : List (Drain S T)

/-- A source-aligned lifecycle with arbitrary retained non-Origin inventories.
Seed appends an unreceipted Origin; publication is indexed; completion only
appends a completed clone; rollback truncates; other owner actions preserve
Origins. It admits duplicates and relation collisions. Authentic extraction
and exhaustiveness of this source-operation abstraction remain source duties.
-/
inductive Reachable (base : Native S T) : Producer S T → Prop
  | initial : Reachable base ⟨{base with origins := []}, []⟩
  | seed (p : Producer S T) (h : Reachable base p)
      (relation : Nat) (occurrence : S) (slot : Nat) :
      Reachable base ⟨{p.native with origins := p.native.origins ++
        [⟨p.native.state, relation, occurrence, slot, none⟩]}, p.completions⟩
  | publish (p : Producer S T) (h : Reachable base p) (index : Nat) (d : Drain S T) :
      Reachable base ⟨{p.native with origins := attachAt p.native.origins index d}, p.completions⟩
  | complete (p : Producer S T) (h : Reachable base p) (d : Drain S T) :
      Reachable base ⟨p.native, p.completions ++ [{d with completed := true}]⟩
  | rollback (p : Producer S T) (h : Reachable base p) (index : Nat) :
      Reachable base ⟨{p.native with origins := p.native.origins.take index}, p.completions⟩
  | preserve (p : Producer S T) (h : Reachable base p) (next : Native S T)
      (sameOrigins : next.origins = p.native.origins) :
      Reachable base ⟨next, p.completions⟩

theorem reachable_pending (base : Native S T) (p : Producer S T)
    (h : Reachable base p) : Pending p.native.origins := by
  induction h with
  | initial => exact pending_nil
  | seed p _ relation occurrence slot ih =>
      exact pending_append_seed p.native.origins ih p.native.state relation occurrence slot
  | publish p _ index d ih => exact pending_attachAt p.native.origins index d ih
  | complete _ _ _ ih => exact ih
  | rollback p _ index ih => exact pending_take p.native.origins index ih
  | preserve _ _ next sameOrigins ih => simpa only [sameOrigins] using ih

/-- Necessary attached-receipt premise of native checked_internal_use_root.
Additional native identity/uniqueness tests cannot repair a false flag. -/
theorem reachable_no_completed_attachment (base : Native S T) (p : Producer S T)
    (h : Reachable base p) (o : Origin S T) (member : o ∈ p.native.origins)
    (d : Drain S T) (attached : o.drain = some d) : d.completed ≠ true := by
  have pending := reachable_pending base p h o member d attached
  rw [pending]
  decide

/-- Native candidate predicate retains all origins with the requested
occurrence and typed pair, without the R84 state/slot prefilter. R57 relation
encoding/authentication is still external to this finite reader. -/
def nativeCandidates (n : Native S T) (occurrence : S)
    (lower upper : Endpoint T) : List (Origin S T) :=
  n.origins.filter (fun o => decide (o.occurrence = occurrence) &&
    match relationRead n o.relation with
    | some r => decide (r.lower = lower ∧ r.upper = upper)
    | none => false)

/-- Executable necessary gate of the native checked-root reader. All original
competitors are enumerated; the receipt flag is checked on the same Origin.
Other native receipt identity guards are omitted only in this overapproximate
gate, so rejection here entails rejection of their conjunction. -/
def checkedRootGate (n : Native S T) (occurrence : S)
    (lower upper : Endpoint T) : Option (Origin S T) :=
  match nativeCandidates n occurrence lower upper with
  | [o] => match o.drain with
    | some d => if d.completed then some o else none
    | none => none
  | _ => none

theorem pending_rejects_checkedRootGate (n : Native S T) (h : Pending n.origins)
    (occurrence : S) (lower upper : Endpoint T) :
    checkedRootGate n occurrence lower upper = none := by
  unfold checkedRootGate
  cases selected : nativeCandidates n occurrence lower upper with
  | nil => rfl
  | cons o rest =>
      cases rest with
      | cons second tail => rfl
      | nil =>
          have member : o ∈ nativeCandidates n occurrence lower upper := by
            rw [selected]
            simp
          have retained : o ∈ n.origins := (List.mem_filter.mp member).1
          cases attached : o.drain with
          | none => rfl
          | some d =>
              have pending := h o retained d attached
              simp [attached, pending]

theorem reachable_rejects_checkedRootGate (base : Native S T) (p : Producer S T)
    (h : Reachable base p) (occurrence : S) (lower upper : Endpoint T) :
    checkedRootGate p.native occurrence lower upper = none :=
  pending_rejects_checkedRootGate p.native (reachable_pending base p h) occurrence lower upper

/-- Apply the lifecycle result to the unchanged R84 Primitive on the same
retained inventory and Records. Its candidate singleton proves membership;
its attached-drain equation and completed=true then contradict Pending.
No Origin is discarded and no global uniqueness assumption is introduced. -/
theorem pending_blocks_R84_primitive
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T) (pending : Pending n.origins) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory n q i index d := by
  intro h
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  have member : d.origin ∈ ConstructedPhysicalRootR84.originCandidates n d.occurrence d.route := by
    rw [hcandidates]
    simp
  have retained : d.origin ∈ n.origins := (List.mem_filter.mp member).1
  have flag := pending d.origin retained d.drain hdrain
  rw [hdone] at flag
  cases flag

theorem reachable_blocks_R84_primitive
    (base : Native S T) (p : Producer S T) (h : Reachable base p)
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory p.native q i index d :=
  pending_blocks_R84_primitive s inventory p.native q i index d (reachable_pending base p h)

end YulangClosure.NativeRootPremisesR85
