import Yulang.GeneralRebaseDepthRefreshTrust286

/-! A selected scalar becomes known using its two retained normalized source
atoms. No audit fact is added and every other stored observation is kept. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthScalarMark286
open GeneralDictionaryOutputDepth252 (roles S)
private abbrev sourceSnapshot := GeneralDictionaryOutputDepth252.snapshot
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralCanonicalObservations (Recorded)
open GeneralRebaseDepthPhase286 (Hop)

structure Atoms (snap : GeneralNominalState.State) (n : Nat)
    (slot : Fin snap.base.slots) : Prop where
  name : snap.base.source slot = n
  upper : PresenceNormalForm.Atom.tyLe (.var slot) (.base .int) ∈ snap.base.ordinary
  lower : PresenceNormalForm.Atom.tyLe (.base .int) (.var slot) ∈ snap.base.ordinary

def Seed (snap : GeneralNominalState.State) (n : Nat) : Prop :=
  ∃ slot : Fin snap.base.slots, Atoms snap n slot

theorem retains {before after : GeneralNominalState.State}
    (r : GeneralNominalRefinements.Refines before after) {n : Nat}
    (there : Seed before n) : Seed after n := by
  obtain ⟨slot,atoms⟩ := there
  exact ⟨r.base.embed slot, (r.base.source slot).trans atoms.name,
    r.base.ordinary _ atoms.upper,r.base.ordinary _ atoms.lower⟩

variable {s : State roles} {n : Nat} {slot : Fin (snapshot s).base.slots}

theorem nonnominal (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n)
    (d : GeneralNominalState.Descriptor (snapshot s).base.slots) :
    (snapshot s).nominals slot ≠ some d := by
  intro yes
  exact missing ⟨slot,atoms.name,Or.inr ⟨d,yes⟩⟩

def view (atoms : Atoms (snapshot s) n slot) :
    GeneralNormalizedObservation.Snapshot (snapshot s).base where
  kinds := (snapshot s).view.kinds
  shapes := (snapshot s).view.shapes
  shapes_injective := (snapshot s).view.shapes_injective
  canonical := (snapshot s).view.canonical
  heads := fun i => if i = slot then .scalar .int else (snapshot s).view.heads i
  checked := by
    intro i term recorded
    change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
      (snapshot s).view.heads i).term = some term at recorded
    split at recorded
    · rename_i atSlot
      subst i
      cases Option.some.inj recorded
      exact .ordinary atoms.upper atoms.lower
    · exact (snapshot s).view.checked i term recorded

def target (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n) :
    GeneralNominalCandidates.Context :=
  { s.core.erased.current.context with
    state := { snapshot s with
      view := view atoms
      bodies_opaque := by
        intro i d held
        change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
          (snapshot s).view.heads i) = .deferred .unresolved
        split
        · rename_i same
          subst i
          exact (nonnominal atoms missing d held).elim
        · exact (snapshot s).bodies_opaque i d held } }

theorem selected (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n) :
    Known (target atoms missing).state n := by
  refine ⟨slot,atoms.name,Or.inl ?_⟩
  change (if slot = slot then GeneralNormalizedObservation.Head.scalar .int else
    (snapshot s).view.heads slot).node ≠ _
  simp [GeneralNormalizedObservation.Head.node]

theorem retains_known (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n) :
    ∀ i, Known (snapshot s) i → Known (target atoms missing).state i := by
  rintro name ⟨i,atName,visible|nominal⟩
  · by_cases same : i = slot
    · subst i
      exact (missing ⟨slot,atoms.name,Or.inl visible⟩).elim
    · refine ⟨i,atName,Or.inl ?_⟩
      change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
        (snapshot s).view.heads i).node ≠ _
      rwa [ite_eq_right same]
  · exact ⟨i,atName,Or.inr nominal⟩

theorem target_other (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n)
    {other : Nat} (different : other ≠ n) :
    Known (target atoms missing).state other ↔ Known (snapshot s) other := by
  refine ⟨?_,retains_known atoms missing other⟩
  rintro ⟨i,whereAt,known|nominal⟩
  · have notSlot : i ≠ slot := by
      intro eq
      exact different (whereAt.symm.trans ((congrArg (snapshot s).base.source eq).trans atoms.name))
    refine ⟨i,whereAt,Or.inl ?_⟩
    change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
      (snapshot s).view.heads i).node ≠ _ at known
    change ((snapshot s).view.heads i).node ≠ _
    simpa only [ite_eq_right notSlot] using known
  · exact ⟨i,whereAt,Or.inr nominal⟩

def refines (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n) :
    GeneralNominalRefinements.Refines (snapshot s) (target atoms missing).state where
  base := (GeneralNominalRefinements.refl (snapshot s)).base
  heads := (GeneralNominalRefinements.refl (snapshot s)).heads
  nominals := (GeneralNominalRefinements.refl (snapshot s)).nominals
  ordinary := fun _ member => member
  known := retains_known atoms missing
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

theorem mark_cache (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n)
    (old : CacheSound s (snapshot s)) (source : s.core.erased.source.state = sourceSnapshot)
    (small : n ≤ 1) : CacheSound s (target atoms missing).state := by
  intro o recorded
  cases recorded with
  | nominal i d held => exact old _ (Recorded.nominal (snapshot := snapshot s) i d held)
  | scalar i b held =>
    change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
      (snapshot s).view.heads i) = .scalar b at held
    by_cases same : i = slot
    · subst i
      have own : (if slot = slot then GeneralNormalizedObservation.Head.scalar .int else
        (snapshot s).view.heads slot) = .scalar .int := ite_eq_left rfl
      rw [own] at held
      cases held
      exact ⟨[],[],.source,.source,fun m _ supported => by
        have raw : GeneralNominalState.Models sourceSnapshot m := source ▸ supported.1
        have sourceCheck := (GeneralRebaseDepthGroundModels285.source_inputs m).mp raw
        change CommonNominalFullCarrier.Equivalent (m ((snapshot s).base.source slot)).1 S
        rw [atoms.name]
        have choices : n = 0 ∨ n = 1 := by omega
        rcases choices with rfl|rfl
        · exact sourceCheck.1
        · exact sourceCheck.2.1⟩
    · exact old _ (Recorded.scalar (snapshot := snapshot s) i b (by simpa only [ite_eq_right same] using held))
  | structural i k children held =>
    change (if i = slot then GeneralNormalizedObservation.Head.scalar .int else
      (snapshot s).view.heads i) = .structural k children at held
    by_cases same : i = slot
    · simp only [ite_eq_left same] at held
      cases held
    · exact old _ (Recorded.structural (snapshot := snapshot s) i k children (by simpa only [ite_eq_right same] using held))

def cert (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n)
    (old : CacheSound s (snapshot s)) (source : s.core.erased.source.state = sourceSnapshot)
    (small : n ≤ 1) : Refresh s (target atoms missing) where
  refines := refines atoms missing
  interpretation := rfl
  support := fun _ member => member
  constraints := fun _ valid => ⟨valid.1.1.1,valid.1.1.2.2⟩
  cache := mark_cache atoms missing old source small

theorem step (atoms : Atoms (snapshot s) n slot) (missing : ¬ Known (snapshot s) n)
    (old : CacheSound s (snapshot s)) (source : s.core.erased.source.state = sourceSnapshot)
    (small : n ≤ 1) : Hop s (refresh s (target atoms missing)) := by
  have present : n ∈ GeneralNominalState.sources (snapshot s) := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨slot,atoms.name⟩
  exact .refresh _ (cert atoms missing old source small) n present missing (selected atoms missing)

end Yulang.GeneralRebaseDepthScalarMark286
