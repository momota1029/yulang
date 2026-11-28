import Yulang.GeneralDeclarativeI65I74ComputedOriginalRoots487
import Yulang.GeneralDeclarativeI65I74ScopedRosterCompatibility487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe requestRootCheck)
open GeneralDeclarations (Declaration)

/-- Start from actual old demand lowers, in demand order. The supplied
candidate permission is independent of the computed root and type graph. -/
def readAutomaticScopedPreElection487 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 := do
  let checks ← computedOriginalRootCertificates487 p.old.state.core pos rel
    (p.old.root.demand.arguments.map (·.lower))
  readScopedPreElection487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel) checks permit

theorem automatic_scoped_election_has_the_checked_exact_roots_and_tape487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {out : PreElection485}
    (ran : readAutomaticScopedPreElection487 p gd pos rel permit = some out) :
    ∃ roots rows,
      computedOriginalRootCertificates487 p.old.state.core pos rel (p.old.root.demand.arguments.map (·.lower)) =
        some roots ∧
      AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) (roots.map Checkpoint.which) ∧
      compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
        (roots.map Checkpoint.which) permit = some rows ∧
      readPlannedPreElection485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit) (rows.map fun x => (x.authoredOrdinal,x.packet)) = some out := by
  unfold readAutomaticScopedPreElection487 at ran
  cases h : computedOriginalRootCertificates487 p.old.state.core pos rel
      (p.old.root.demand.arguments.map (·.lower)) with
  | none => simp [h] at ran
  | some roots =>
    have direct : readScopedPreElection487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
        roots permit = some out := by simpa [h] using ran
    obtain ⟨safe,rows,compiled,replayed⟩ :=
      scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487 direct
    exact ⟨roots,rows,rfl,safe,compiled,replayed⟩

theorem independently_guarded_demand_and_prefix_authority_compile_checkable_automatic_tape487
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permission : ∀ ordinal key, permit ordinal key = true → Authorized ordinal key)
    (roots : AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords)
    (guard : ∀ i ∈ coords, GuardedObservationInput p.old.state.core pos rel i)
    (actualArity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (starts : ∀ i : Fin (visible485 p).length, ∀ argument root, coords[argument]? = some root →
      Nonempty (OriginalArgumentStart486 p gd pos i.val argument root))
    (coherent : OriginalRosterPermissionIsPrefixCoherent487 p gd pos rel
      (computedOriginalPalette486 p.old.state.core pos rel) permit) :
    ∃ bits : List (Nat × Bool), readAutomaticScopedPreElection487 p gd pos rel permit = some (gate485 bits) := by
  obtain ⟨nodes,made,own⟩ := given_exact_old_guarded_safe_roots_the_computer_returns_all_in_same_order487 roots guard
  have checked : requestRootCheck p pos rel nodes = true :=
    computed_original_roots_pass_unmodified_ordered_request_root_check487 _ _ _ _ _ made
  have enough : nodes.length = p.old.root.demand.arguments.length := by
    simpa only [List.length_map] using (all_checked_request_roots_carry_guards_and_exact_list_length487 checked).1
  let palette := computedOriginalPalette486 p.old.state.core pos rel
  have complete : CompletePalette486 p.old.state.core pos rel palette :=
    real_existing_graph_finitely_computes_its_verified_optional_palette486 _ _ _
  obtain ⟨rows,bits,_,_,computed⟩ :=
    independently_scoped_all_canonical_head_coordinates_produce_a_rechecked_whole_tape486
      p gd pos rel palette complete nodes permit Authorized permission checked enough actualArity
      (fun i arg j h => starts i arg j (by simpa only [own] using h))
  have same := scoped_roster_and_old_guarded_pre_election_have_identical_results487
    (gd := gd) complete nodes permit coherent
  refine ⟨bits,?_⟩
  simp only [readAutomaticScopedPreElection487,made]
  change readScopedPreElection487 p gd pos rel palette nodes permit = some (gate485 bits)
  rw [same]
  exact computed

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
