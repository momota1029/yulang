import Yulang.GeneralDeclarativeI65I74AutomaticScopedElection487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (StepWire GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe)
open GeneralDeclarations (Declaration)
open Producer479 (Site)

def ExplicitOriginalPermissions487 (n : Nat) := List (Nat × CandidateVisitKey485 n)

def checkExplicitPermission487 {n : Nat} (rows : ExplicitOriginalPermissions487 n)
    (ordinal : Nat) (key : CandidateVisitKey485 n) : Bool :=
  decide ((ordinal,key) ∈ (show List (Nat × CandidateVisitKey485 n) from rows))

def originalPermissionStep487 (w : WrittenPattern460.Address × List WrittenPattern460.PhysicalOrigin.Pose) :
    StepWire := ⟨w.1,w.2⟩

/-- A row lists proper prefixes using exactly the same ordinal, original
argument, action, written pose, and prior coordinates. No old sign is
consulted by this structural test. -/
def checkExplicitPermissionRow487 {n : Nat} (rows : ExplicitOriginalPermissions487 n)
    (row : Nat × CandidateVisitKey485 n) : Bool :=
  match row.2.original, row.2.points with
  | [], _ | _, [] => false
  | a::moves, root::points =>
    originalSuffixPermitted487 (checkExplicitPermission487 rows row.1) ⟨row.2.argument,root,[],[]⟩
      ((a::moves).map originalPermissionStep487) points

def checkExplicitPermissionTable487 {n : Nat} (rows : ExplicitOriginalPermissions487 n) : Bool :=
  (show List (Nat × CandidateVisitKey485 n) from rows).all (checkExplicitPermissionRow487 rows)

private theorem written_steps_reconstructed_from_exact_geometry487 (steps : List StepWire) :
    (steps.map (fun w => (w.action,w.written))).map originalPermissionStep487 = steps := by
  induction steps with
  | nil => rfl
  | cons w rest ih =>
    cases w
    simp [originalPermissionStep487,ih]

theorem explicit_table_check_gives_all_prefix_permissions_before_any_geometry_read487
    {n : Nat} {rows : ExplicitOriginalPermissions487 n}
    (valid : checkExplicitPermissionTable487 rows = true)
    {s : GeneralDeclarativeI65.State} {pos : Positions n} (ord arg : Nat)
    (first : Site s pos) (v : GeometricVisit486 s pos)
    (nonempty : v.moves ≠ [])
    (terminal : checkExplicitPermission487 rows ord (exactGeometryKey486 arg first v) = true) :
    originalSuffixPermitted487 (checkExplicitPermission487 rows ord)
      (originalVisitAnchor487 arg first) v.moves v.points = true := by
  have mem : (ord,exactGeometryKey486 arg first v) ∈ (show List (Nat × CandidateVisitKey485 n) from rows) :=
    of_decide_eq_true terminal
  have each := List.all_eq_true.mp valid _ mem
  cases moves : v.moves with
  | nil => exact False.elim (nonempty moves)
  | cons a tail =>
    have rebuilt := written_steps_reconstructed_from_exact_geometry487 (a::tail)
    unfold checkExplicitPermissionRow487 exactGeometryKey486 at each
    simp only [moves,List.map_cons] at each
    change originalSuffixPermitted487 (checkExplicitPermission487 rows ord)
      (originalVisitAnchor487 arg first) (((a::tail).map (fun w => (w.action,w.written))).map
       originalPermissionStep487) v.points = true at each
    rw [rebuilt] at each
    exact each

theorem explicit_table_check_gives_roster_prefix_coherence487
    {n : Nat} {rows : ExplicitOriginalPermissions487 n}
    (valid : checkExplicitPermissionTable487 rows = true)
    (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) :
    OriginalRosterPermissionIsPrefixCoherent487 p gd pos rel palette (checkExplicitPermission487 rows) := by
  intro _ arg _ head v _ nonempty yes
  exact explicit_table_check_gives_all_prefix_permissions_before_any_geometry_read487 valid _ arg
    head.site v nonempty yes

/-- Decline an inconsistent input table before reading the selected
old geometry. A validated table grants no source authority by itself. -/
def readExplicitPrefixPreElection487 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (rows : ExplicitOriginalPermissions487 n) : Option PreElection485 :=
  if checkExplicitPermissionTable487 rows then
    readAutomaticScopedPreElection487 p gd pos rel (checkExplicitPermission487 rows)
  else none

theorem successful_explicit_prefix_entry_passes_structural_table_check487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {rows : ExplicitOriginalPermissions487 n}
    {out : PreElection485}
    (run : readExplicitPrefixPreElection487 p gd pos rel rows = some out) :
    checkExplicitPermissionTable487 rows = true ∧
    readAutomaticScopedPreElection487 p gd pos rel (checkExplicitPermission487 rows) = some out := by
  unfold readExplicitPrefixPreElection487 at run
  split at run
  · exact ⟨by assumption,run⟩
  · cases run

theorem backed_explicit_prior_table_replays_one_finite_tape_without_source_or_root_packet_inputs487
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (rows : ExplicitOriginalPermissions487 n) (structural : checkExplicitPermissionTable487 rows = true)
    (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (truth : ∀ ordinal key, (ordinal,key) ∈ (show List (Nat × CandidateVisitKey485 n) from rows) →
      Authorized ordinal key)
    (roots : AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords)
    (guard : ∀ i ∈ coords, GuardedObservationInput p.old.state.core pos rel i)
    (arity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (starts : ∀ i : Fin (visible485 p).length, ∀ argument root, coords[argument]? = some root →
      Nonempty (OriginalArgumentStart486 p gd pos i.val argument root)) :
    ∃ bits : List (Nat × Bool), readExplicitPrefixPreElection487 p gd pos rel rows = some (gate485 bits) := by
  obtain ⟨bits,run⟩ := independently_guarded_demand_and_prefix_authority_compile_checkable_automatic_tape487
    p gd pos rel coords (checkExplicitPermission487 rows) Authorized
    (fun ordinal key accepted => truth ordinal key (of_decide_eq_true accepted)) roots guard arity starts
    (explicit_table_check_gives_roster_prefix_coherence487 structural _ _ _ _ _)
  exact ⟨bits,by simp only [readExplicitPrefixPreElection487,structural,ite_true,run]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
