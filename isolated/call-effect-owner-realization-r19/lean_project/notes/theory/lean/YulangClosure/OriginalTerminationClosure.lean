import YulangClosure.NativeValueStructure

/-!
The persistent native extrusion-rewrite owner.

This is a source-grounded component of the ORIGINAL termination obligation,
not a declaration of `SourceProblem.InferenceTermination`.  The raw Value
pair cache survives changed Context identities and intrusion generations.
Its replacement admission updates diagnostics without clearing the retained
extrusion target.  A new changed extrusion can consequently be charged to a
previously unrewritten RAW endpoint pair, even in a growing graph.

The actual dispatch function is imported and used below.  The small memo
projection transcribes `record_typed_pair_admission` and
`retain_candidate_value_rewrite`; its history does not model rollback or
source-to-native construction.  Those boundaries are stated explicitly in
the companion note.  In particular, a finite source-derived supply of raw
pairs is NOT assumed here and is NOT concluded.
-/

namespace YulangClosure.OriginalTerminationClosure

open NativeValueStructure

/-- The payload is the native diagnostic update (direct witness/completion).
Other fields, including retained diagnostic children, are outside this
projection; the rewrite coordinate is never diagnostic state. -/
structure ValueMemo (D : Type) where
  rewrite : Option ValuePair
  diagnostic : D

abbrev MemoStore (D : Type) := ValuePair → Option (ValueMemo D)

def retained (store : MemoStore D) (pair : ValuePair) : Option ValuePair :=
  (store pair).bind ValueMemo.rewrite

/-- Exact rewrite-coordinate behavior of the replacing-admission branch.
An existing rewrite and its entire diagnostic-independent identity survive. -/
def recordAdmission (store : MemoStore D) (pair : ValuePair)
    (diagnostic : D) : MemoStore D :=
  fun key => if key = pair then
    match store pair with
    | none => some ⟨none, diagnostic⟩
    | some old => some {old with diagnostic := diagnostic}
  else store key

theorem recordAdmission_retained (store : MemoStore D)
    (pair : ValuePair) (diagnostic : D) :
    retained (recordAdmission store pair diagnostic) = retained store := by
  funext key
  by_cases same : key = pair
  · subst key
    cases selected : store pair <;> simp [retained, recordAdmission, selected]
  · simp [retained, recordAdmission, same]

/-- The native retained-write call rejects a missing Value memo or a
conflicting previous target.  Reinstalling the same target is an exact no-op. -/
def recordRewrite (store : MemoStore D) (pair target : ValuePair) :
    Option (MemoStore D) :=
  match store pair with
  | none => none
  | some old =>
    match old.rewrite with
    | some prior => if prior = target then some store else none
    | none => some fun key =>
        if key = pair then some {old with rewrite := some target} else store key

theorem recordRewrite_exact {store after : MemoStore D}
    {pair target : ValuePair} (written : recordRewrite store pair target = some after) :
    retained after pair = some target ∧
    (∀ key, key ≠ pair → retained after key = retained store key) ∧
    (∀ key old, retained store key = some old → retained after key = some old) := by
  unfold recordRewrite at written
  cases selected : store pair with
  | none => simp [selected] at written
  | some entry =>
    simp only [selected] at written
    cases previous : entry.rewrite with
    | none =>
      simp only [previous, Option.some.injEq] at written
      subst after
      refine ⟨?_, ?_, ?_⟩
      · simp [retained]
      · intro key different
        simp [retained, different]
      · intro key old found
        by_cases same : key = pair
        · subst key
          simp [retained, selected, previous] at found
        · simpa [retained, same] using found
    | some prior =>
      simp only [previous] at written
      split at written
      · rename_i same
        cases written
        subst prior
        exact ⟨by simp [retained, selected, previous], fun _ _ => rfl,
          fun _ _ found => found⟩
      · cases written

/-- The imported native dispatch, with its full request payload and exact
precedence, cannot enter ANY body after a retained raw-pair rewrite. -/
theorem retained_excludes_body (tables : Tables) (routing : Routing)
    (request : Request) (target : ValuePair) (candidate : routing.candidate = true)
    (saved : routing.retained request.pair = some target) (body : Local) :
    dispatch tables routing request ≠ .body body := by
  intro computed
  obtain ⟨_, alternative, _⟩ := (dispatch_body_iff tables routing request body).mp computed
  rcases alternative with legacy | ⟨_, absent⟩
  · simp [candidate] at legacy
  · rw [saved] at absent
    cases absent

/-- This covers a successful Context-prefix result as well.  It neither skips
Context nor equates Context discharge with the later raw-pair memo admission. -/
theorem retained_excludes_context_fallback
    (contexts : NativeContextExpansion.Tables) (fuel : Nat)
    (tables : Tables) (routing : Routing) (request : Request)
    (target : ValuePair) (candidate : routing.candidate = true)
    (saved : routing.retained request.pair = some target)
    (operation : Option ExtrusionRequest) :
    afterContext contexts fuel tables routing request ≠ some (.body (.fallback operation)) := by
  intro computed
  have routed := (after_context_exact computed).2
  exact retained_excludes_body tables routing request target candidate saved _ routed.symm

/-- The actually selected allocating branch requires an absent retained
rewrite, independently of current-pair generation and request Context. -/
theorem fallback_requires_unwritten {tables : Tables} {routing : Routing}
    {request : Request} {operation : Option ExtrusionRequest}
    (candidate : routing.candidate = true)
    (selected : dispatch tables routing request = .body (.fallback operation)) :
    routing.retained request.pair = none := by
  obtain ⟨_, alternative, _⟩ := (dispatch_body_iff tables routing request _).mp selected
  rcases alternative with legacy | exact
  · simp [candidate] at legacy
  · exact exact.2

/-- Ghost log of NEW changed-extrusion producers. It does not bound or alter
the native graph or preallocate a finite raw-pair universe. -/
structure RewriteState (D : Type) where
  store : MemoStore D
  births : List (ValuePair × ValuePair) := []

def RewriteState.Valid (s : RewriteState D) : Prop :=
  (s.births.map Prod.fst).Nodup ∧
  ∀ pair target, (pair, target) ∈ s.births → retained s.store pair = some target

def RewriteState.initial : RewriteState D := ⟨fun _ => none, []⟩

/-- Only mutations of the retained rewrite projection are recorded. All
source/FreshUse/Context/Replay/generation operations that leave the typed
memo unchanged erase to `unchanged`; this is not a full inference Step. -/
inductive RewriteStep : RewriteState D → RewriteState D → Prop
  | admission (s : RewriteState D) (pair : ValuePair) (diagnostic : D) :
      RewriteStep s {s with store := recordAdmission s.store pair diagnostic}
  | unchanged (s : RewriteState D) : RewriteStep s s
  | changed (s : RewriteState D) (tables : Tables) (routing : Routing)
      (request : Request) (operation : Option ExtrusionRequest) (target : ValuePair)
      (after : MemoStore D)
      (candidate : routing.candidate = true)
      (memo : routing.retained = retained s.store)
      (selected : dispatch tables routing request = .body (.fallback operation))
      (different : target ≠ request.pair)
      (written : recordRewrite s.store request.pair target = some after) :
      RewriteStep s ⟨after, (request.pair, target) :: s.births⟩

theorem rewrite_initial_valid : (RewriteState.initial (D := D)).Valid := by
  simp [RewriteState.initial, RewriteState.Valid]

theorem rewrite_step_valid {s u : RewriteState D}
    (step : RewriteStep s u) (valid : s.Valid) : u.Valid := by
  obtain ⟨unique, kept⟩ := valid
  cases step with
  | admission pair diagnostic =>
    refine ⟨unique, ?_⟩
    intro key target member
    rw [recordAdmission_retained]
    exact kept key target member
  | unchanged => exact ⟨unique, kept⟩
  | changed tables routing request operation target after candidate memo selected different written =>
    have empty := fallback_requires_unwritten candidate selected
    rw [memo] at empty
    have notSeen : request.pair ∉ s.births.map Prod.fst := by
      intro member
      obtain ⟨⟨key, old⟩, found, same⟩ := List.mem_map.mp member
      change key = request.pair at same
      subst key
      have recorded := kept request.pair old found
      rw [empty] at recorded
      cases recorded
    have publication := recordRewrite_exact written
    refine ⟨by simpa only [List.map_cons, List.nodup_cons] using And.intro notSeen unique, ?_⟩
    intro pair result member
    rcases List.mem_cons.mp member with same | old
    · cases same
      exact publication.1
    · exact publication.2.2 pair result (kept pair result old)

inductive RewriteRun : RewriteState D → RewriteState D → Prop
  | nil (s : RewriteState D) : RewriteRun s s
  | snoc {s u v : RewriteState D} : RewriteRun s u → RewriteStep u v → RewriteRun s v

theorem rewrite_run_valid {s u : RewriteState D}
    (run : RewriteRun s u) (valid : s.Valid) : u.Valid := by
  induction run with
  | nil => exact valid
  | snoc _ step ih => exact rewrite_step_valid step ih

/-- A finite-prefix, dynamically growing no-duplication result. No final
row-count, future-demand bound, cap, fuel or eventual drain receipt occurs. -/
theorem changed_extrusion_parents_nodup {s : RewriteState D}
    (run : RewriteRun RewriteState.initial s) : (s.births.map Prod.fst).Nodup :=
  (rewrite_run_valid run rewrite_initial_valid).1

theorem changed_extrusion_targets_persistent {s : RewriteState D}
    (run : RewriteRun RewriteState.initial s) :
    ∀ pair target, (pair, target) ∈ s.births → retained s.store pair = some target :=
  (rewrite_run_valid run rewrite_initial_valid).2

/-- Any later request carrying a previously rewritten raw pair is excluded
from a second extrusion-producing body, even under unrelated current-pair,
canonical-map, level, Context, source-set or demand observations. -/
theorem prior_changed_extrusion_excludes_later_body
    {s : RewriteState D} (run : RewriteRun RewriteState.initial s)
    {pair target : ValuePair} (earlier : (pair, target) ∈ s.births)
    (tables : Tables) (routing : Routing) (request : Request)
    (candidate : routing.candidate = true) (memo : routing.retained = retained s.store)
    (rawPair : request.pair = pair) (body : Local) :
    dispatch tables routing request ≠ .body body := by
  apply retained_excludes_body tables routing request target candidate
  rw [memo, rawPair]
  exact changed_extrusion_targets_persistent run pair target earlier

end YulangClosure.OriginalTerminationClosure
