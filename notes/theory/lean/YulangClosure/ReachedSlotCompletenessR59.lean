import YulangClosure.ReachedSlotSearchR58

/-! Candidate completeness for the exact R58 operational relation. Primitive
readers and successful Run remain explicit; no Rust interpretation is asserted. -/
namespace YulangClosure.ReachedSlotCompletenessR59
open ReachedSlotSearchR58
variable {S T : Type} [DecidableEq S] [DecidableEq T]

/-- A source-indexed single checked expansion, without a global scheduling
assumption. Branch-local freshness is the same condition as R58.Checked. -/
inductive Hop (e : Readers S T) (q : Query) : Branch S T → Branch S T → Prop where
  | support {b v index family ordinal}
      (atSupport : b.endpoint = .support index)
      (read : e.views index = .ok v) (owned : v.state = e.state ∧ v.index = index)
      (closed : v.tail = none) (member : (family, ordinal) ∈ v.allowed.zipIdx)
      (ordinalFits : ordinal ≤ 2^32-1)
      (fresh : ProviderNativeContextR57.EffectEndpoint.annotationMember index ordinal ∉ b.seen) :
      Hop e q b (child b (.annotationMember index ordinal) (supportStep e v family ordinal) b.useRoot)
  | physical {b row c p root bounds}
      (atRow : b.endpoint = .row row) (read : e.rows row = .ok bounds)
      (member : c ∈ cells bounds) (fresh : c.target ∉ b.seen)
      (edge : e.physical row c = .ok p) (owner : policy e q.mode b p = .ok root) :
      Hop e q b (child b c.target (.physical p) root)

inductive Trace (e : Readers S T) (q : Query) : Branch S T → Branch S T → Prop where
  | refl (b) : Trace e q b b
  | next {b c d} : Hop e q b c → Trace e q c d → Trace e q b d

omit [DecidableEq S] in
theorem hop_seen (e : Readers S T) (q : Query) (b c : Branch S T) (h : Hop e q b c) :
    c.seen = c.endpoint :: b.seen := by cases h <;> rfl

omit [DecidableEq S] in
theorem hop_fresh (e : Readers S T) (q : Query) (b c : Branch S T) (h : Hop e q b c) :
    c.endpoint ∉ b.seen := by cases h <;> assumption

omit [DecidableEq S] in
theorem trace_trans (e : Readers S T) (q : Query) (a b c : Branch S T)
    (first : Trace e q a b) (last : Trace e q b c) : Trace e q a c := by
  induction first with
  | refl => exact last
  | next hop tail ih => exact .next hop (ih last)

omit [DecidableEq S] in
theorem checked_trace (e : Readers S T) (q : Query) (b : Branch S T) (checked : Checked e q b) :
    Trace e q (initial q) b := by
  induction checked with
  | root => exact .refl _
  | support prior atSupport read owned closed member fits fresh ih =>
      exact trace_trans e q _ _ _ ih (.next (.support atSupport read owned closed member fits fresh) (.refl _))
  | physical prior atRow read member fresh edge owner ih =>
      exact trace_trans e q _ _ _ ih (.next (.physical atRow read member fresh edge owner) (.refl _))

omit [DecidableEq S] in
theorem checked_endpoint_seen (e : Readers S T) (q : Query) (b : Branch S T) (checked : Checked e q b) :
    b.endpoint ∈ b.seen := by
  cases checked with
  | root => exact List.mem_cons_self
  | support => exact List.mem_cons_self
  | physical => exact List.mem_cons_self

omit [DecidableEq S] in
theorem trace_refl_or_endpoint_fresh (e : Readers S T) (q : Query) (b goal : Branch S T)
    (trace : Trace e q b goal) : b = goal ∨ goal.endpoint ∉ b.seen := by
  induction trace with
  | refl => exact Or.inl rfl
  | @next b c goal hop tail ih =>
      apply Or.inr
      rcases ih with same | fresh
      · subst goal; exact hop_fresh e q b c hop
      · intro member
        apply fresh
        rw [hop_seen e q b c hop]
        exact List.mem_cons_of_mem _ member

omit [DecidableEq S] in
theorem target_trace_is_reflexive (e : Readers S T) (q : Query) (b goal : Branch S T)
    (trace : Trace e q b goal) (seen : b.endpoint ∈ b.seen)
    (atTarget : b.endpoint = q.target) (terminal : goal.endpoint = q.target) : b = goal := by
  rcases trace_refl_or_endpoint_fresh e q b goal trace with same | fresh
  · exact same
  · exact False.elim (fresh (by simpa [terminal,atTarget] using seen))

def Pending (e : Readers S T) (q : Query) (goal : Branch S T) (branches : List (Branch S T)) : Prop :=
  ∃ b ∈ branches, Trace e q b goal

def Active (e : Readers S T) (q : Query) (goal : Branch S T) : Phase S T → Prop
  | .pop => False
  | .support b v rest => ∃ family ordinal, (family,ordinal) ∈ rest ∧
      ProviderNativeContextR57.EffectEndpoint.annotationMember v.index ordinal ∉ b.seen ∧
      Trace e q (child b (.annotationMember v.index ordinal) (supportStep e v family ordinal) b.useRoot) goal
  | .physical b row rest => ∃ c ∈ rest, c.target ∉ b.seen ∧
      ∃ p root, e.physical row c = .ok p ∧ policy e q.mode b p = .ok root ∧
        Trace e q (child b c.target (.physical p) root) goal

def Frontier (e : Readers S T) (q : Query) (goal : Branch S T) : State S T → Prop
  | .live s => goal ∈ s.results ∨ Pending e q goal s.pending ∨ Active e q goal s.phase
  | .success results => goal ∈ results
  | .failure _ => True

omit [DecidableEq S] in
theorem pending_cons (e : Readers S T) (q : Query) (goal head : Branch S T) (rest : List (Branch S T)) :
    Pending e q goal (head :: rest) ↔ Trace e q head goal ∨ Pending e q goal rest := by
  constructor
  · rintro ⟨b,member,trace⟩
    rcases List.mem_cons.mp member with same | later
    · subst b; exact Or.inl trace
    · exact Or.inr ⟨b,later,trace⟩
  · rintro (trace | ⟨b,member,trace⟩)
    · exact ⟨head,List.mem_cons_self,trace⟩
    · exact ⟨b,List.mem_cons_of_mem _ member,trace⟩

omit [DecidableEq S] in
theorem support_frontier (e : Readers S T) (q : Query) (b goal : Branch S T)
    (index : Nat) (v : ProviderNativeContextR57.View S)
    (trace : Trace e q b goal) (different : b.endpoint ≠ q.target)
    (terminal : goal.endpoint = q.target) (atSupport : b.endpoint = .support index)
    (read : e.views index = .ok v) : Active e q goal (.support b v v.allowed.zipIdx) := by
  cases trace with
  | refl => exact False.elim (different terminal)
  | next hop tail =>
    cases hop with
    | support atSupport' read' owned closed member fits fresh =>
      have sameIndex := atSupport.symm.trans atSupport'
      cases sameIndex
      have sameView := Except.ok.inj (read.symm.trans read')
      cases sameView
      exact ⟨_,_,member,by simpa [owned.2] using fresh,by simpa [owned.2] using tail⟩
    | physical atRow read' member fresh edge owner =>
      rw [atSupport] at atRow
      cases atRow

omit [DecidableEq S] in
theorem physical_frontier (e : Readers S T) (q : Query) (b goal : Branch S T)
    (row : Nat) (bounds : ProviderNativeContextR57.Bounds Endpoint)
    (trace : Trace e q b goal) (different : b.endpoint ≠ q.target)
    (terminal : goal.endpoint = q.target) (atRow : b.endpoint = .row row)
    (read : e.rows row = .ok bounds) : Active e q goal (.physical b row (cells bounds)) := by
  cases trace with
  | refl => exact False.elim (different terminal)
  | next hop tail =>
    cases hop with
    | physical atRow' read' member fresh edge owner =>
      have sameIndex := atRow.symm.trans atRow'
      cases sameIndex
      have sameBounds := Except.ok.inj (read.symm.trans read')
      cases sameBounds
      exact ⟨_,member,fresh,_,_,edge,owner,tail⟩
    | support atSupport read' owned closed member fits fresh =>
      rw [atRow] at atSupport
      cases atSupport

omit [DecidableEq S] in
theorem leaf_cannot_complete (e : Readers S T) (q : Query) (b goal : Branch S T)
    (trace : Trace e q b goal) (different : b.endpoint ≠ q.target) (terminal : goal.endpoint = q.target)
    (notRow : ∀ index, b.endpoint ≠ .row index) (notSupport : ∀ index, b.endpoint ≠ .support index) : False := by
  cases trace with
  | refl => exact different terminal
  | next hop tail =>
    cases hop with
    | physical atRow read member fresh edge owner => exact notRow _ atRow
    | support atSupport read owned closed member fits fresh => exact notSupport _ atSupport


omit [DecidableEq S] in
theorem move_preserves_frontier (e : Readers S T) (q : Query) (limits : Limits)
    (s : Live S T) (t : State S T) (move : Move e q limits s t)
    (goal : Branch S T) (terminal : goal.endpoint = q.target)
    (valid : Invariant e q (.live s)) (frontier : Frontier e q goal (.live s)) : Frontier e q goal t := by
  cases move with
  | done =>
    rcases frontier with found | ⟨b,impossible,trace⟩ | impossible
    · exact found
    · cases impossible
    · exact False.elim impossible
  | target atTarget charged allocated =>
    rename_i r r' r'' b pending
    rcases frontier with impossible | before | impossible
    · cases impossible
    · rcases (pending_cons e q goal b pending).mp before with trace | later
      · have same := target_trace_is_reflexive e q b goal trace
          (checked_endpoint_seen e q b (valid.1 b List.mem_cons_self)) atTarget terminal
        exact Or.inl (List.mem_singleton.mpr same.symm)
      · exact Or.inr (Or.inl later)
    · exact False.elim impossible
  | support different atSupport charged read owned closed =>
    rename_i r r' b pending results index v
    rcases frontier with found | before | impossible
    · exact Or.inl found
    · rcases (pending_cons e q goal b pending).mp before with trace | later
      · exact Or.inr (Or.inr (support_frontier e q b goal index v trace different terminal atSupport read))
      · exact Or.inr (Or.inl later)
    · exact False.elim impossible
  | row different atRow charged read =>
    rename_i r r' b pending results index bounds
    rcases frontier with found | before | impossible
    · exact Or.inl found
    · rcases (pending_cons e q goal b pending).mp before with trace | later
      · exact Or.inr (Or.inr (physical_frontier e q b goal index bounds trace different terminal atRow read))
      · exact Or.inr (Or.inl later)
    · exact False.elim impossible
  | leaf different notRow notSupport charged =>
    rename_i r r' b pending results
    rcases frontier with found | before | impossible
    · exact Or.inl found
    · rcases (pending_cons e q goal b pending).mp before with trace | later
      · exact False.elim (leaf_cannot_complete e q b goal trace different terminal notRow notSupport)
      · exact Or.inr (Or.inl later)
    · exact False.elim impossible
  | supportDone =>
    rcases frontier with found | before | ⟨family,ordinal,impossible,fresh,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl before)
    · cases impossible
  | supportSkip charged fits seen =>
    rename_i r r' b v f index rest pending results
    rcases frontier with found | before | ⟨family,ordinal,member,fresh,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl before)
    · rcases List.mem_cons.mp member with same | later
      · cases same
        exact False.elim (fresh seen)
      · exact Or.inr (Or.inr ⟨family,ordinal,later,fresh,trace⟩)
  | supportPush charged fits nativeFits fresh allocated =>
    rename_i r r' r'' b v f index rest pending results
    rcases frontier with found | before | ⟨family,ordinal,member,wantedFresh,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl ((pending_cons e q goal _ pending).mpr (Or.inr before)))
    · rcases List.mem_cons.mp member with same | later
      · cases same
        exact Or.inr (Or.inl ((pending_cons e q goal _ pending).mpr (Or.inl trace)))
      · exact Or.inr (Or.inr ⟨family,ordinal,later,wantedFresh,trace⟩)
  | rowDone =>
    rcases frontier with found | before | ⟨c,impossible,fresh,p,root,edge,owner,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl before)
    · cases impossible
  | rowSkip charged seen =>
    rename_i r r' b row c rest pending results
    rcases frontier with found | before | ⟨wanted,member,fresh,p,root,edge,owner,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl before)
    · rcases List.mem_cons.mp member with same | later
      · subst wanted
        exact False.elim (fresh seen)
      · exact Or.inr (Or.inr ⟨wanted,later,fresh,p,root,edge,owner,trace⟩)
  | rowPush charged fresh edge owner allocated =>
    rename_i r r' r'' b row c rest pending results p root
    rcases frontier with found | before | ⟨wanted,member,wantedFresh,wp,wr,wantedEdge,wantedOwner,trace⟩
    · exact Or.inl found
    · exact Or.inr (Or.inl ((pending_cons e q goal _ pending).mpr (Or.inr before)))
    · rcases List.mem_cons.mp member with same | later
      · subst wanted
        have samePhysical := Except.ok.inj (edge.symm.trans wantedEdge)
        subst wp
        have sameRoot := Except.ok.inj (owner.symm.trans wantedOwner)
        subst wr
        exact Or.inr (Or.inl ((pending_cons e q goal _ pending).mpr (Or.inl trace)))
      · exact Or.inr (Or.inr ⟨wanted,later,wantedFresh,wp,wr,wantedEdge,wantedOwner,trace⟩)

omit [DecidableEq S] in
theorem step_preserves_frontier (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (step : Step e q limits s t) (goal : Branch S T)
    (terminal : goal.endpoint = q.target) (valid : Invariant e q s)
    (frontier : Frontier e q goal s) : Frontier e q goal t := by
  cases step with
  | move move => exact move_preserves_frontier e q limits _ _ move goal terminal valid frontier
  | failure fault => trivial

omit [DecidableEq S] in
theorem run_preserves_frontier (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (run : Run e q limits s t) (goal : Branch S T)
    (terminal : goal.endpoint = q.target) (valid : Invariant e q s)
    (frontier : Frontier e q goal s) : Frontier e q goal t := by
  induction run with
  | refl => exact frontier
  | next first rest ih =>
    exact ih (ReachedSlotSearchR58.step_preserves_checked e q limits _ _ first valid)
      (step_preserves_frontier e q limits _ _ first goal terminal valid frontier)

omit [DecidableEq S] in
theorem initial_invariant (e : Readers S T) (q : Query) (r : Resource) :
    Invariant e q (.live ⟨r,[initial q],[],.pop⟩) := by
  refine ⟨?_,?_,trivial⟩
  · intro b member
    have same := List.mem_singleton.mp member
    subst b
    exact Checked.root
  · intro b impossible
    cases impossible

omit [DecidableEq S] in
theorem initial_frontier (e : Readers S T) (q : Query) (r : Resource)
    (goal : Branch S T) (checked : Checked e q goal) :
    Frontier e q goal (.live ⟨r,[initial q],[],.pop⟩) :=
  Or.inr (Or.inl ⟨initial q,by simp,checked_trace e q goal checked⟩)

/- Full candidate converse, with no queued/Present or assumed coverage premise.
Every complete successful initial Run returns every Checked target branch. -/
omit [DecidableEq S] in
theorem initial_success_contains_every_checked_target (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked e q goal) (terminal : goal.endpoint = q.target) :
    goal ∈ results :=
  run_preserves_frontier e q limits _ _ run goal terminal (initial_invariant e q r)
    (initial_frontier e q r goal checked)

/- Exact equality of the operationally returned candidate predicate and the
original R58.Checked terminal predicate, conditional only on actual success. -/
omit [DecidableEq S] in
theorem successful_results_exactly_checked_targets (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) : goal ∈ results ↔ Checked e q goal ∧ goal.endpoint = q.target := by
  constructor
  · exact successful_results_checked e q limits r results run goal
  · rintro ⟨checked,terminal⟩
    exact initial_success_contains_every_checked_target e q limits r results run goal checked terminal


omit [DecidableEq S] in
theorem initial_run_prefix_covers_every_candidate (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (state : State S T)
    (segment : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) state)
    (goal : Branch S T) (checked : Checked e q goal) (terminal : goal.endpoint = q.target) :
    Frontier e q goal state :=
  run_preserves_frontier e q limits _ _ segment goal terminal (initial_invariant e q r)
    (initial_frontier e q r goal checked)

omit [DecidableEq S] in
theorem run_trans (e : Readers S T) (q : Query) (limits : Limits) (a b c : State S T)
    (first : Run e q limits a b) (last : Run e q limits b c) : Run e q limits a c := by
  induction first with
  | refl => exact last
  | next step tail ih => exact .next step (ih last)

/-- R2's omitted-member state cannot be reached from the genuine initial state.
The same local state was permitted by R1's weaker soundness invariant. -/
theorem r2_omitted_candidate_state_unreachable (r : Resource) :
    ¬ Run fixtureReaders fixtureCatchQuery nativeLimits
      (.live ⟨r,[initial fixtureCatchQuery],[],.pop⟩)
      (.live ⟨resourceAt 0 8,[],[],.physical fixtureBranch 6 []⟩) := by
  intro segment
  have counter := soundness_invariant_allows_omitted_candidate
  have completed := run_trans fixtureReaders fixtureCatchQuery nativeLimits _ _ _ segment counter.2.2.1
  have member := initial_success_contains_every_checked_target fixtureReaders fixtureCatchQuery nativeLimits
    r [] completed fixtureChild counter.2.1 rfl
  cases member

omit [DecidableEq S] in
theorem competing_checked_targets_forbid_success (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T)) (first second : Branch S T)
    (firstChecked : Checked e q first) (secondChecked : Checked e q second)
    (firstTarget : first.endpoint = q.target) (secondTarget : second.endpoint = q.target)
    (different : first ≠ second) :
    ¬ Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results) := by
  intro run
  have firstMember := initial_success_contains_every_checked_target e q limits r results run first firstChecked firstTarget
  have secondMember := initial_success_contains_every_checked_target e q limits r results run second secondChecked secondTarget
  have count := successful_results_never_ambiguous e q limits r results run
  cases results with
  | nil => cases firstMember
  | cons head rest =>
    cases rest with
    | nil => exact different ((List.mem_singleton.mp firstMember).trans (List.mem_singleton.mp secondMember).symm)
    | cons next tail => simp at count

omit [DecidableEq S] in
theorem branch_cycle_cannot_complete (e : Readers S T) (q : Query) (b c : Branch S T)
    (seen : b.endpoint ∈ b.seen) (hop : Hop e q b c) : ¬ Trace e q c b := by
  intro loop
  rcases trace_refl_or_endpoint_fresh e q c b loop with same | fresh
  · subst c
    exact hop_fresh e q b b hop seen
  · apply fresh
    rw [hop_seen e q b c hop]
    exact List.mem_cons_of_mem _ seen

/-- Complete candidate enumeration applied to the existing consumer inputs.
The primitive LocalDecode/source correspondence premise remains explicit. -/
theorem complete_candidates_apply_existing_consumer (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked e q goal) (terminal : goal.endpoint = q.target)
    (m : AuthenticatedResidualConsumerR49.Inputs Nat (ProviderNativeContextR57.Key S T) ProviderNativeContextR57.Fact)
    (decode : LocalDecode e m) :
    goal ∈ results ∧
    AuthenticatedResidualConsumerR49.pathCheck m (encodedEndpoint e q.root)
      (goal.steps.map ProviderNativeContextR57.step) (encodedEndpoint e q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival m (encodedEndpoint e q.target) (encodedEndpoint e q.root) := by
  have member := initial_success_contains_every_checked_target e q limits r results run goal checked terminal
  exact ⟨member,successful_paths_refine_existing_consumer e q limits r results run m decode goal member⟩

/- Every explicit original Support member with a continuation remains covered
through the full loop and all subsequent successful worklist prefixes. -/
omit [DecidableEq S] in
theorem complete_support_member_generation (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (pending previous results : List (Branch S T))
    (b goal : Branch S T) (v : ProviderNativeContextR57.View S) (family : S) (ordinal : Nat)
    (member : (family,ordinal) ∈ v.allowed.zipIdx)
    (fresh : ProviderNativeContextR57.EffectEndpoint.annotationMember v.index ordinal ∉ b.seen)
    (continuation : Trace e q
      (child b (.annotationMember v.index ordinal) (supportStep e v family ordinal) b.useRoot) goal)
    (terminal : goal.endpoint = q.target)
    (valid : Invariant e q (.live ⟨r,pending,previous,.support b v v.allowed.zipIdx⟩))
    (run : Run e q limits (.live ⟨r,pending,previous,.support b v v.allowed.zipIdx⟩) (.success results)) :
    goal ∈ results :=
  run_preserves_frontier e q limits _ _ run goal terminal valid
    (Or.inr (Or.inr ⟨family,ordinal,member,fresh,continuation⟩))

def mixedCell : Cell := ⟨.atom,0,.support 0⟩
def mixedBounds : ProviderNativeContextR57.Bounds Endpoint := ⟨[],[],[.support 0],[]⟩
def mixedBound : ProviderNativeContextR57.Bound Nat := ⟨.effect 8,.positive,.effect (.support 0)⟩
def mixedSlot : ProviderNativeContextR57.Slot := ⟨.effect 8,.effectLowerAtom,0⟩
def mixedPhysical : ProviderNativeContextR57.Physical Nat :=
  ⟨0,0,⟨1,mixedBound,some 0⟩,⟨1,0,mixedBound,mixedSlot,mixedSlot,mixedBound⟩,0,[]⟩
def mixedReaders : Readers Nat Nat :=
  { fixtureReaders with
    rows := fun row => if row = 8 then .ok mixedBounds else fixtureReaders.rows row
    physical := fun row c => if row = 8 ∧ c = mixedCell then .ok mixedPhysical else fixtureReaders.physical row c }
def mixedQuery : Query := ⟨.row 8,.annotationMember 0 0,.catchSearch⟩
def mixedRoot : Branch Nat Nat := initial mixedQuery
def mixedSupport : Branch Nat Nat := child mixedRoot (.support 0) (.physical mixedPhysical) none
def mixedGoal : Branch Nat Nat := child mixedSupport (.annotationMember 0 0)
  (supportStep mixedReaders ProviderNativeContextR57.fixtureView 7 0) none

theorem mixed_physical_support_candidate_checked : Checked mixedReaders mixedQuery mixedGoal := by
  apply Checked.support (v := ProviderNativeContextR57.fixtureView) (index := 0)
    (family := 7) (ordinal := 0)
  · exact .physical (b := mixedRoot) (row := 8) (c := mixedCell) (p := mixedPhysical) (root := none)
      (bounds := mixedBounds) Checked.root rfl rfl (by decide) (by decide) rfl rfl
  · rfl
  · rfl
  · exact ⟨rfl,rfl⟩
  · rfl
  · decide
  · decide
  · decide

theorem mixed_physical_support_success :
    Run mixedReaders mixedQuery nativeLimits
      (.live ⟨resourceAt 0 12,[mixedRoot],[],.pop⟩) (.success [mixedGoal]) := by
  refine .next (t := .live ⟨resourceAt 2 12,[],[],.physical mixedRoot 8 [mixedCell]⟩) (.move ?_) ?_
  · exact .row (bounds := mixedBounds) (by decide) rfl rfl rfl
  refine .next (t := .live ⟨resourceAt 3 9,[mixedSupport],[],.physical mixedRoot 8 []⟩) (.move ?_) ?_
  · exact .rowPush (r' := resourceAt 3 12) rfl (by decide) rfl rfl rfl
  refine .next (t := .live ⟨resourceAt 3 9,[mixedSupport],[],.pop⟩) (.move .rowDone) ?_
  refine .next (t := .live ⟨resourceAt 7 9,[],[],.support mixedSupport ProviderNativeContextR57.fixtureView [(7,0)]⟩) (.move ?_) ?_
  · exact .support (by decide) rfl rfl rfl ⟨rfl,rfl⟩ rfl
  refine .next (t := .live ⟨resourceAt 8 6,[mixedGoal],[],.support mixedSupport ProviderNativeContextR57.fixtureView []⟩) (.move ?_) ?_
  · exact .supportPush (r' := resourceAt 8 9) rfl (by decide) (by decide) (by decide) rfl
  refine .next (t := .live ⟨resourceAt 8 6,[mixedGoal],[],.pop⟩) (.move .supportDone) ?_
  refine .next (t := .live ⟨resourceAt 14 5,[],[mixedGoal],.pop⟩) (.move ?_) ?_
  · exact .target (r' := resourceAt 14 6) rfl rfl rfl
  exact .next (.move .done) (.refl _)

theorem mixed_candidate_reflected_by_full_converse : mixedGoal ∈ [mixedGoal] :=
  initial_success_contains_every_checked_target mixedReaders mixedQuery nativeLimits (resourceAt 0 12)
    [mixedGoal] mixed_physical_support_success mixedGoal mixed_physical_support_candidate_checked rfl

end YulangClosure.ReachedSlotCompletenessR59
