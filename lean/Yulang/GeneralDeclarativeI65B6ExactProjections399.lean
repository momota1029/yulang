import Yulang.GeneralDeclarativeI65B6OriginalOrdinaryEvent399

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (normalize Pattern variablesArgs)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open GeneralDeclarations (Equation)

inductive B4Projection399 where
  | center
  | bounds
  deriving DecidableEq

def observedB4Projection399 (slots : Nat → Option Capture) (n : Nat) :
    B4Projection399 → Option (Nat × Nat)
  | .center => (slots n).map fun c => (c.center,c.center)
  | .bounds => (slots n).map fun c => (c.lower,c.upper)

mutual
def B6ValuePlan398.readShape399 {s c p} :
    B6ValuePlan398 s c p → List (Nat × B4Projection399)
  | .binder n => [(n,.center)]
  | .record _ a b => a.readShape399 ++ b.readShape399
  | .variant _ a => a.readShape399
  | .join a b => a.readShape399 ++ b.readShape399
  | .declaredApp _ _ _ _ a => a.readShape399

def B6ArgPlan398.readShape399 {s c param p} :
    B6ArgPlan398 s c param p → List (Nat × B4Projection399)
  | .valuePoint n _ _ => [(n,.center)]
  | .valueInterval n _ _ => [(n,.bounds)]
  | .rowPoint n _ _ => [(n,.center)]
  | .rowInterval n _ _ => [(n,.bounds)]
  | .valueTree _ _ a => a.readShape399

def B6ArgPlans398.readShape399 {s c params ps} :
    B6ArgPlans398 s c params ps → List (Nat × B4Projection399)
  | .nil => []
  | .cons a b => a.readShape399 ++ b.readShape399
end

/-- Exact lexical variable occurrence list, including repetitions.
Changing the kind or inherited variance affects the projection, not
which binder occurrence is read. -/
theorem B6_read_names_are_original_syntax399 {s c p} (plan : B6ValuePlan398 s c p) :
    plan.readShape399.map Prod.fst = p.variables := by
  refine B6ValuePlan398.rec
    (motive_1 := fun _ p plan => plan.readShape399.map Prod.fst = p.variables)
    (motive_2 := fun _ _ p plan => plan.readShape399.map Prod.fst = p.variables)
    (motive_3 := fun _ _ ps plan => plan.readShape399.map Prod.fst = variablesArgs ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intros; rfl
  · intro _ _ _ _ _ _ first rest
    simp [B6ValuePlan398.readShape399,Pattern.variables,first,rest]
  · intro _ _ _ _ below
    exact below
  · intro _ _ _ _ _ first last
    simp [B6ValuePlan398.readShape399,Pattern.variables,first,last]
  · intro _ _ _ _ _ _ _ _ below
    exact below
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro _ _ _ _ _ _ below
    exact below
  · intros; rfl
  · intro _ _ _ _ _ _ _ first rest
    simp [B6ArgPlans398.readShape399,variablesArgs,first,rest]

def AgreeB4Observations399 (first last : Nat → Option Capture)
    (reads : List (Nat × B4Projection399)) : Prop :=
  ∀ r ∈ reads, observedB4Projection399 first r.1 r.2 = observedB4Projection399 last r.1 r.2

private theorem agree_left399 {first last a b} (same : AgreeB4Observations399 first last (a ++ b)) :
    AgreeB4Observations399 first last a := fun _ hit => same _ (List.mem_append.mpr (.inl hit))

private theorem agree_right399 {first last a b} (same : AgreeB4Observations399 first last (a ++ b)) :
    AgreeB4Observations399 first last b := fun _ hit => same _ (List.mem_append.mpr (.inr hit))

/-- The exact logical RHS needs only the projections actually read
by that same authored plan. Points need the center; intervals need
both exact endpoints. Two complete tables need not be equal. -/
theorem B6_replay_depends_only_on_exact_projections399
    {s c p} (plan : B6ValuePlan398 s c p) {first last : Nat → Option Capture}
    (same : AgreeB4Observations399 first last plan.readShape399) :
    instantiateB6Value398 first plan = instantiateB6Value398 last plan := by
  refine B6ValuePlan398.rec
    (motive_1 := fun _ _ plan => AgreeB4Observations399 first last plan.readShape399 →
      instantiateB6Value398 first plan = instantiateB6Value398 last plan)
    (motive_2 := fun _ _ _ plan => AgreeB4Observations399 first last plan.readShape399 →
      instantiateB6Arg398 first plan = instantiateB6Arg398 last plan)
    (motive_3 := fun _ _ _ plan => AgreeB4Observations399 first last plan.readShape399 →
      instantiateB6Args398 first plan = instantiateB6Args398 last plan)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan same
  · intro context name agrees
    have reads := agrees (name,.center) (by simp [B6ValuePlan398.readShape399])
    cases orig : first name <;> cases later : last name <;>
      simp [observedB4Projection399,orig,later] at reads
    all_goals simp [instantiateB6Value398,orig,later,reads]
  · intro _ _ _ _ _ _ left right agrees
    simp [instantiateB6Value398,left (agree_left399 agrees),right (agree_right399 agrees)]
  · intro _ _ _ _ below agrees
    simp [instantiateB6Value398,below agrees]
  · intro _ _ _ _ _ left right agrees
    simp [instantiateB6Value398,left (agree_left399 agrees),right (agree_right399 agrees)]
  · intro _ _ _ _ _ _ _ _ below agrees
    simp [instantiateB6Value398,below agrees]
  · intro context param name kind mode agrees
    have reads := agrees (name,.center) (by simp [B6ArgPlan398.readShape399])
    cases orig : first name <;> cases later : last name <;>
      simp [observedB4Projection399,orig,later] at reads
    all_goals simp [instantiateB6Arg398,orig,later,reads]
  · intro context param name kind mode agrees
    have reads := agrees (name,.bounds) (by simp [B6ArgPlan398.readShape399])
    cases orig : first name <;> cases later : last name <;>
      simp [observedB4Projection399,orig,later] at reads
    all_goals first
      | (simp [instantiateB6Arg398,orig,later]; done)
      | simp [instantiateB6Arg398,orig,later,reads.1,reads.2]
  · intro context param name kind mode agrees
    have reads := agrees (name,.center) (by simp [B6ArgPlan398.readShape399])
    cases orig : first name <;> cases later : last name <;>
      simp [observedB4Projection399,orig,later] at reads
    all_goals simp [instantiateB6Arg398,orig,later,reads]
  · intro context param name kind mode agrees
    have reads := agrees (name,.bounds) (by simp [B6ArgPlan398.readShape399])
    cases orig : first name <;> cases later : last name <;>
      simp [observedB4Projection399,orig,later] at reads
    all_goals first
      | (simp [instantiateB6Arg398,orig,later]; done)
      | simp [instantiateB6Arg398,orig,later,reads.1,reads.2]
  · intro _ _ _ _ _ _ below agrees
    simp [instantiateB6Arg398,below agrees]
  · intros; rfl
  · intro _ _ _ _ _ _ _ left right agrees
    simp [instantiateB6Args398,left (agree_left399 agrees),right (agree_right399 agrees)]

/-- Recover the same original declaration and raw ordinal from the
actual selected event and checked registry, then compare only the
projections the B6 source plan really reads. This establishes exact
code equality, not equivalence of declarations from model values,
and does not identify the two events' unobserved where spines. -/
theorem frame_event_same_rhs_from_original_reads399 {s q}
    (event : LiteralLocalEvent s q) (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (sameSelectedId : f.decl.id = event.declaration.id)
    (atlas : B6SymbolicAtlas398 s) (i : Fin q.demand.outputs.length)
    {body : Body}
    (supplied : Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name body)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern body))}
    (typed : atlas.read event.declarationOrdinal body = some plan)
    (compatible : B6UsesFit398 s (writtenBodySlot392 event body) plan.needs)
    (same : AgreeB4Observations399 (f.slots body) (writtenBodySlot392 event body) plan.readShape399) :
    ∃ (frameOut : LogicalRoleOutput398 f i) (eventOut : EventLogicalOutput399 event i),
      (∃ wf : (f.decl.associated.map Equation.name).Nodup,
        logicalOutputAt398 f atlas i wf = some frameOut) ∧
      (∃ wf : (event.declaration.associated.map Equation.name).Nodup,
        logicalOutputOfEvent399 event atlas i wf = some eventOut) ∧
      frameOut.equation = eventOut.equation ∧
      CompoundSourceRhs394 s (writtenBodySlot392 event body) false
        (normalize (bodyPattern body)) eventOut.equation.rhs := by
  have ordinal := exact_frame_ordinal_of_same_selected_id399 event f checked sameSelectedId
  have fRow := f.authored
  rw [ordinal,event.declaredAt] at fRow
  have rows : f.decl = event.declaration := (Option.some.inj fRow).symm
  have wfF := (checked.2 f.decl (List.mem_of_getElem? f.authored)).identified.2.2.1
  have wfE := (checked.2 event.declaration (List.mem_of_getElem? event.declaredAt)).identified.2.2.1
  have framed : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body := rows ▸ supplied
  obtain ⟨rhs,replayed,meaning⟩ := symbolic_replay_meaning_with_supplied_capture_kinds398 plan compatible
  have typedFrame : atlas.read f.ordinal body = some plan := ordinal ▸ typed
  have replayFrame : instantiateB6Value398 (f.slots body) plan = some rhs :=
    (B6_replay_depends_only_on_exact_projections399 plan same).trans replayed
  let frameOut : LogicalRoleOutput398 f i := ⟨body,framed,rhs⟩
  let eventOut : EventLogicalOutput399 event i := ⟨body,supplied,rhs⟩
  refine ⟨frameOut,eventOut,⟨wfF,?_⟩,⟨wfE,?_⟩,rfl,meaning⟩
  · have hit : lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some body :=
      (lookup_exact _ _ wfF _ _).mpr framed
    unfold logicalOutputAt398
    dsimp only
    split
    next notFound => rw [hit] at notFound; contradiction
    next found read =>
      rw [hit] at read
      injection read with eqBody
      subst found
      simp [typedFrame,replayFrame,frameOut]
  · have hit : lookup (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name = some body :=
      (lookup_exact _ _ wfE _ _).mpr supplied
    unfold logicalOutputOfEvent399
    dsimp only
    split
    next notFound => rw [hit] at notFound; contradiction
    next found read =>
      rw [hit] at read
      injection read with eqBody
      subst found
      simp [typed,replayed,eventOut]

/-- Change only the selected center name; source lower/upper names
and their typing witnesses remain unchanged. -/
def recenterNative399 (capture : Nat → Capture) (center : Nat → Nat) (n : Nat) : Capture :=
  ⟨(capture n).lower,center n,(capture n).upper⟩

private theorem value_bind_ignores_center399 {s : State} {c : Capture} {lo hi} (bound : ValueBind s c lo hi)
    (candidate : Nat) : ValueBind s ⟨c.lower,candidate,c.upper⟩ lo hi :=
  ⟨bound.lowToSlot,bound.slotToLow,bound.highToSlot,bound.slotToHigh⟩

private theorem row_bind_ignores_center399 {s : State} {c : Capture} {lo hi} (bound : RowBind s c lo hi)
    (candidate : Nat) : RowBind s ⟨c.lower,candidate,c.upper⟩ lo hi :=
  ⟨bound.lowToSlot,bound.slotToLow,bound.highToSlot,bound.slotToHigh⟩

/-- Real native DeepRead observes the actual named bounds, inherited
kind/mode and binder occurrences, but by itself does not determine
any actual center. This is an interface fact about the existing source
judgment, not a new admissible source case. -/
noncomputable def deep_read_recenter_only399 {s capture c p lo hi found}
    (source : DeepRead s capture c p lo hi found) (center : Nat → Nat) :
    DeepRead s (recenterNative399 capture center) c p lo hi found := by
  refine DeepRead.rec
    (motive_1 := fun c p lo hi found _ => DeepRead s (recenterNative399 capture center) c p lo hi found)
    (motive_2 := fun c params ps lo hi found _ =>
      DeepArguments s (recenterNative399 capture center) c params ps lo hi found)
    (motive_3 := fun c param p lo hi found _ =>
      DeepArgument s (recenterNative399 capture center) c param p lo hi found)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intro n lo hi c bound
    exact .bind (value_bind_ignores_center399 bound (center n))
  · intro _ _ _ _ _ _ _ use declared table _ next
    exact .nominal use declared table next
  · exact .nil
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ child rest
    exact .cons child rest
  · intro _ _ _ _ _ _ next
    exact .covariantValue next
  · intro _ _ _ _ _ _ next
    exact .contravariantValue next
  · intro _ _ _ _ _ _ _ _ first rest
    exact .invariantValue first rest
  · intro _ _ _ _ covered
    exact .unusedValue covered
  · intro n _ _ _ bound
    exact .covariantRow (row_bind_ignores_center399 bound (center n))
  · intro n _ _ _ bound
    exact .contravariantRow (row_bind_ignores_center399 bound (center n))
  · intro n _ _ _ a b
    exact .invariantRow (row_bind_ignores_center399 a (center n))
      (row_bind_ignores_center399 b (center n))
  · intro _ _ _ _ covered
    exact .unusedRow covered

theorem declared_head_does_not_force_center399
    {s capture arg p found} (read : ModeWindow s arg p)
    (native : DeepRead s capture false (normalize p) read.lower.endpoint read.upper.endpoint found)
    (center : Nat → Nat) :
    DeepHead s (recenterNative399 capture center) arg p :=
  .declared read (deep_read_recenter_only399 native center)

/-- Corollary of the exact projection evaluator: a point use of a
genuine native binder actually writes the chosen center syntax. The
native bound witness can stay exactly the same while this syntax
changes, so a source-selected center must be retained independently. -/
theorem exact_point_rhs_sees_recentered_name399
    {s : State} {capture : Nat → Capture} {c : Bool}
    (n : Nat) (center : Nat → Nat) (different : (capture n).center ≠ center n) :
    instantiateB6Value398 (fun i => some (capture i)) (B6ValuePlan398.binder (s := s) (context := c) n) ≠
    instantiateB6Value398 (fun i => some (recenterNative399 capture center i))
      (B6ValuePlan398.binder (s := s) (context := c) n) := by
  intro equal
  apply different
  simpa [instantiateB6Value398,recenterNative399] using equal

/-- A positive native read alone can be retained while an exact
point RHS changes. This lemma holds at the proof-carrier level and
does not claim either center is admitted by the full classifier. -/
theorem native_bound_reads_do_not_identify_point_rhs399 {s capture context p lo hi found}
    (read : DeepRead s capture context p lo hi found) (n : Nat) :
    ∃ other : Nat → Capture,
      Nonempty (DeepRead s other context p lo hi found) ∧
      (∀ i, (other i).lower = (capture i).lower ∧ (other i).upper = (capture i).upper) ∧
      instantiateB6Value398 (fun i => some (capture i))
          (B6ValuePlan398.binder (s := s) (context := context) n) ≠
        instantiateB6Value398 (fun i => some (other i))
          (B6ValuePlan398.binder (s := s) (context := context) n) := by
  let shift := fun i => (capture i).center + 1
  exact ⟨recenterNative399 capture shift,⟨deep_read_recenter_only399 read shift⟩,
    fun _ => ⟨rfl,rfl⟩,
    exact_point_rhs_sees_recentered_name399 n shift (Nat.ne_of_lt (Nat.lt_succ_self _))⟩

open GeneralDeclarationPatterns (normalizeArgs)
open GeneralDeclarativeOutputs320 (termPattern termPatterns)

mutual
private theorem normalized_default_term_positions399 (rhs : Roles.Term) (n : Nat)
    (there : n ∈ (normalize (termPattern rhs)).variables) : n < rhs.bound := by
  cases rhs with
  | var j =>
    have same : n = j := by simpa [termPattern,normalize,Pattern.variables] using there
    subst n
    exact Nat.lt_succ_self _
  | app name args =>
    exact normalized_default_args_positions399 args n
      (by simpa only [termPattern,normalize,Pattern.variables] using there)
termination_by sizeOf rhs

private theorem normalized_default_args_positions399 (rs : List Roles.Term) (n : Nat)
    (there : n ∈ variablesArgs (normalizeArgs (termPatterns rs))) :
    n < Roles.argsBound rs := by
  cases rs with
  | nil => simp [termPatterns,normalizeArgs,variablesArgs] at there
  | cons head tail =>
    simp only [termPatterns,normalizeArgs,variablesArgs] at there
    rcases List.mem_append.mp there with first|last
    · exact Nat.lt_of_lt_of_le (normalized_default_term_positions399 head n first) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (normalized_default_args_positions399 tail n last) (Nat.le_max_right _ _)
termination_by sizeOf rs
end

/-- Existing authored role signatures carry positional default scope.
This discharges the default-scope input of the ordinary event theorem
for the actual registry, without B6 computing or filling a missing slot. -/
theorem default_positions_from_authored_role_decl399 (s : State) :
    OriginalDefaultPositions399 s := by
  intro role name rhs source n occurs
  have exactRange := ((authoredRegistry s.current).roles role).defaultsScoped name rhs source
  exact Nat.lt_of_lt_of_le (normalized_default_term_positions399 rhs n occurs) exactRange

end Yulang.GeneralDeclarativeI65
