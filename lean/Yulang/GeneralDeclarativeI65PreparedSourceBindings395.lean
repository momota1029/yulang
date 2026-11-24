import Yulang.GeneralDeclarativeI65SelectedWhereBindings395

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeAggregate324 (aligned kept allNames span ready)
open GeneralDeclarativeFreshTerms324 (protectedNames first second)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeMerge320 (lower upper EqualTerm)
open GeneralDeclarativeOpaqueGroup328 (group group_exact)
open GeneralDeclarativeOpaqueShared328 (build)
open GeneralDeclarativeStableAssemble329 (tieState merged)
open GeneralDeclarativeWitnessCompiler350 (Context portNames initial)

/-- Even a singleton actual span gets newly named aggregate endpoints.
Its source center is unchanged; equality of centers is not equality of
the literal capture used at an invariant RHS position. -/
theorem actual_aggregate_replaces_endpoints395 (s : GeneralDeclarativeHead320.State)
    (keep : List Nat) (seed : Capture) (rest : List Capture) :
    (span s keep seed rest).center = seed.center ∧
      seed.lower < (span s keep seed rest).lower ∧
      seed.upper < (span s keep seed rest).upper := by
  have lo : seed.lower ∈ kept keep seed rest := by simp [kept,allNames]
  have hi : seed.upper ∈ kept keep seed rest := by simp [kept,allNames]
  have originalLo :
      seed.lower ∈ protectedNames (aligned s seed rest) (kept keep seed rest) (lower seed rest) (upper seed rest) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ lo))
  have originalHi :
      seed.upper ∈ protectedNames (aligned s seed rest) (kept keep seed rest) (lower seed rest) (upper seed rest) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hi))
  exact ⟨rfl,before_after originalLo,Nat.lt_trans (before_after originalHi) (Nat.lt_succ_self _)⟩

theorem build_keeps_merged_span_not_old395 {s : GeneralDeclarativeHead320.State}
    {keys : List Nat} {uses : List (Nat × Capture)} {key : Nat} {seed : Capture} {more : List Capture}
    (keep : List Nat) (fallback : Nat → Capture)
    (present : key ∈ keys) (hit : group key uses = seed :: more) :
    ∃ prior : GeneralDeclarativeHead320.State, (build keep uses fallback s keys).captures key =
      span prior keep seed more := by
  induction keys generalizing s with
  | nil => cases present
  | cons other rest ih =>
    by_cases same : key = other
    · subst other
      exact ⟨s,by simp [build,hit]⟩
    · have later := (List.mem_cons.mp present).resolve_left same
      cases grouped : group other uses with
      | nil => simpa [build,grouped] using (ih (s := s) later)
      | cons old more' =>
        simpa [build,grouped,same] using (ih (s := ready s keep old more') later)

/-- The actual preparation naming function addresses both fresh
aggregates, not the two endpoints of the first pre-merge read. -/
theorem actual_port_capture_replaces_endpoints395 {c : Context}
    {ports : List GeneralDeclarativeClauseBatch327.Port} {key : Nat} {cap : Capture}
    (head : (c.spans.find? (fun item => item.1 == key)).map Prod.snd = some cap)
    (ordinaryInput : key ∉ c.decl.outputNames) :
    ∃ prior : GeneralDeclarativeHead320.State, ∃ extra : List Capture,
      (portNames c ports).input key = span prior c.keep cap extra ∧
      ((portNames c ports).input key).center = cap.center ∧
      cap.lower < ((portNames c ports).input key).lower ∧
      cap.upper < ((portNames c ports).input key).upper := by
  obtain ⟨more,grouped⟩ := find_first_group head
  have included : cap ∈ group key c.spans := by rw [grouped]; exact List.mem_cons_self
  have listed := (group_exact key c.spans).mp included
  have keyWritten : key ∈ c.spans.map Prod.fst := List.mem_map.mpr ⟨(key,cap),listed,rfl⟩
  obtain ⟨prior,recover⟩ := build_keeps_merged_span_not_old395
    (s := tieState c.named c.spans c.fallback) c.keep c.fallback keyWritten grouped
  have actual : (portNames c ports).input key = span prior c.keep cap more := by
    simpa only [portNames,GeneralDeclarativeFrameReadback325.sourceNames,
      GeneralDeclarativeProducedNames325.table,ordinaryInput,ite_false,initial,merged] using recover
  exact ⟨prior,more,actual,by rw [actual]; exact actual_aggregate_replaces_endpoints395 prior c.keep cap more⟩

/-- A value-kind ticket for those actual new endpoints comes from the
two signed logical aggregate definitions in the same State, not
from the numerical identity of a previous source center. This rule
does not manufacture row atoms from value equations. -/
theorem actual_aggregate_value_evidence395 {s : State} {cap seed : Capture} {rest : List Capture}
    (lo : EqualTerm s.current.ordinary cap.lower (lower seed rest))
    (hi : EqualTerm s.current.ordinary cap.upper (upper seed rest)) :
    ValueBind s cap (lower seed rest) (upper seed rest) :=
  ⟨lo.2,lo.1,hi.2,hi.1⟩

open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeAggregate324 (aggregates)
open GeneralDeclarativeFreshTerms324 (actual_rows)

private theorem ready_extends395 (s : GeneralDeclarativeHead320.State)
    (keep : List Nat) (seed : Capture) (rest : List Capture) :
    Extends s (ready s keep seed rest) :=
  GeneralDeclarativeGrowth327.trans
    (GeneralDeclarativeGrowth327.ordinary _ _)
    (GeneralDeclarativeGrowth327.trans (GeneralDeclarativeGrowth327.ordinary _ _)
      (GeneralDeclarativeGrowth327.ordinary _ _))

private theorem build_extends395 {s : GeneralDeclarativeHead320.State}
    (keep : List Nat) (uses : List (Nat × Capture)) (fallback : Nat → Capture)
    (ks : List Nat) : Extends s (build keep uses fallback s ks).state := by
  induction ks generalizing s with
  | nil => exact GeneralDeclarativeClauseBatch327.reflexive _
  | cons key rest ih =>
    cases got : group key uses with
    | nil => simpa [build,got] using (ih (s := s))
    | cons seed rest =>
      simpa [build,got] using
        (GeneralDeclarativeGrowth327.trans (ready_extends395 s keep seed rest)
          (ih (s := ready s keep seed rest)))

private theorem equalTerm_extended395 {a b : GeneralDeclarativeHead320.State} {n t}
    (grows : Extends a b) (literal : EqualTerm a n t) : EqualTerm b n t :=
  ⟨grows.constraints literal.1,grows.constraints literal.2⟩

private theorem actual_ready_has_endpoint_rows395 (s : GeneralDeclarativeHead320.State)
    (keep : List Nat) (seed : Capture) (rest : List Capture) :
    EqualTerm (ready s keep seed rest) (span s keep seed rest).lower (lower seed rest) ∧
      EqualTerm (ready s keep seed rest) (span s keep seed rest).upper (upper seed rest) := by
  have eqs := actual_rows (aligned s seed rest) (kept keep seed rest) (lower seed rest) (upper seed rest)
  have grows : Extends (aggregates s keep seed rest) (ready s keep seed rest) :=
    GeneralDeclarativeGrowth327.ordinary _ _
  exact ⟨equalTerm_extended395 grows eqs.1,equalTerm_extended395 grows eqs.2⟩

theorem build_group_keeps_endpoint_rows395 {s : GeneralDeclarativeHead320.State}
    {ks : List Nat} {uses : List (Nat × Capture)} {key : Nat} {seed : Capture} {more : List Capture}
    (keep : List Nat) (fallback : Nat → Capture)
    (present : key ∈ ks) (hit : group key uses = seed :: more) :
    let result := build keep uses fallback s ks
    EqualTerm result.state (result.captures key).lower (lower seed more) ∧
      EqualTerm result.state (result.captures key).upper (upper seed more) := by
  induction ks generalizing s with
  | nil => cases present
  | cons other rest ih =>
    by_cases same : key = other
    · subst other
      have made := actual_ready_has_endpoint_rows395 s keep seed more
      have grows := build_extends395 (s := ready s keep seed more) keep uses fallback rest
      simpa [build,hit] using
        (And.intro (equalTerm_extended395 grows made.1) (equalTerm_extended395 grows made.2))
    · have later := (List.mem_cons.mp present).resolve_left same
      cases grouped : group other uses with
      | nil => simpa [build,grouped] using (ih (s := s) later)
      | cons old more =>
        simpa [build,grouped,same] using (ih (s := ready s keep old more) later)

/-- Actual source preparation supplies both signed literal value
endpoint definitions at the real selected port. It is independent
of the fixed output batch and of a model. The equations apply to the
prepared state; use in a fixed State still needs actual same-state data. -/
theorem prepared_port_has_value_endpoint_rows395 {c : Context} {prepared}
    {ports : List GeneralDeclarativeClauseBatch327.Port} {key : Nat} {cap : Capture}
    (head : (c.spans.find? (fun item => item.1 == key)).map Prod.snd = some cap)
    (ordinaryInput : key ∉ c.decl.outputNames)
    (ran : GeneralDeclarativeWitnessCompiler350.preparation c = some (prepared,ports)) :
    ∃ more : List Capture, group key c.spans = cap :: more ∧
      EqualTerm prepared ((portNames c ports).input key).lower (lower cap more) ∧
      EqualTerm prepared ((portNames c ports).input key).upper (upper cap more) := by
  obtain ⟨more,grouped⟩ := find_first_group head
  have included : cap ∈ group key c.spans := by rw [grouped]; exact List.mem_cons_self
  have listed := (group_exact key c.spans).mp included
  have keyWritten : key ∈ c.spans.map Prod.fst := List.mem_map.mpr ⟨(key,cap),listed,rfl⟩
  have found := build_group_keeps_endpoint_rows395
    (s := tieState c.named c.spans c.fallback) c.keep c.fallback keyWritten grouped
  have earlier : EqualTerm (initial c).state ((portNames c ports).input key).lower (lower cap more) ∧
      EqualTerm (initial c).state ((portNames c ports).input key).upper (upper cap more) := by
    simpa only [portNames,GeneralDeclarativeFrameReadback325.sourceNames,
      GeneralDeclarativeProducedNames325.table,ordinaryInput,ite_false,initial,merged] using found
  have grows := GeneralDeclarativeStableAssemble329.prepare_grows ran
  exact ⟨more,grouped,equalTerm_extended395 grows earlier.1,equalTerm_extended395 grows earlier.2⟩

open GeneralDeclarations (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessCompiler350 (preparation placed)
open GeneralDictionaryAssociatedProvenance (Body)

/-- Reuse the actual successful pre-output source preparation. Its
logical equations must already be available in the same ambient
declarative State. This is not an output batch or State mutation. -/
structure PreparedSourceFrame395 (s : State) (q : Request) where
  ctx : Context
  sameRegistry : ctx.registry = authoredRegistry s.current
  sameDemand : ctx.demand = q.demand
  original : Nat
  authored : (authoredRegistry s.current).declarations[original]? = some ctx.decl
  visibleIn : ctx.decl ∈ visible s q
  beforeOutput : GeneralDeclarativeHead320.State
  ports : List GeneralDeclarativeClauseBatch327.Port
  prepared : preparation ctx = some (beforeOutput,ports)
  inCurrent : Extends beforeOutput s.current.ordinary

def PreparedSourceFrame395.frame {s q} (prepared : PreparedSourceFrame395 s q) :
    AuthoredBodyFrame393 s q :=
  frameAtSource395 prepared.visibleIn prepared.original prepared.authored
    (placed prepared.ctx prepared.ports) (initial prepared.ctx).captures

theorem PreparedSourceFrame395.slot_eq {s q} (prepared : PreparedSourceFrame395 s q)
    (body : Equation) (name : Nat) (written : name ∈ prepared.ctx.decl.inputNames) :
    prepared.frame.slots (.explicit body) name = some ((portNames prepared.ctx prepared.ports).input name) := by
  change ((prepared.ctx.decl.inputNames ++ prepared.ctx.decl.outputNames).map
    (fun n => (n,(portNames prepared.ctx prepared.ports).input n))).lookup name =
    some ((portNames prepared.ctx prepared.ports).input name)
  have member := List.mem_append_left prepared.ctx.decl.outputNames written
  generalize prepared.ctx.decl.inputNames ++ prepared.ctx.decl.outputNames = listed at member ⊢
  induction listed with
  | nil => cases member
  | cons head rest ih =>
    by_cases identical : head = name
    · subst head
      simp
    · have notMatch : (name == head) = false := beq_eq_false_iff_ne.mpr (Ne.symm identical)
      simp only [List.map_cons,List.lookup,notMatch,ih ((List.mem_cons.mp member).resolve_left (Ne.symm identical))]

/-- The value arm of the ordinary preparation is not kind
authority. The old source window must really have read this lexical
binder as a value in the actual winning declaration occurrence. -/
structure PreparedSelection395 {s q} (p : PreparedSourceFrame395 s q) where
  tape : CandidateTape s q (visible s q)
  winner : TapedMatch s q tape p.ctx.decl
  origin : SelectedHeadOrigin395 (row := p.ctx.decl) tape
  sameOrdinal : origin.rawOrdinal = p.original
  capture : Nat → Capture
  observed : CommonRoleOutermostResolver.All₂ (DeepHead s capture)
    q.demand.arguments p.ctx.decl.head
  sameHead : origin.pick.head = .ordered capture observed

/-- Every value ticket in a body uses one fixed observed selection.
In particular this relation cannot pick a different tape per use. -/
def PreparedValueAuthority395 {s q} {p : PreparedSourceFrame395 s q}
    (chosen : PreparedSelection395 p) (n : Nat) (seed : Capture) : Prop :=
  ActualHeadBinding395 chosen.origin.pick.head chosen.capture n .value ∧ chosen.capture n = seed

structure PreparedValueTicket395 {s q} {p : PreparedSourceFrame395 s q}
    (chosen : PreparedSelection395 p) (body : Equation) (n : Nat) (seed : Capture) where
  originalKind : PreparedValueAuthority395 chosen n seed
  ticket : BindingTicket394 s (p.frame.slots (.explicit body)) n .value

/-- The original prepared body capture carries its actual new
logical names. The two independently generated aggregate equations
give typed endpoints only after independent source value-kind
authority, rather than from the numerical identity of a previous center. -/
theorem prepared_source_value_ticket395 {s q} (prepared : PreparedSourceFrame395 s q)
    (chosen : PreparedSelection395 prepared)
    (separate : prepared.ctx.decl.OutputOnly) (body : Equation) (n : Nat)
    (usedInHead : n ∈ prepared.ctx.decl.inputNames)
    {seed : Capture} (seen : (prepared.ctx.spans.find? (fun item => item.1 == n)).map Prod.snd = some seed)
    (authority : PreparedValueAuthority395 chosen n seed) :
    Nonempty (PreparedValueTicket395 chosen body n seed) := by
  have noOutput : n ∉ prepared.ctx.decl.outputNames :=
    fun bad => separate.1 n bad
      (GeneralPatternVariableProvenance.normalize_args_variables prepared.ctx.decl.head usedInHead)
  obtain ⟨_,_,lowering,raising⟩ := prepared_port_has_value_endpoint_rows395 seen noOutput prepared.prepared
  exact ⟨⟨authority,⟨_,prepared.slot_eq body n usedInHead,
    .value (actual_aggregate_value_evidence395
      (equalTerm_extended395 prepared.inCurrent lowering)
      (equalTerm_extended395 prepared.inCurrent raising))⟩⟩⟩

noncomputable def readPreparedSourceBinding395 {s q} (prepared : PreparedSourceFrame395 s q)
    (chosen : PreparedSelection395 prepared)
    (separate : prepared.ctx.decl.OutputOnly) (body : Equation) :
    SourceBindingReads394 s (prepared.frame.slots (.explicit body)) := by
  classical
  exact ⟨fun n => if named : n ∈ prepared.ctx.decl.inputNames then
    match h : (prepared.ctx.spans.find? (fun item => item.1 == n)).map Prod.snd with
    | none => none
    | some seed =>
      if good : PreparedValueAuthority395 chosen n seed then
        some (Classical.choice (prepared_source_value_ticket395 prepared chosen separate body n named h good)).ticket
      else none
    else none,fun _ => none⟩

theorem read_prepared_value_at_literal_port395 {s q} {prepared : PreparedSourceFrame395 s q}
    {chosen : PreparedSelection395 prepared}
    {separate : prepared.ctx.decl.OutputOnly} {body : Equation} {n : Nat}
    (named : n ∈ prepared.ctx.decl.inputNames) {seed : Capture}
    (atSpan : (prepared.ctx.spans.find? (fun item => item.1 == n)).map Prod.snd = some seed)
    (good : PreparedValueAuthority395 chosen n seed) :
    ∃ ticket, (readPreparedSourceBinding395 prepared chosen separate body).value n = some ticket ∧
      ticket.val = (portNames prepared.ctx prepared.ports).input n := by
  classical
  let ticket := (Classical.choice (prepared_source_value_ticket395 prepared chosen separate body n named atSpan good)).ticket
  refine ⟨ticket,?_,?_⟩
  · unfold readPreparedSourceBinding395
    dsimp only
    rw [dite_eq_left named]
    split
    next lost => cases atSpan.symm.trans lost
    next picked chosen =>
      cases Option.some.inj (atSpan.symm.trans chosen)
      rw [dite_eq_left good]
  · exact Option.some.inj (ticket.2.1.symm.trans (prepared.slot_eq body n named))

/-- Re-run the actual typed RHS evaluator using the prepared value
source reads before a fixed output batch exists. No fallback read
is synthesized for a default, unsupported row, or missing span. -/
noncomputable def derivePreparedValueOutput395 {s q} (prepared : PreparedSourceFrame395 s q)
    (chosen : PreparedSelection395 prepared)
    (declared : GeneralDeclarations.Checked (authoredRegistry s.current))
    (ord : Fin q.demand.outputs.length) : Option (OriginalCompoundOutput394 prepared.frame ord) :=
  let checked := declared.2 prepared.ctx.decl ((visible_exact ..).mp prepared.visibleIn).1
  deriveOriginalCompoundOutput394 prepared.frame ord checked.identified.2.2.1
    (fun body => match body with
      | .explicit eq => readPreparedSourceBinding395 prepared chosen checked.outputOnly eq
      | .default .. => ⟨fun _ => none,fun _ => none⟩)

open CommonRecursiveNominalIntervals (Bounds Endpoint)
open Core.PresenceGeneration (TyTerm)

theorem actual_preparation_changes_invariant_value_literal395 {c : Context}
    {ports : List GeneralDeclarativeClauseBatch327.Port} {key : Nat} {cap : Capture}
    (atSpan : (c.spans.find? (fun item => item.1 == key)).map Prod.snd = some cap)
    (isInput : key ∉ c.decl.outputNames) :
    let selected := (portNames c ports).input key
    SourceRhsArg394.valueSlot key (.point (.ordinary (.var selected.center))) =
      SourceRhsArg394.valueSlot key (.point (.ordinary (.var cap.center))) ∧
    SourceRhsArg394.valueSlot key (.interval (.ordinary (.var selected.lower)) (.ordinary (.var selected.upper))) ≠
      SourceRhsArg394.valueSlot key (.interval (.ordinary (.var cap.lower)) (.ordinary (.var cap.upper))) := by
  obtain ⟨_,_,_,center,lo,_⟩ := actual_port_capture_replaces_endpoints395 (ports := ports) atSpan isInput
  dsimp only
  constructor
  · rw [center]
  · intro equal
    have sameLower := (Bounds.interval.inj (SourceRhsArg394.valueSlot.inj equal).2).1
    have conflict := TyTerm.var.inj (Endpoint.ordinary.inj sameLower)
    omega

theorem prepared_where_children_are_original395 {s q} (p : PreparedSourceFrame395 s q) :
    p.frame.clauses.map LiteralWhereEntry.demand =
      GeneralDeclarativeEmissionForest322.children p.ctx.decl (portNames p.ctx p.ports)
        (placed p.ctx p.ports) := by
  unfold PreparedSourceFrame395.frame AuthoredBodyFrame393.clauses
    GeneralDeclarativeEmissionForest322.children
  rw [List.map_map]
  rfl

/-- For the actual pre-output context, the ordered where proof really
belongs to the generated child occurrence, not a stand-in demand.
The child's own selected body rule is still needed for its kinded output. -/
theorem prepared_where_binder_comes_from_real_child395 {s q}
    (p : PreparedSourceFrame395 s q) (produced : p.ctx.decl.Produced)
    (body : Equation) {binder : GeneralDeclarations.OutputBinder}
    (used : binder ∈ p.ctx.decl.outputBinders) {rules : SelectedSourceRule383}
    {ds : List CommonRoleOutermostResolver.Dictionary}
    (selected : SelectedSourceForest383 rules s
      (children q (GeneralDeclarativeEmissionForest322.children p.ctx.decl
        (portNames p.ctx p.ports) (placed p.ctx p.ports))) ds) :
    ∃ origin : OriginalWhereBinder395 p.frame binder body, ∃ d,
      ds[origin.clauseOrdinal]? = some d ∧
      Nonempty (SelectedSourceProof383 rules s origin.child d) := by
  obtain ⟨origin⟩ := original_where_produces_lexical_slot395 p.frame produced body used
  have which : SelectedSourceForest383 rules s (children q (p.frame.clauses.map LiteralWhereEntry.demand)) ds := by
    rw [prepared_where_children_are_original395]
    exact selected
  let child := selectWhereBinderProducer395 origin which
  exact ⟨origin,child.dictionary,child.dictionaryAt,child.proof⟩

end Yulang.GeneralDeclarativeI65
