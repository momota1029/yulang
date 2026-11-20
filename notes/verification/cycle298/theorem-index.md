# Cycle 298: exact theorem signatures

## lean/Yulang/GeneralRebaseAlignedScan298.lean

```lean
theorem Yulang.GeneralRebaseAlignedScan298.positive_exact (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    positive (annotate plans head reject joint) = GeneralRebaseHeadProbe267.positive head plans
```

```lean
theorem Yulang.GeneralRebaseAlignedScan298.unknown_exact (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    unknown (annotate plans head reject joint) =
      (GeneralRebaseHeadProbe267.unresolved head plans).map observation
```

```lean
theorem Yulang.GeneralRebaseAlignedScan298.filter_exact (s : State roles) (plans : List (Plan roles)) (target : Match roles)
    (head : Plan roles → Option Bool) (reject joint : Plan roles → Bool) :
    ((annotate plans head reject joint).filter (eligibleRow s target)).map (·.plan) =
      plans.filter (eligible s head reject joint target)
```

```lean
theorem Yulang.GeneralRebaseAlignedScan298.scan_exact (s : State roles) (plans : List (Plan roles)) (head : Plan roles → Option Bool)
    (reject joint : Plan roles → Bool) :
    scan s (annotate plans head reject joint) = GeneralRebaseInstallCandidates267.scan s head reject joint plans
```

```lean
theorem Yulang.GeneralRebaseAlignedScan298.entry_order (s : State roles) (plans : List (Plan roles)) (check : Body → Option Bool) :
    (symbolic s plans check).map (·.plan) = plans
```


## lean/Yulang/GeneralRebaseDepthWindowExact298.lean

```lean
theorem Yulang.GeneralRebaseDepthWindowExact298.exact_window (target : View [owner] [output]) :
    target ∈ evaluated ↔ ∃ u : State roles, Weak registry root [owner] [output] initial u ∧
      project [owner] [output] u = target
```


## lean/Yulang/GeneralRebaseExecutableJournal298.lean

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.cls_exact (s : GeneralNominalCenteredSteps.State roles) (f : Occurrence roles)
    (p : Plan roles) (mapping : Nat → CompTerm Nat) :
    cls s f p mapping = GeneralNominalRebaseClassView243.compile s f p mapping
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.effect_exact (s : State roles) (e : GeneralNominalVersionedJournal232.Effect roles)
    (mapping : Nat → CompTerm Nat) :
    effect s e mapping = GeneralNominalRebaseJournalView243.effect s e mapping
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.compile_exact (s : State roles) (mapping : Nat → CompTerm Nat) :
    compile s mapping = GeneralNominalRebaseJournalView243.compile s mapping
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.source_models {s : State roles} {r : GeneralDeclarations.Registry} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (GeneralRebaseSourceSurvivor267.Boundary roles) r root s)
    (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (compile s mapping).Models m ↔ Models s (read mapping m)
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.candidate_exact (s : State roles) (p : Plan roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (candidate s p mapping).1.Holds m ∧ (candidate s p mapping).2.Holds m ↔
      GeneralRebaseSignedModels297.Conditions s p (read mapping m)
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.journalReads_exact (s : State roles) :
    journalReads s = GeneralRebaseSliceJournal283.journalReads s
```

```lean
theorem Yulang.GeneralRebaseExecutableJournal298.candidateReads_exact (s : State roles) (p : Plan roles) :
    candidateReads s p = GeneralRebaseSignedSupport297.candidateReads s p
```


## lean/Yulang/GeneralRebaseExplicitWindow298.lean

```lean
theorem Yulang.GeneralRebaseExplicitWindow298.agrees {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start : State roles) (window : List (State roles)) :
    scan owners pool start (materialized codes window) = GeneralRebaseWeakExit298.exits codes owners pool start window
```

```lean
theorem Yulang.GeneralRebaseExplicitWindow298.safe_scan {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    {s : State roles} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output) (window : List (Entry r root checked))
    (good : ∀ e ∈ window, Lull (Encoded r) root owners pool s e.state)
    (t : View owners pool) (found : t ∈ scan owners pool s window) :
    ∃ u, Weak (Encoded r) root owners pool s u ∧ project owners pool u = t
```

```lean
theorem Yulang.GeneralRebaseExplicitWindow298.Actual.only_one : evaluated.length = 1
```

```lean
theorem Yulang.GeneralRebaseExplicitWindow298.Actual.sole_target : evaluated.map (·.remaining) = [[]]
```

```lean
theorem Yulang.GeneralRebaseExplicitWindow298.Actual.concrete_real_target :
    ∃ u, Weak (Encoded sourceRegistry) root [owner] [output] initial u ∧
      (project [owner] [output] u).remaining = []
```


## lean/Yulang/GeneralRebaseFiniteSublists298.lean

```lean
theorem Yulang.GeneralRebaseFiniteSublists298.choices_exact (xs ys : List α) : ys ∈ choices xs ↔ ys.Sublist xs
```

```lean
theorem Yulang.GeneralRebaseFiniteSublists298.choices_count (xs : List α) : (choices xs).length = 2 ^ xs.length
```

```lean
theorem Yulang.GeneralRebaseFiniteSublists298.samples_sourced (holds : Q → A → Prop) (qs : List Q) (a : A)
    (listed : a ∈ GeneralRebaseFiniteWitnessTable297.samples holds qs) :
    ∃ q ∈ qs, holds q a
```


## lean/Yulang/GeneralRebaseLocalProgram298.lean

```lean
theorem Yulang.GeneralRebaseLocalProgram298.current_code {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (code : Local r s root checked) (owners : List Nat) (pool : List Output) :
    transition code owners pool (project owners pool s) = emit code
```

```lean
theorem Yulang.GeneralRebaseLocalProgram298.strict_exact {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output) (t) :
    GeneralRebaseStep258.Step (transition code owners pool) (project owners pool s) t ↔
    ∃ after, (Boundary roles).Step r root s after ∧ project owners pool after = t ∧ t ≠ project owners pool s
```

```lean
theorem Yulang.GeneralRebaseLocalProgram298.represents {r : Registry} {s t : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output)
    (step : (Boundary roles).Step r root s t) (different : project owners pool t ≠ project owners pool s) :
    ∃ p ∈ emit code, write (project owners pool s) p = project owners pool t
```

```lean
theorem Yulang.GeneralRebaseLocalProgram298.reifies {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output)
    (p : Proposal) (present : p ∈ emit code) :
    ∃ t, (Boundary roles).Step r root s t ∧ write (project owners pool s) p = project owners pool t
```


## lean/Yulang/GeneralRebasePackedAnswers298.lean

```lean
theorem Yulang.GeneralRebasePackedAnswers298.unique_mem (names : List Nat) (n : Nat) : n ∈ unique names ↔ n ∈ names
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.unique_nodup (names : List Nat) : (unique names).Nodup
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.key_injective (names : List Nat) : Function.Injective (unique names).get
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.type_at (f : Footprint) (x : Vector f) (fallback : Assignment) (i : Fin (unique f.types).length) :
    (fill f x fallback ((unique f.types).get i)).1 = x.types i
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.row_at (f : Footprint) (x : Vector f) (fallback : Assignment) (i : Fin (unique f.rows).length) :
    (fill f x fallback ((unique f.rows).get i)).2 = x.rows i
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.unpack_pack (f : Footprint) (x : Vector f) (fallback : Assignment) : pack f (fill f x fallback) = x
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.retain (f : Footprint) (a fallback : Assignment) :
    agrees f (fill f (pack f a) fallback) a
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.fallback_irrelevant (f : Footprint) (x : Vector f) (a b : Assignment) :
    agrees f (fill f x a) (fill f x b)
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.check_same (j : Journal) (q : Body) (a fallback : Assignment) :
    q.Holds j (fill (question j q) (pack (question j q) a) fallback) ↔ q.Holds j a
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.same_vector (j : Journal) (q : Body) (a b : Assignment)
    (same : pack (question j q) a = pack (question j q) b) : q.Holds j a ↔ q.Holds j b
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.asked_iff (j : Journal) (q : Body) (fallback : Assignment) :
    (∃ a, q.Holds j a) ↔
    ∃ v : Vector (question j q), q.Holds j (fill (question j q) v fallback)
```

```lean
theorem Yulang.GeneralRebasePackedAnswers298.valid_prior_iff (j : Journal) (fallback : Assignment) :
    (∃ a, j.Models a) ↔ ∃ v : Vector (prior j), j.Models (fill (prior j) v fallback)
```


## lean/Yulang/GeneralRebasePackedDecision298.lean

```lean
theorem Yulang.GeneralRebasePackedDecision298.included_sound (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) :
    Reflect (∃ a ∈ rows, P a) (reduce probe rows)
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.sound (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a))
    (yes : reduce probe rows = some true) : ∃ a, P a
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.total (probe : α → Answer) (rows : List α)
    (decided : ∀ a ∈ rows, probe a ≠ none) : reduce probe rows ≠ none
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.exact_if_covered (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) (cover : Covered P rows) :
    Reflect (∃ a, P a) (reduce probe rows)
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.complete (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) (cover : Covered P rows)
    (decided : ∀ a ∈ rows, probe a ≠ none) :
    reduce probe rows = some true ↔ ∃ a, P a
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.covered_encoding (j : Journal) (q : Body) (pad : Assignment) (rows : List Assignment)
    (cover : Covered (q.Holds j) rows) :
    Covered (Judge j q pad) (encode j q rows)
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.answer (j : Journal) (q : Body) (pad : Assignment) (xs : List Assignment)
    (probe : Vector (question j q) → Answer)
    (covered : Covered (q.Holds j) xs)
    (reflect : ∀ v ∈ encode j q xs, Reflect (Judge j q pad v) (probe v)) :
    Reflect (∃ m, q.Holds j m) (reduce probe (encode j q xs))
```

```lean
theorem Yulang.GeneralRebasePackedDecision298.unknown_control : reduce (fun _ : Unit => none) [()] = none
```


## lean/Yulang/GeneralRebasePackedDepthDecision298.lean

```lean
theorem Yulang.GeneralRebasePackedDepthDecision298.output_read (sign : Sign) : 3 ∈ (shape sign).types
```

```lean
theorem Yulang.GeneralRebasePackedDepthDecision298.answer_bits (sign : Sign) : reduce (ask sign) (encode base (body sign) xs) = some true
```

```lean
theorem Yulang.GeneralRebasePackedDepthDecision298.all_packed_rows_reflect (sign : Sign) (v : Vector (shape sign))
    (row : v ∈ encode base (body sign) xs) : Reflect (Judge base (body sign) fallback v) (ask sign v)
```

```lean
theorem Yulang.GeneralRebasePackedDepthDecision298.packed_cover (sign : Sign) : Covered ((body sign).Holds base) xs
```

```lean
theorem Yulang.GeneralRebasePackedDepthDecision298.exact_answer (sign : Sign) :
    Reflect (∃ a, Test after candidate sign a) (reduce (ask sign) (encode base (body sign) xs))
```


## lean/Yulang/GeneralRebasePackedNodeCompose298.lean

```lean
theorem Yulang.GeneralRebasePackedNodeCompose298.no_second_raw_step (next : State roles) : ¬ (boundary roles).Step registry displayRoot after next
```

```lean
theorem Yulang.GeneralRebasePackedNodeCompose298.child_of_answer (v : Vector footprint) (fallback : Assignment)
    (valid : Models after (complete v fallback)) :
    (boundary roles).Evidence registry after (complete v fallback) displayChild (.node 3 [])
```

```lean
theorem Yulang.GeneralRebasePackedNodeCompose298.parent_of_answer (v : Vector footprint) (fallback : Assignment)
    (valid : Models after (complete v fallback)) :
    (boundary roles).Evidence registry after (complete v fallback) displayRoot (.node 1 [.node 3 []])
```

```lean
theorem Yulang.GeneralRebasePackedNodeCompose298.supplied_model_composes (fallback : Assignment) :
    let v
```


## lean/Yulang/GeneralRebasePackedNonleaf298.lean

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.joint_exact (m : Assignment) (p d : Payload) :
    joint m p d ↔ TypeCheck m ∧ p = .node 1 [.node 3 []] ∧ d = .node 3 []
```

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.stable (a b : Assignment) (p d : Payload) (same : agrees footprint a b) :
    joint a p d ↔ joint b p d
```

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.model_and_tree_packed (a fallback : Assignment) (p d : Payload) :
    joint (fill footprint (pack footprint a) fallback) p d ↔ joint a p d
```

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.witness_reified (fallback : Assignment) :
    ∃ data : Vector footprint,
      joint (fill footprint data fallback) (.node 1 [.node 3 []]) (.node 3 [])
```

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.actual_generated :
    (Boundary roles).Step registry displayRoot before after ∧
      GeneralNominalSaturationState.Generated after.core.erased.current displayRoot displayChild
```

```lean
theorem Yulang.GeneralRebasePackedNonleaf298.hidden_by_no_output_projection :
    GeneralRebaseWeakProgress268.Stutter compiled displayRoot [] [] before after
```


## lean/Yulang/GeneralRebasePackedRowFixture298.lean

```lean
theorem Yulang.GeneralRebasePackedRowFixture298.before_exact (a : Assignment) : old.Models a ↔ Models before a
```

```lean
theorem Yulang.GeneralRebasePackedRowFixture298.installed_exact (a : Assignment) : installed.Models a ↔ OutputCheck a
```

```lean
theorem Yulang.GeneralRebasePackedRowFixture298.requires_row_zero : 0 ∈ (prior old).rows
```

```lean
theorem Yulang.GeneralRebasePackedRowFixture298.retained_after (a fallback : Assignment) :
    OutputCheck (fill (prior installed) (pack (prior installed) a) fallback) ↔ OutputCheck a
```


## lean/Yulang/GeneralRebasePackedSource298.lean

```lean
theorem Yulang.GeneralRebasePackedSource298.source_question {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (q : Question roles) (fallback : Assignment) :
    (∃ m, Holds s q m) ↔ ∃ v, reduced s q fallback v
```

```lean
theorem Yulang.GeneralRebasePackedSource298.empty_source {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s) (fallback : Assignment) :
    (¬ ∃ m, Models s m) ↔ ¬ ∃ v : Vector (prior (journal s CompTerm.var)),
      (journal s CompTerm.var).Models (fill (prior (journal s CompTerm.var)) v fallback)
```

```lean
theorem Yulang.GeneralRebasePackedSource298.reduced_independent (s : State roles) (q : Question roles) (a b : Assignment) (v) :
    reduced s q a v ↔ reduced s q b v
```


## lean/Yulang/GeneralRebaseQuestionFootprint298.lean

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.agrees_append {f g : Footprint} {a b : Assignment} :
    agrees (append f g) a b ↔ agrees f a b ∧ agrees g a b
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.typed_cut (P : Assignment → Prop) (f : Footprint)
    (typeCase : ∀ a b : Assignment, (∀ n, (a n).2 = (b n).2) →
      (∀ n ∈ f.types, (a n).1 = (b n).1) → (P a ↔ P b))
    (rowCase : ∀ a b : Assignment, (∀ n, (a n).1 = (b n).1) →
      (∀ n ∈ f.rows, (a n).2 = (b n).2) → (P a ↔ P b))
    (a b : Assignment) (equal : agrees f a b) : P a ↔ P b
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.prior_exact (view : Journal) (a b : Assignment) (equal : agrees (prior view) a b) :
    view.Models a ↔ view.Models b
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.head_exact (h : Head) (a b : Assignment) (equal : agrees (head h) a b) : h.Holds a ↔ h.Holds b
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.candidate_exact (c : Candidate) (a b : Assignment) (equal : agrees (candidate c) a b) :
    (c.1.Holds a ∧ c.2.Holds a) ↔ (c.1.Holds b ∧ c.2.Holds b)
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.atoms_exact (as : List GeneralNominalRebaseRawView243.Atom) (a b : Assignment)
    (equal : agrees (atoms as) a b) :
    PresenceNormalForm.All model a as ↔ PresenceNormalForm.All model b as
```

```lean
theorem Yulang.GeneralRebaseQuestionFootprint298.question_exact (j : Journal) (q : Body) (a b : Assignment)
    (equal : agrees (question j q) a b) : q.Holds j a ↔ q.Holds j b
```


## lean/Yulang/GeneralRebaseRefreshCode298.lean

```lean
theorem Yulang.GeneralRebaseRefreshCode298.listed : entries = [candidate]
```

```lean
theorem Yulang.GeneralRebaseRefreshCode298.head_moves (m : Assignment) (prior : Models initial m) :
    headTest candidate m ↔ headTest plan m
```

```lean
theorem Yulang.GeneralRebaseRefreshCode298.head_witness (m : Assignment) (member : m ∈ xs) : headTest candidate m
```

```lean
theorem Yulang.GeneralRebaseRefreshCode298.observed : Observed after xs entries checks
```

```lean
theorem Yulang.GeneralRebaseRefreshCode298.coverage : Covers (Holds after) (questions sourceRegistry after root checked) xs
```


## lean/Yulang/GeneralRebaseRefreshInstall298.lean

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.scan_exact : installAt sourceRegistry after root root checked probes = [candidate]
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.actual_effect :
    ∃ e : Effect roles, e.plan = candidate ∧ Installable registry after e ∧ ¬ Committed after e.plan
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.models_same {e : Effect roles} (same : e.plan = candidate) (enabled : Installable registry after e)
    (a : GeneralNominalCommonBridge.Assignment) :
    Models (install after e) a ↔ Models installed a
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.real_step {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (fresh : ¬ Committed after e.plan) :
    (Boundary roles).Step sourceRegistry root after (install after e)
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.before_projection : project [owner] [output] initial = project [owner] [output] after
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.writes_all : (write (project [owner] [output] after) projectedProposal).remaining = []
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.project_same {e : Effect roles} (same : e.plan = candidate) (enabled : Installable registry after e) :
    project [owner] [output] (install after e) = project [owner] [output] installed
```

```lean
theorem Yulang.GeneralRebaseRefreshInstall298.exact_two_steps :
    ∃ e : Effect roles, e.plan = candidate ∧ (Boundary roles).Step sourceRegistry root initial after ∧
      (Boundary roles).Step sourceRegistry root after (install after e) ∧
      project [owner] [output] initial = project [owner] [output] after ∧
      project [owner] [output] (install after e) = project [owner] [output] installed ∧
      (∀ m, Models (install after e) m ↔ Models installed m)
```


## lean/Yulang/GeneralRebaseRefreshPayload298.lean

```lean
theorem Yulang.GeneralRebaseRefreshPayload298.has_leaf {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (a : Assignment) (valid : Models (install after e) a) :
    Evidence registry (install after e).core a root (.node 0 [])
```

```lean
theorem Yulang.GeneralRebaseRefreshPayload298.only_leaf (s : State roles) (a : Assignment) (p : Payload)
    (ev : Evidence registry s.core a root p) : p = .node 0 []
```

```lean
theorem Yulang.GeneralRebaseRefreshPayload298.same_models_and_payload {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (a : Assignment) (p : Payload) :
    Models (install after e) a ∧ Evidence registry (install after e).core a root p ↔
    Models installed a ∧ Evidence registry installed.core a root p
```

```lean
theorem Yulang.GeneralRebaseRefreshPayload298.actual_annotated (codes : Family sourceRegistry root checked) :
    ∃ e : Effect roles, ∃ p, e.plan = candidate ∧
      Trace codes [owner] [output] initial (install after e) [p] ∧
      (∀ m d, Models (install after e) m ∧ Evidence registry (install after e).core m root d ↔
        Models installed m ∧ Evidence registry installed.core m root d)
```


## lean/Yulang/GeneralRebaseRefreshSafety298.lean

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.real_metadata : Metadata registry target
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.candidate_ready : candidate ∈ GeneralRebaseCandidatePrepared267.readyPlans registry after root (declChecked checked)
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.prepared : Prepared registry target root declaration
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.raw_edge {a b : Fin target.state.base.slots}
    (edge : GeneralNominalMixedRecurrence.Edge target.state a b) : (form b.val).rank < (form a.val).rank
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.raw_acyclic (slot : Fin target.state.base.slots) : ¬ GeneralNominalCycleK2.RecursAt target.state slot
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.semantic_acyclic (o) : ¬ GeneralNominalVersionedCycles232.Cyclic after o
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady after root
```

```lean
theorem Yulang.GeneralRebaseRefreshSafety298.safe : Known sourceRegistry after root
```


## lean/Yulang/GeneralRebaseRequestMultiplicity298.lean

```lean
theorem Yulang.GeneralRebaseRequestMultiplicity298.repetitions : requests doubled root = [⟨0,3⟩,⟨0,3⟩]
```

```lean
theorem Yulang.GeneralRebaseRequestMultiplicity298.literal_size : compiled.equations.length = 2 ∧ compiled.equalities.length = 8
```

```lean
theorem Yulang.GeneralRebaseRequestMultiplicity298.unchanged_semantics (m : GeneralNominalCommonBridge.Assignment) :
    compiled.Holds m ↔ GeneralNominalVersionedEffects231.ClassEffects doubled root plan m
```


## lean/Yulang/GeneralRebaseRevisitedTrace298.lean

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.raw {codes : Family r root checked} {owners pool s t ps}
    (walk : Trace codes owners pool s t ps) :
    Steps ((Boundary roles).Step r root) s t
```

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.reachable_tail {s t : State roles} (start : B4TargetV8.Reachable (Boundary roles) r root s)
    (walk : Steps ((Boundary roles).Step r root) s t) :
    B4TargetV8.Reachable (Boundary roles) r root t
```

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.compile_path (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    {s t : State roles} (start : B4TargetV8.Reachable (Boundary roles) r root s)
    (walk : Steps ((Boundary roles).Step r root) s t) :
    ∃ ps, Trace codes owners pool s t ps
```

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.exact {s t : State roles} (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start : B4TargetV8.Reachable (Boundary roles) r root s) :
    (∃ ps, Trace codes owners pool s t ps) ↔ Steps ((Boundary roles).Step r root) s t
```

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.replay {codes : Family r root checked} {owners pool s t ps}
    (trace : Trace codes owners pool s t ps) :
    ps.foldl write (project owners pool s) = project owners pool t
```

```lean
theorem Yulang.GeneralRebaseRevisitedTrace298.strict_budget {codes : Family r root checked} {owners pool s t ps}
    (trace : Trace codes owners pool s t ps) :
    ps.length + (project owners pool t).remaining.length ≤ (project owners pool s).remaining.length
```


## lean/Yulang/GeneralRebaseRowBasis298.lean

```lean
theorem Yulang.GeneralRebaseRowBasis298.type_eval_equal (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (term : TyTerm Name)
    (rows : ∀ n ∈ rowReads term, (a n).2 = (b n).2) :
    term.eval m a = term.eval m b
```

```lean
theorem Yulang.GeneralRebaseRowBasis298.atom_iff (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (q : Atom Name)
    (rows : ∀ n ∈ atomRowReads q, (a n).2 = (b n).2) :
    q.Holds m a ↔ q.Holds m b
```

```lean
theorem Yulang.GeneralRebaseRowBasis298.all_iff (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (atoms : List (Atom Name))
    (rows : ∀ n ∈ listRowReads atoms, (a n).2 = (b n).2) :
    All m a atoms ↔ All m b atoms
```

```lean
theorem Yulang.GeneralRebaseRowBasis298.equation_iff (q : GeneralNominalRebaseEffectView243.Equation) (a b : Assignment)
    (types : ∀ n, (a n).1 = (b n).1)
    (rows : ∀ n ∈ equationRows q, (a n).2 = (b n).2) :
    q.Holds a ↔ q.Holds b
```


## lean/Yulang/GeneralRebaseRowClass298.lean

```lean
theorem Yulang.GeneralRebaseRowClass298.holds_iff (view : View) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support view, (first n).2 = (last n).2) : view.Holds first ↔ view.Holds last
```


## lean/Yulang/GeneralRebaseRowJournal298.lean

```lean
theorem Yulang.GeneralRebaseRowJournal298.effect_iff (effect : Effect) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ effectReads effect, (first n).2 = (last n).2) :
 effect.Holds first ↔ effect.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowJournal298.models_iff (journal : Journal) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support journal, (first n).2 = (last n).2) :
 journal.Models first ↔ journal.Models last
```


## lean/Yulang/GeneralRebaseRowLive298.lean

```lean
theorem Yulang.GeneralRebaseRowLive298.argument_iff (a : GeneralNominalRebaseLiveView243.Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ argumentReads a, (first n).2 = (last n).2) : a.Holds first ↔ a.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowLive298.site_iff (site : Site) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support site, (first n).2 = (last n).2) : site.Holds first ↔ site.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowLive298.output_equal (site : Site) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support site, (first n).2 = (last n).2)
 (output : Output) (member : output ∈ site.outputs) :
 output.target.eval model first = output.target.eval model last
```


## lean/Yulang/GeneralRebaseRowObserved298.lean

```lean
theorem Yulang.GeneralRebaseRowObserved298.argument_iff (argument : Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ argumentReads argument, (first n).2 = (last n).2) :
 argument.Holds first ↔ argument.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowObserved298.holds_iff (arguments : List Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support arguments, (first n).2 = (last n).2) :
 Holds arguments first ↔ Holds arguments last
```


## lean/Yulang/GeneralRebaseRowOrigin298.lean

```lean
theorem Yulang.GeneralRebaseRowOrigin298.observes_forward (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (seen : Observes first origin actual)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) : Observes last origin actual
```

```lean
theorem Yulang.GeneralRebaseRowOrigin298.observes_iff (origin : Origin) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) (actual : Ty) :
 Observes first origin actual ↔ Observes last origin actual
```

```lean
theorem Yulang.GeneralRebaseRowOrigin298.head_iff (origin : Origin) (test : GeneralNominalRecursiveInspection.Test) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) :
 Head first origin test ↔ Head last origin test
```

```lean
theorem Yulang.GeneralRebaseRowOrigin298.same_iff (a b : Origin) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support a ++ support b, (first n).2 = (last n).2) :
 Same first a b ↔ Same last a b
```


## lean/Yulang/GeneralRebaseRowPacket298.lean

```lean
theorem Yulang.GeneralRebaseRowPacket298.equations_iff (equations : List GeneralNominalRebaseEffectView243.Equation)
 (first last : Assignment) (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ equationReads equations, (first n).2 = (last n).2) :
 AllEquations equations first ↔ AllEquations equations last
```

```lean
theorem Yulang.GeneralRebaseRowPacket298.child_iff (child : Child) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ childReads child, (first n).2 = (last n).2) :
 child.Holds first ↔ child.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowPacket298.packet_iff (packet : Packet) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support packet, (first n).2 = (last n).2) :
 packet.Holds first ↔ packet.Holds last
```


## lean/Yulang/GeneralRebaseRowProjection298.lean

```lean
theorem Yulang.GeneralRebaseRowProjection298.bounds_iff (b : Bounds) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ boundsReads b, (first n).2 = (last n).2) (actual : Ty) :
 b.Fits first actual ↔ b.Fits last actual
```

```lean
theorem Yulang.GeneralRebaseRowProjection298.models_iff (report : Report) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support report, (first n).2 = (last n).2) :
 report.Models first ↔ report.Models last
```


## lean/Yulang/GeneralRebaseRowSchema298.lean

```lean
theorem Yulang.GeneralRebaseRowSchema298.requirement_iff (r : Requirement) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ requirementReads r, (first n).2 = (last n).2) (actual : Ty) :
 r.Holds first actual ↔ r.Holds last actual
```

```lean
theorem Yulang.GeneralRebaseRowSchema298.use_iff (u : Use) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ useReads u, (first n).2 = (last n).2) : u.Holds first ↔ u.Holds last
```

```lean
theorem Yulang.GeneralRebaseRowSchema298.schema_iff (schema : Schema) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support schema, (first n).2 = (last n).2) : schema.Holds first ↔ schema.Holds last
```


## lean/Yulang/GeneralRebaseRowView298.lean

```lean
theorem Yulang.GeneralRebaseRowView298.slot_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ perSlot view index) : name ∈ support view
```

```lean
theorem Yulang.GeneralRebaseRowView298.type_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ rowReads (view.slot index).ty) : name ∈ support view
```

```lean
theorem Yulang.GeneralRebaseRowView298.head_member (view : View) (index : Fin view.slots) (term : TyTerm Nat)
 (found : view.heads index = some term) (name : Nat) (member : name ∈ rowReads term) :
 name ∈ support view
```

```lean
theorem Yulang.GeneralRebaseRowView298.descriptor_member (view : View) (index : Fin view.slots) (d : Descriptor)
 (found : view.nominals index = some d) (name : Nat) (member : name ∈ descriptorReads d) :
 name ∈ support view
```

```lean
theorem Yulang.GeneralRebaseRowView298.parameter_iff (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1) (p : Parameter)
 (rows : ∀ name ∈ parameterReads p, (first name).2 = (last name).2) (value : Argument) :
 p.Fits first value ↔ p.Fits last value
```

```lean
theorem Yulang.GeneralRebaseRowView298.fitsAll_forward (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1)
 (parameters : List Parameter) (values : List Argument)
 (rows : ∀ name ∈ parameters.flatMap parameterReads, (first name).2 = (last name).2)
 (valid : FitsAll first parameters values) : FitsAll last parameters values
```

```lean
theorem Yulang.GeneralRebaseRowView298.fitsAll_iff (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1) (parameters : List Parameter) (values : List Argument)
 (rows : ∀ name ∈ parameters.flatMap parameterReads, (first name).2 = (last name).2) :
 FitsAll first parameters values ↔ FitsAll last parameters values
```

```lean
theorem Yulang.GeneralRebaseRowView298.descriptor_iff (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1) (d : Descriptor) (target : TyTerm Nat)
 (rows : ∀ name ∈ descriptorReads d, (first name).2 = (last name).2)
 (targetTypes : ∀ name ∈ rowReads target, (first name).2 = (last name).2) :
 d.Denotes first target ↔ d.Denotes last target
```

```lean
theorem Yulang.GeneralRebaseRowView298.models_iff (view : View) (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1)
 (rows : ∀ name ∈ support view, (first name).2 = (last name).2) :
 view.Models first ↔ view.Models last
```


## lean/Yulang/GeneralRebaseSilentFactor298.lean

```lean
theorem Yulang.GeneralRebaseSilentFactor298.path_extend {R : A → A → Prop} {start middle after : A}
    (path : Steps R start middle) (edge : R middle after) : Steps R start after
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.restrict_acc {R S : A → A → Prop} (restrict : ∀ {a b}, R a b → S a b)
    {s : A} (acc : Acc S s) : Acc R s
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.accessible_factor (R : A → A → Prop) (rank : A → Nat)
    (mono : ∀ a b, R a b → rank b ≤ rank a) (s : A) :
    Acc (fun next current => R current next) s ↔
    ∀ a, Steps R s a → Acc (fun next current => Silent R rank current next) a
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.monotone (r : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
    (a b : State roles) (h : (Boundary roles).Step r root a b) : rank owners pool b ≤ rank owners pool a
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.silent_iff (r : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
    (a b : State roles) :
    Silent ((Boundary roles).Step r root) (rank owners pool) a b ↔ Stutter (Encoded r) root owners pool a b
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.necessary_and_sufficient (r : Registry) (root : Occurrence roles)
    (owners : List Nat) (pool : List Output) (s : State roles) :
    Acc (fun next current => (Boundary roles).Step r root current next) s ↔
    ∀ a, Steps ((Boundary roles).Step r root) s a →
      Acc (fun next current => Stutter (Encoded r) root owners pool current next) a
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.stutter_no_install {r : Registry} {root : Occurrence roles} {a b : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root a) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool)
    (quiet : Stutter (Encoded r) root owners pool a b) :
    GeneralNominalVersionedMixedProgressSplit236.QuietStep r root a b
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.counted_quiet {r : Registry} {root : Occurrence roles} {s t : State roles} {n : Nat}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool)
    (path : GeneralRebaseQuietBound277.Counted (Stutter (Encoded r) root owners pool) s n t) :
    n ≤ GeneralRebaseQuietBasis277.budget s
```

```lean
theorem Yulang.GeneralRebaseSilentFactor298.Source.accessible_if_visible_install {r : Registry} {root : Occurrence roles} {s : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool) :
    Acc (fun next current => (Boundary roles).Step r root current next) s
```


## lean/Yulang/GeneralRebaseSymbolicQuestions298.lean

```lean
theorem Yulang.GeneralRebaseSymbolicQuestions298.head_exact (p : Plan roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (head p mapping).Holds m ↔ headTest p (read mapping m)
```

```lean
theorem Yulang.GeneralRebaseSymbolicQuestions298.merge_exact (pair : Pair roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (mergeAtoms pair mapping) ↔
      atModel pair (read mapping m)
```

```lean
theorem Yulang.GeneralRebaseSymbolicQuestions298.compile_holds {r : Registry} {s : State roles} {root : Occurrence roles}
    (path : B4TargetV8.Reachable (Boundary roles) r root s) (mapping : Nat → CompTerm Nat)
    (q : Question roles) (m : Assignment) :
    (compile s mapping q).Holds (GeneralRebaseExecutableJournal298.compile s mapping) m ↔
      Holds s q (read mapping m)
```

```lean
theorem Yulang.GeneralRebaseSymbolicQuestions298.length_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (mapping : Nat → CompTerm Nat) :
    (program r s root checked mapping).jobs.length =
      3 * (GeneralRebaseSourceQuestions297.entries r s root checked).length + s.core.sites.length * s.core.sites.length
```

```lean
theorem Yulang.GeneralRebaseSymbolicQuestions298.at_index {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s) (checked : (Boundary roles).Checked r)
    (mapping : Nat → CompTerm Nat) (i : Nat) (q : Question roles)
    (recorded : (GeneralRebaseSourceWitnessProgram297.questions r s root checked)[i]? = some q)
    (m : Assignment) :
    ∃ body, (program r s root checked mapping).jobs[i]? = some body ∧
      (body.Holds (program r s root checked mapping).prior m ↔ Holds s q (read mapping m))
```


## lean/Yulang/GeneralRebaseWeakExit298.lean

```lean
theorem Yulang.GeneralRebaseWeakExit298.listed (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool) :
    target ∈ fromState codes owners pool s m ↔
    ∃ p ∈ emit (codes m), target = write (project owners pool s) p ∧
      target.remaining ≠ (project owners pool s).remaining
```

```lean
theorem Yulang.GeneralRebaseWeakExit298.target_sublist (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool) (member : target ∈ fromState codes owners pool s m) :
    target.remaining.Sublist (project owners pool s).remaining
```

```lean
theorem Yulang.GeneralRebaseWeakExit298.realizes {codes : Family r root checked} {s m : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (silent : Lull (Encoded r) root owners pool s m)
    (target : View owners pool) (member : target ∈ fromState codes owners pool s m) :
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target
```

```lean
theorem Yulang.GeneralRebaseWeakExit298.completeness {codes : Family r root checked} {s after : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (weak : Weak (Encoded r) root owners pool s after) :
    ∃ m, Lull (Encoded r) root owners pool s m ∧
      project owners pool after ∈ fromState codes owners pool s m
```

```lean
theorem Yulang.GeneralRebaseWeakExit298.sound_window {codes : Family r root checked} {s : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (window : List (State roles)) (good : ∀ m ∈ window, Lull (Encoded r) root owners pool s m)
    (target : View owners pool) (member : target ∈ exits codes owners pool s window) :
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target
```


## lean/Yulang/GeneralRebaseWeakWindow298.lean

```lean
theorem Yulang.GeneralRebaseWeakWindow298.window_size (codes : Family r root checked) (owners : List Nat) (pool : List Output) (s : State roles) :
    (window codes owners pool s).length ≤ 2 ^ (project owners pool s).remaining.length
```

```lean
theorem Yulang.GeneralRebaseWeakWindow298.genuine (codes : Family r root checked) (owners : List Nat) (pool : List Output) (s m : State roles)
    (listed : m ∈ window codes owners pool s) : Lull (Encoded r) root owners pool s m
```

```lean
theorem Yulang.GeneralRebaseWeakWindow298.enough (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool)
    (silent : Lull (Encoded r) root owners pool s m) (found : target ∈ fromState codes owners pool s m) :
    target ∈ exits codes owners pool s (window codes owners pool s)
```

```lean
theorem Yulang.GeneralRebaseWeakWindow298.exact (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) (target : View owners pool) :
    target ∈ exits codes owners pool s (window codes owners pool s) ↔
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target
```

```lean
theorem Yulang.GeneralRebaseWeakWindow298.target_codes_exact (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) (result : List Fact) :
    result ∈ targetCodes codes owners pool s (window codes owners pool s) ↔
    ∃ after, Weak (Encoded r) root owners pool s after ∧ (project owners pool after).remaining = result
```

```lean
theorem Yulang.GeneralRebaseWeakWindow298.no_weak_iff (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) :
    targetCodes codes owners pool s (window codes owners pool s) = [] ↔
    ∀ after, ¬ Weak (Encoded r) root owners pool s after
```


## lean/Yulang/GeneralRebaseWeakWindowLegacy298.lean

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.positive_initial :
    (project [owner] [] (state 0)).remaining = []
```

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.observed_install :
    (project [owner] [] (installed 0)).remaining = []
```

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.installed_reachable :
    B4TargetV8.Reachable (Boundary roles) sourceRegistry root (installed 0)
```

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.no_weak_after_first (after : GeneralNominalVersionedJournal232.State roles) :
    ¬ Weak registry root [owner] [] (installed 0) after
```

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.no_raw_accessibility :
    ¬ Acc (fun next prev => Step registry root prev next) (installed 0)
```

```lean
theorem Yulang.GeneralRebaseWeakWindowLegacy298.empty_but_divergent (checked : (Boundary roles).Checked sourceRegistry)
    (codes : Family sourceRegistry root checked) :
    targetCodes codes [owner] [] (installed 0) (window codes [owner] [] (installed 0)) = [] ∧
      ¬ Acc (fun next prev => Step registry root prev next) (installed 0)
```

Indexed 172 theorem declarations. Each has one standalone audit.
