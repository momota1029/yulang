# Cycle 297: exact theorem signatures

## lean/Yulang/GeneralRebaseDepthCompiler297.lean

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.votes_agree (sign : Sign) :
    hit (values pool) (signed (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a)) (plan,sign) =
      vote pool GeneralRebaseSignedDepth297.check plan sign
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.root_entries : atFocus (Encoded sourceRegistry) initial root root (declChecked checked) = [plan]
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.entries : GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked = [plan]
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.all_models_checked :
    GeneralRebaseSourceQuestions297.Checked initial [plan] (values pool) (fun _ => true)
      (fun _ a => GeneralRebaseSignedDepth297.nested a)
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.head_condition : GeneralRebaseCandidatePrepared267.headCondition plan
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.scan_root : installAt sourceRegistry initial root root checked compiled = [plan]
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.no_structural_novelty :
    installAt sourceRegistry initial root root checked
      ({compiled with novelty
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.no_joint :
    installAt sourceRegistry initial root root checked
      ({compiled with joint
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.proposals_exact :
    GeneralRebaseSourceObserver267.proposals sourceRegistry initial root checked compiled =
      [GeneralRebaseMultiSelection263.proposal initial.core (GeneralRebaseMultiSelection263.ofPlan plan)]
```

```lean
theorem Yulang.GeneralRebaseDepthCompiler297.same_real_successor :
    ∃ p ∈ GeneralRebaseSourceObserver267.proposals sourceRegistry initial root checked compiled,
      (Boundary roles).Step sourceRegistry root initial installed ∧
      GeneralRebaseStep258.write (project [owner] [output] initial) p = project [owner] [output] installed
```


## lean/Yulang/GeneralRebaseFiniteWitnessTable297.lean

```lean
theorem Yulang.GeneralRebaseFiniteWitnessTable297.length_le (holds : Q → A → Prop) (questions : List Q) :
    (samples holds questions).length ≤ questions.length
```

```lean
theorem Yulang.GeneralRebaseFiniteWitnessTable297.covers (holds : Q → A → Prop) (questions : List Q) :
    Covers holds questions (samples holds questions)
```

```lean
theorem Yulang.GeneralRebaseFiniteWitnessTable297.hit_true (holds : Q → A → Prop) (xs : List A) (check : Q → A → Bool) (q : Q)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = true ↔ ∃ a ∈ xs, holds q a
```

```lean
theorem Yulang.GeneralRebaseFiniteWitnessTable297.hit_exact (holds : Q → A → Prop) (questions : List Q) (xs : List A)
    (cover : Covers holds questions xs) (check : Q → A → Bool) (q : Q) (listed : q ∈ questions)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = true ↔ ∃ a, holds q a
```

```lean
theorem Yulang.GeneralRebaseFiniteWitnessTable297.hit_false (holds : Q → A → Prop) (questions : List Q) (xs : List A)
    (cover : Covers holds questions xs) (check : Q → A → Bool) (q : Q) (listed : q ∈ questions)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = false ↔ ¬ ∃ a, holds q a
```


## lean/Yulang/GeneralRebaseMergeQuestions297.lean

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.shape_exact (p : Pair roles) : shape p = true ↔
    p.1.occurrence.demand.role = p.2.occurrence.demand.role ∧
    (centers p.1).length = (centers p.2).length
```

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.roles_force_length (p : Pair roles)
    (r : p.1.occurrence.demand.role = p.2.occurrence.demand.role) :
    (centers p.1).length = (centers p.2).length
```

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.all₂_zip (relation : Nat → Nat → Prop) (as bs : List Nat) :
    All₂ (fun a b => ∃ i j, a = some (GeneralNominalRecursiveInspection.Origin.source i) ∧
       b = some (GeneralNominalRecursiveInspection.Origin.source j) ∧ relation i j)
      (givenNames as) (givenNames bs) ↔
    as.length = bs.length ∧ ∀ c ∈ as.zip bs, relation c.1 c.2
```

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.semantic_exact (s : State roles) (p : Pair roles) :
    SameInputs (Models s) p.1 p.2 ↔ shape p = true ∧ ∀ m, Models s m → atModel p m
```

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.counter_exact (s : State roles) (p : Pair roles) :
    SameInputs (Models s) p.1 p.2 ↔ shape p = true ∧ ¬ ∃ m, counter s p m
```

```lean
theorem Yulang.GeneralRebaseMergeQuestions297.equal_exact (s : State roles) (pairs : List (Pair roles)) (samples : List Assignment)
    (cover : Covers (counter s) pairs samples) (test : Pair roles → Assignment → Bool)
    (p : Pair roles) (listed : p ∈ pairs)
    (cert : ∀ m ∈ samples, test p m = true ↔ counter s p m) :
    equal samples test p = true ↔ SameInputs (Models s) p.1 p.2
```


## lean/Yulang/GeneralRebaseMergeWitnessFixture297.lean

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.EqualCenter.no_counter : ¬ ∃ m, counter journal pair m
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.EqualCenter.coverage : Covers (counter journal) [pair] []
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.EqualCenter.computed : equal [] test pair = true
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.EqualCenter.determined :
    equal [] test pair = true ↔ SameInputs (Models journal) first last
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.EqualCenter.same_not_literal : equal [] test pair = true ∧ GeneralRebaseMergeCenters267.same first last = false
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.not_equal : ¬ atModel pair model
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.loss : counter initial pair model
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.coverage : Covers (counter initial) [pair] [model]
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.computed : equal [model] test pair = false
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.determined :
    equal [model] test pair = true ↔ SameInputs (Models initial) pair.1 pair.2
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.DifferentCenter.missing_counter_unsound :
    equal [] test pair = true ∧ ¬ SameInputs (Models initial) pair.1 pair.2
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.ActualStep.listed : (aSite,bSite) ∈ GeneralRebaseMergeScan267.scan sample root
    (fun a b => equal [] tested (a,b))
```

```lean
theorem Yulang.GeneralRebaseMergeWitnessFixture297.ActualStep.actual_preserved :
    GeneralNominalVersionedMixedKernel234.Step registry root sample merged ∧
      GeneralRebaseLiveProjection264.project owners pool merged ≠ GeneralRebaseLiveProjection264.project owners pool sample
```


## lean/Yulang/GeneralRebasePreInstallReplay297.lean

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.kept (id : Nat) : Known snapshot id → Known target.state id
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.sound_cache : CacheSound initial target.state
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.zero_old : ¬ Known snapshot 0
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.zero_new : Known target.state 0
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.zero_source : 0 ∈ sources snapshot
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.actual_before_install : Step registry root initial after
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.different : after ≠ initial
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.seen : GeneralRebaseRetarget275.Observed plan
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.all_tests (sign : Sign) (m : Assignment) :
    Test after candidate sign m ↔ Test initial plan sign m
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.signs_preserved :
    Test after candidate .pass model ∧ Test after candidate .reject smallModel
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.source_reachable :
    B4TargetV8.Reachable (GeneralRebaseSourceSurvivor267.Boundary roles) sourceRegistry root after
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.raw_observation_not_determined_by_tests :
    (∀ sign m, Test after candidate sign m ↔ Test initial plan sign m) ∧
      ¬ Known initial.core.erased.current.context.state 0 ∧ Known after.core.erased.current.context.state 0
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.listed_after (p : GeneralNominalCenters.Plan roles) :
    p ∈ GeneralRebaseSourceQuestions297.entries sourceRegistry after root GeneralRebaseSignedDepth297.checked ↔
      p = candidate
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.retained_table :
    GeneralRebaseSourceQuestions297.Checked after entries xs (fun _ => true)
      (fun _ a => GeneralRebaseSignedDepth297.nested a)
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.retained_coverage :
    GeneralRebaseFiniteWitnessTable297.Covers (GeneralRebaseSourceQuestions297.holds after)
      (GeneralRebaseSourceQuestions297.questions entries) xs
```

```lean
theorem Yulang.GeneralRebasePreInstallReplay297.retained_answers (sg : Sign) :
    GeneralRebaseFiniteWitnessTable297.hit xs
      (GeneralRebaseSourceQuestions297.signed (fun _ => true) (fun _ a => GeneralRebaseSignedDepth297.nested a))
      (candidate,sg) = true
```


## lean/Yulang/GeneralRebasePriorWitness297.lean

```lean
theorem Yulang.GeneralRebasePriorWitness297.covers {s : State roles} {plans : List (Plan roles)} {pool : List (Prior s)}
    (rep : Represents s plans pool) : Covers (holds s) (questions plans) (values pool)
```

```lean
theorem Yulang.GeneralRebasePriorWitness297.prior_exact {s : State roles} (pool : List (Prior s)) (a : Assignment)
    (used : a ∈ values pool) : Models s a
```

```lean
theorem Yulang.GeneralRebasePriorWitness297.vote_exact {s : State roles} {plans : List (Plan roles)} {pool : List (Prior s)}
    (cover : Covers (holds s) (questions plans) (values pool))
    (check : Plan roles → Prior s → Bool) (p : Plan roles) (listed : p ∈ plans)
    (cert : ∀ a ∈ pool, check p a = true ↔ Conditions s p a.val) (sign : Sign) :
    vote pool check p sign = true ↔ ∃ m, Test s p sign m
```


## lean/Yulang/GeneralRebaseRawDepthReplay297.lean

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.safe_exact : ExactSafety sourceRegistry initial root safety
```

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.small_head : headTest plan smallModel
```

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.observed :
    Observed initial (values pool) (GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked) checks
```

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.program_covers : GeneralRebaseFiniteWitnessTable297.Covers
    (GeneralRebaseSourceWitnessProgram297.Holds initial)
      (questions sourceRegistry initial root checked) (values pool)
```

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.metadata : GeneralNominalRecursiveCandidates.Metadata registry initial.core.erased.current.context
```

```lean
theorem Yulang.GeneralRebaseRawDepthReplay297.exact_raw_projection (target : GeneralRebaseStep258.State
    (GeneralRebaseCompression266.Basis [owner] [output])) :
    GeneralRebaseStep258.Step (observe sourceRegistry initial root checked (values pool) checks safety [owner] [output])
      (GeneralRebaseLiveProjection264.project [owner] [output] initial) target ↔
    ∃ after, (Boundary roles).Step sourceRegistry root initial after ∧
      GeneralRebaseLiveProjection264.project [owner] [output] after = target ∧
      target ≠ GeneralRebaseLiveProjection264.project [owner] [output] initial
```


## lean/Yulang/GeneralRebaseRawInstallScan297.lean

```lean
theorem Yulang.GeneralRebaseRawInstallScan297.frame_positions {p : Plan roles}
    (safe : Known r s f) (frame : Frame (Encoded r) s.core f k p) :
    GeneralNominalVersionedCycles232.Safe s p
```

```lean
theorem Yulang.GeneralRebaseRawInstallScan297.install_from_current {e : Effect roles} (checked : (Boundary roles).Checked r)
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (reg : e.registry = Encoded r) (snap : e.snapshot = s.core)
    (safe : Known r s e.plan.packet.site.occurrence)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current e.plan.packet)
    (common : ∃ m, GeneralNominalVersionedMixedMaterialization237.Residual s e m) :
    Installable (Encoded r) s e
```

```lean
theorem Yulang.GeneralRebaseRawInstallScan297.reconstruct (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (generated : Generated s.core.erased.current root f)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (honest : Honest (probes.head f) (atFocus (Encoded r) s root f (declChecked checked)))
    (p : Plan roles) (listed : p ∈ installAt r s root f checked probes) :
    ∃ e : Effect roles, e.registry = Encoded r ∧ e.snapshot = s.core ∧ e.plan = p ∧
      e.plan.packet.site.occurrence = f
```

```lean
theorem Yulang.GeneralRebaseRawInstallScan297.selected_raw (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (generated : Generated s.core.erased.current root f)
    (metadata : Metadata (Encoded r) s.core.erased.current.context) (safe : Known r s f)
    (honest : Honest (probes.head f) (atFocus (Encoded r) s root f (declChecked checked)))
    (contracts : GeneralRebaseInstallCandidates267.Probes (Encoded r) s
      (probes.novelty f) (probes.joint f) (atFocus (Encoded r) s root f (declChecked checked)))
    (p : Plan roles) (listed : p ∈ installAt r s root f checked probes) :
    ∃ e : Effect roles, e.plan = p ∧ e.plan.packet.site.occurrence = f ∧
      Installable (Encoded r) s e ∧ ¬ Committed s e.plan
```


## lean/Yulang/GeneralRebaseRawObserver297.lean

```lean
theorem Yulang.GeneralRebaseRawObserver297.listed_install (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) (p : Plan roles) :
    p ∈ installs r s root checked probes safety ↔
      ∃ f, Generated s.core.erased.current root f ∧ safety f = true ∧ p ∈ installAt r s root f checked probes
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) (result : Proposal) :
    result ∈ proposals r s root checked probes safety ↔
      (∃ p ∈ installs r s root checked probes safety, proposal s.core (ofPlan p) = result) ∨
      ∃ pair ∈ GeneralRebaseMergeScan267.scan s root probes.mergeInputs,
        affectedProposal s pair.1 pair.2 = result
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.sound (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (p : Proposal) (present : p ∈ proposals r s root checked (callbacks xs c) safety) :
    ∃ after, (Boundary roles).Step r root s after ∧
      write (project owners pool s) p = project owners pool after ∧ p ⊆ liveFacts after
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.complete (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output) (after : State roles)
    (real : (Boundary roles).Step r root s after)
    (changed : project owners pool after ≠ project owners pool s) :
    ∃ p ∈ proposals r s root checked (callbacks xs c) safety,
      write (project owners pool s) p = project owners pool after
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.observe_at (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (xs : List Assignment) (c : Checks roles)
    (safety : Occurrence roles → Bool) (owners : List Nat) (pool : List Output) :
    observe r s root checked xs c safety owners pool (project owners pool s) =
      proposals r s root checked (callbacks xs c) safety
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.strict_exact (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (target : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (project owners pool s) target ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      project owners pool after = target ∧ target ≠ project owners pool s
```

```lean
theorem Yulang.GeneralRebaseRawObserver297.same_projection_only (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output) :
    (∀ next, ¬ GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (project owners pool s) next) ↔
    ∀ after, (Boundary roles).Step r root s after → project owners pool after = project owners pool s
```


## lean/Yulang/GeneralRebaseRawSafetyBits297.lean

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.reflect {r : Registry} {s : State roles} {f : Occurrence roles} {b : Bits}
    (cert : Certified r s f b) : Reflect (Known r s f) (run b)
```

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.all_false : run ⟨some false,some false,some false,some false⟩ = some true
```

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.unknown_not_negative : run ⟨some false,some false,none,some false⟩ = none
```

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.known_violation : run ⟨some false,some true,none,none⟩ = some false
```

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.allow_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (bits : Occurrence roles → Bits)
    (cert : ∀ f, GeneralNominalSaturationState.Generated s.core.erased.current root f → Certified r s f (bits f))
    (resolved : ∀ f, GeneralNominalSaturationState.Generated s.core.erased.current root f → run (bits f) ≠ none) :
    ExactSafety r s root (allow bits)
```

```lean
theorem Yulang.GeneralRebaseRawSafetyBits297.allow_positive (r : Registry) (s : State roles) (f : Occurrence roles)
    (bits : Occurrence roles → Bits) (cert : Certified r s f (bits f)) :
    allow bits f = true → Known r s f
```


## lean/Yulang/GeneralRebaseSignedDepth297.lean

```lean
theorem Yulang.GeneralRebaseSignedDepth297.checked : (Boundary roles).Checked sourceRegistry
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.listed : plan ∈ entries sourceRegistry initial root checked
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.positive : Test initial plan .pass model
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.negative : Test initial plan .reject smallModel
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.same_public_types :
    GeneralRebaseDepthPublic285.project model = GeneralRebaseDepthPublic285.project smallModel
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.all_rows_same : ∀ n, (model n).2 = (smallModel n).2
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.output_only_rejection : Test initial plan .reject (GeneralRebaseDepthMinimal285.damage 3)
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.output_must_be_observed :
    3 ∈ candidateReads initial plan
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.bit_checked (a : Prior initial) (row : a ∈ pool) :
    check plan a = true ↔ Conditions initial plan a.val
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.pool_covers : Covers (GeneralRebaseSourceQuestions297.holds initial)
    (questions [plan]) (values pool)
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.exact_both (sign : Sign) :
    vote pool check plan sign = true ↔ ∃ m, Test initial plan sign m
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.computes_both : vote pool check plan .pass = true ∧
    vote pool check plan .reject = true
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.reject_only_is_incomplete (cert : Covers (GeneralRebaseSourceQuestions297.holds initial)
    (questions [plan]) (values [rejectRow])) : False
```

```lean
theorem Yulang.GeneralRebaseSignedDepth297.public_only_impossible (evaluate : GeneralRebaseDepthPublic285.SourceTypes → (Nat → Common.Row) → Bool)
    (recovers : ∀ m, Models initial m →
      (evaluate (GeneralRebaseDepthPublic285.project m) (fun n => (m n).2) = true ↔ Conditions initial plan m)) : False
```


## lean/Yulang/GeneralRebaseSignedHistory297.lean

```lean
theorem Yulang.GeneralRebaseSignedHistory297.at_least {A : Type} (rejects : Nat → A → Prop)
    (disjoint : ∀ i j, i < j → ∀ a, rejects i a → ¬ rejects j a)
    (xs : List A) (n : Nat)
    (covers : ∀ i < n, ∃ a ∈ xs, rejects i a) : n ≤ xs.length
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.no_fixed_table {A : Type} (rejects : Nat → A → Prop)
    (disjoint : ∀ i j, i < j → ∀ a, rejects i a → ¬ rejects j a)
    (xs : List A) : ¬ ∀ i, ∃ a ∈ xs, rejects i a
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Version.exact_loss (n : Nat) (m : Assignment) :
    dropped n m ↔ Models (state n) m ∧ ¬ Models (installed n) m
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Version.bad_witness (n : Nat) : dropped n (bad n)
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Version.disjoint (a b : Nat) (earlier : a < b) (m : Assignment)
    (lost : dropped a m) (later : dropped b m) : False
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Version.no_universal_rejections (xs : List Assignment) :
    ¬ ∀ n, ∃ a ∈ xs, Test (state n) (plan n) .reject a
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Version.finite_prefix_minimum (limit : Nat) :
    ∃ xs : List Assignment, xs.length = limit ∧
      (∀ n < limit, ∃ a ∈ xs, dropped n a) ∧
      ∀ ys : List Assignment, (∀ n < limit, ∃ a ∈ ys, dropped n a) → limit ≤ ys.length
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Loose.exact_loss (n : Nat) (m : Assignment) :
    dropped n m ↔ Models (state n) m ∧ ¬ Models (installed n) m
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Loose.bad_witness (n : Nat) : dropped n (bad n)
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Loose.disjoint (a b : Nat) (earlier : a < b) (m : Assignment)
    (lost : dropped a m) (later : dropped b m) : False
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Loose.no_universal_rejections (xs : List Assignment) :
    ¬ ∀ n, ∃ a ∈ xs, Test (state n) (plan n) .reject a
```

```lean
theorem Yulang.GeneralRebaseSignedHistory297.Loose.finite_prefix_minimum (limit : Nat) :
    ∃ xs : List Assignment, xs.length = limit ∧
      (∀ n < limit, ∃ a ∈ xs, dropped n a) ∧
      ∀ ys : List Assignment, (∀ n < limit, ∃ a ∈ ys, dropped n a) → limit ≤ ys.length
```


## lean/Yulang/GeneralRebaseSignedIndex297.lean

```lean
theorem Yulang.GeneralRebaseSignedIndex297.length_exact (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) :
    (compile plans xs prior candidate).length = plans.length
```

```lean
theorem Yulang.GeneralRebaseSignedIndex297.lookup_exact (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (index : Nat) (sign : Sign) :
    lookup plans xs prior candidate index sign =
      (plans[index]?).map (fun p => hit xs (signed prior candidate) (p,sign))
```

```lean
theorem Yulang.GeneralRebaseSignedIndex297.missing_index (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (index : Nat) (sign : Sign) :
    lookup plans xs prior candidate index sign = none ↔ plans.length ≤ index
```

```lean
theorem Yulang.GeneralRebaseSignedIndex297.same_plan_same_answer (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) {i j : Nat}
    (same : plans[i]? = plans[j]?) (sign : Sign) :
    lookup plans xs prior candidate i sign = lookup plans xs prior candidate j sign
```

```lean
theorem Yulang.GeneralRebaseSignedIndex297.true_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs) (cert : Checked s plans xs prior candidate)
    (i : Nat) (p : Plan roles) (found : plans[i]? = some p) (sign : Sign) :
    lookup plans xs prior candidate i sign = some true ↔ ∃ a, Test s p sign a
```

```lean
theorem Yulang.GeneralRebaseSignedIndex297.false_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs) (cert : Checked s plans xs prior candidate)
    (i : Nat) (p : Plan roles) (found : plans[i]? = some p) (sign : Sign) :
    lookup plans xs prior candidate i sign = some false ↔ ¬ ∃ a, Test s p sign a
```


## lean/Yulang/GeneralRebaseSignedModels297.lean

```lean
theorem Yulang.GeneralRebaseSignedModels297.reject_exact (s : State roles) (p : Plan roles) :
    (∃ m, Test s p .reject m) ↔ ¬ semanticCommitted s p
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.pass_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .pass m ↔ Residual s e m
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.accepted_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .pass m ↔ Models (install s e) m
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.rejected_exact {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reg : e.registry = registry r) (snap : e.snapshot = s.core) (m : Assignment) :
    Test s e.plan .reject m ↔ Models s m ∧ ¬ Models (install s e) m
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.exclusive (s : State roles) (p : Plan roles) (m : Assignment) :
    ¬ (Test s p .pass m ∧ Test s p .reject m)
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.neither_of_no_model (s : State roles) (empty : ¬ ∃ m, Models s m)
    (p : Plan roles) (sign : Sign) : ¬ ∃ m, Test s p sign m
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.reject_loses {s : State roles} {e : Effect roles} (snap : e.snapshot = s.core)
    (m : Assignment) (rejected : Test s e.plan .reject m) :
    Models s m ∧ ¬ Models (install s e) m
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.loss_includes_delta {s : State roles} {e : Effect roles} (snap : e.snapshot = s.core)
    (m : Assignment) :
    (Models s m ∧ ¬ Models (install s e) m) ↔
      Test s e.plan .reject m ∨
      (Test s e.plan .pass m ∧ ¬ GeneralRebaseInstallDeltaModels279.Delta s e m)
```

```lean
theorem Yulang.GeneralRebaseSignedModels297.loss_exact_of_no_requests {s : State roles} {e : Effect roles}
    (snap : e.snapshot = s.core)
    (quiet : GeneralRebaseInstallDeltaModels279.NoFreshRequests s e) (m : Assignment) :
    (Models s m ∧ ¬ Models (install s e) m) ↔ Test s e.plan .reject m
```


## lean/Yulang/GeneralRebaseSignedObserver297.lean

```lean
theorem Yulang.GeneralRebaseSignedObserver297.novelty_exact (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (p : Plan roles) (listed : p ∈ entries r s root checked) (focus : Occurrence roles) :
    (withModels base xs prior test).novelty focus p = true ↔
      ¬ GeneralRebaseInstallChecks267.semanticCommitted s p
```

```lean
theorem Yulang.GeneralRebaseSignedObserver297.joint_exact (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (e : Effect roles) (listed : e.plan ∈ entries r s root checked)
    (reg : e.registry = Encoded r) (snap : e.snapshot = s.core) (focus : Occurrence roles) :
    (withModels base xs prior test).joint focus e.plan = true ↔ ∃ m, Residual s e m
```

```lean
theorem Yulang.GeneralRebaseSignedObserver297.sound_guards (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (focus : Occurrence roles) (generated : Generated s.core.erased.current root focus) :
    GeneralRebaseInstallCandidates267.Probes (Encoded r) s
      ((withModels base xs prior test).novelty focus) ((withModels base xs prior test).joint focus)
      (atFocus (Encoded r) s root focus (declChecked checked))
```

```lean
theorem Yulang.GeneralRebaseSignedObserver297.complete_guards (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (focus : Occurrence roles) (generated : Generated s.core.erased.current root focus) :
    GeneralRebaseInstallCoverage267.Covers (Encoded r) s
      ((withModels base xs prior test).novelty focus) ((withModels base xs prior test).joint focus)
      (atFocus (Encoded r) s root focus (declChecked checked))
```

```lean
theorem Yulang.GeneralRebaseSignedObserver297.contracts (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (other : Other r s root checked (withModels base xs prior test)) :
    GeneralRebaseObserverSound267.Sound r s root checked (withModels base xs prior test) ∧
      GeneralRebaseObserverCoverage267.Covers r s root checked (withModels base xs prior test)
```

```lean
theorem Yulang.GeneralRebaseSignedObserver297.strict_exact (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (other : Other r s root checked (withModels base xs prior test))
    (owners : List Nat) (pool : List Output)
    (target : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step
      (GeneralRebaseObserverExact267.observe r root s checked (withModels base xs prior test) owners pool)
      (project owners pool s) target ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      project owners pool after = target ∧ target ≠ project owners pool s
```


## lean/Yulang/GeneralRebaseSignedOptional297.lean

```lean
theorem Yulang.GeneralRebaseSignedOptional297.negative : Test before plan .reject model
```

```lean
theorem Yulang.GeneralRebaseSignedOptional297.positive : Test before plan .pass extended
```

```lean
theorem Yulang.GeneralRebaseSignedOptional297.no_new_edge : edgesRecorded before.core.erased.current plan = true
```

```lean
theorem Yulang.GeneralRebaseSignedOptional297.structural_gate_empty :
    GeneralRebaseNoveltyProbe267.novel before (fun _ => false) plan = false
```

```lean
theorem Yulang.GeneralRebaseSignedOptional297.semantically_enabled :
    ¬ GeneralRebaseInstallChecks267.semanticCommitted before plan ∧
    ∃ m, Test before plan .pass m
```

```lean
theorem Yulang.GeneralRebaseSignedOptional297.mixed_raw_actual :
    GeneralNominalVersionedMixedKernel234.Step registry root before installed
```


## lean/Yulang/GeneralRebaseSignedRefresh297.lean

```lean
theorem Yulang.GeneralRebaseSignedRefresh297.interp (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context) :
    ctx.interpretation = p.packet.context.interpretation
```

```lean
theorem Yulang.GeneralRebaseSignedRefresh297.class_exact (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (m : Assignment) :
    ClassEffects (refresh s ctx).core p.packet.site.occurrence (moved cert current) m ↔
    ClassEffects s.core p.packet.site.occurrence p m
```

```lean
theorem Yulang.GeneralRebaseSignedRefresh297.candidate_exact (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (m : Assignment) (prior : Models s m) :
    Conditions (refresh s ctx) (moved cert current) m ↔ Conditions s p m
```

```lean
theorem Yulang.GeneralRebaseSignedRefresh297.preserves_test (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (sign : Sign) (m : Assignment) :
    Test (refresh s ctx) (moved cert current) sign m ↔ Test s p sign m
```

```lean
theorem Yulang.GeneralRebaseSignedRefresh297.preserves_covers (cert : Refresh s ctx) (current : p.packet.context = s.core.erased.current.context)
    (seen : Observed p) (xs : List Assignment) (sign : Sign)
    (cover : (∃ m, Test s p sign m) → ∃ m ∈ xs, Test s p sign m) :
    (∃ m, Test (refresh s ctx) (moved cert current) sign m) →
      ∃ m ∈ xs, Test (refresh s ctx) (moved cert current) sign m
```


## lean/Yulang/GeneralRebaseSignedSupport297.lean

```lean
theorem Yulang.GeneralRebaseSignedSupport297.restrict {ids watched : List Nat} {a b : Assignment}
    (supports : ids ⊆ watched) (agree : Agree watched a b) : Agree ids a b
```

```lean
theorem Yulang.GeneralRebaseSignedSupport297.conditions_iff (s : State roles) (p : Plan roles) (a b : Assignment)
    (agree : Agree (candidateReads s p) a b) : Conditions s p a ↔ Conditions s p b
```

```lean
theorem Yulang.GeneralRebaseSignedSupport297.prior_iff {s : State roles} {r : Registry} {root : Occurrence roles}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s) (a b : Assignment)
    (agree : Agree (journalReads s) a b) : Models s a ↔ Models s b
```

```lean
theorem Yulang.GeneralRebaseSignedSupport297.on_prior_models (s : State roles) (p : Plan roles) (sign : Sign)
    (a b : Assignment) (oldA : Models s a) (oldB : Models s b)
    (agree : Agree (candidateReads s p) a b) :
    Test s p sign a ↔ Test s p sign b
```

```lean
theorem Yulang.GeneralRebaseSignedSupport297.signed_iff {s : State roles} {r : Registry} {root : Occurrence roles}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (p : Plan roles) (sign : Sign) (a b : Assignment)
    (agree : Agree (journalReads s ++ candidateReads s p) a b) :
    Test s p sign a ↔ Test s p sign b
```


## lean/Yulang/GeneralRebaseSourceMetadata297.lean

```lean
theorem Yulang.GeneralRebaseSourceMetadata297.context_equalities {r : Registry} {root : Occurrence roles}
    {before after : State roles} (action : Step (Encoded r) root before after) :
    (current after).state.constructors = (current before).state.constructors ∧
      (current after).interpretation = (current before).interpretation
```

```lean
theorem Yulang.GeneralRebaseSourceMetadata297.fixed_metadata {r : Registry} {root : Occurrence roles}
    {before after : State roles} (action : Step (Encoded r) root before after) :
    Metadata (Encoded r) (current after) ↔ Metadata (Encoded r) (current before)
```

```lean
theorem Yulang.GeneralRebaseSourceMetadata297.reachable_metadata {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4TargetV8.Reachable (Boundary roles) r root s) :
    Metadata (Encoded r) (current s)
```

```lean
theorem Yulang.GeneralRebaseSourceMetadata297.source_strict_exact {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} {xs : List Assignment} {c : Checks roles}
    {safety : Occurrence roles → Bool}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (safe : ExactSafety r s root safety)
    (cover : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (t : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (GeneralRebaseLiveProjection264.project owners pool s) t ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      GeneralRebaseLiveProjection264.project owners pool after = t ∧
      t ≠ GeneralRebaseLiveProjection264.project owners pool s
```


## lean/Yulang/GeneralRebaseSourceQuestions297.lean

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.of_focus (r : Registry) (s : State roles) (root f : Occurrence roles)
    (checked : (Boundary roles).Checked r)
    (generated : GeneralNominalSaturationState.Generated s.core.erased.current root f)
    (p : Plan roles) (present : p ∈ atFocus (Encoded r) s root f (declChecked checked)) :
    p ∈ entries r s root checked
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.entries_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) :
    p ∈ entries r s root checked ↔
      ∃ f, GeneralNominalSaturationState.Generated s.core.erased.current root f ∧
        p ∈ atFocus (Encoded r) s root f (declChecked checked)
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.question_exact (plans : List (Plan roles)) (p : Plan roles) (sign : Sign) :
    (p,sign) ∈ questions plans ↔ p ∈ plans
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.question_count (plans : List (Plan roles)) :
    (questions plans).length = 2 * plans.length
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.materialize_covers (s : State roles) (plans : List (Plan roles)) :
    Covers (holds s) (questions plans) (materialize s plans)
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.materialize_size (s : State roles) (plans : List (Plan roles)) :
    (materialize s plans).length ≤ 2 * plans.length
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.signed_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (check : Checked s plans xs prior candidate) (p : Plan roles) (listed : p ∈ plans)
    (sign : Sign) (a : Assignment) (found : a ∈ xs) :
    signed prior candidate (p,sign) a = true ↔ Test s p sign a
```

```lean
theorem Yulang.GeneralRebaseSourceQuestions297.exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs)
    (check : Checked s plans xs prior candidate) (p : Plan roles) (listed : p ∈ plans) (sign : Sign) :
    hit xs (signed prior candidate) (p,sign) = true ↔ ∃ m, Test s p sign m
```


## lean/Yulang/GeneralRebaseSourceWitnessProgram297.lean

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.pairs_exact (s : State roles) (a b : Site roles) :
    (a,b) ∈ registeredPairs s ↔ a ∈ s.core.sites ∧ b ∈ s.core.sites
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.pairs_size (s : State roles) :
    (registeredPairs s).length = s.core.sites.length * s.core.sites.length
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.head_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) (found : p ∈ entries r s root checked) :
    Question.head p ∈ questions r s root checked
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.install_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) (found : p ∈ entries r s root checked) (sign : Sign) :
    Question.install p sign ∈ questions r s root checked
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.merge_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (pair : Pair roles) (found : pair ∈ registeredPairs s) :
    Question.mergeFailure pair ∈ questions r s root checked
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.questions_size (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    (questions r s root checked).length =
      3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.mergeBit_exact {s : State roles} {xs : List Assignment} {plans : List (Plan roles)} {c : Checks roles}
    (cert : Observed s xs plans c) (pair : Pair roles) (listed : pair ∈ registeredPairs s)
    (a : Assignment) (seen : a ∈ xs) :
    mergeBit c pair a = true ↔ GeneralRebaseMergeQuestions297.counter s pair a
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.materialize_covers (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    Covers (Holds s) (questions r s root checked) (materialize r s root checked)
```

```lean
theorem Yulang.GeneralRebaseSourceWitnessProgram297.materialize_size (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    (materialize r s root checked).length ≤
      3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length
```


## lean/Yulang/GeneralRebaseWitnessAnchor297.lean

```lean
theorem Yulang.GeneralRebaseWitnessAnchor297.at_most_succ {s : State roles} (plans : List (Plan roles)) (a : Prior s) :
    (around plans a).length ≤ plans.length + 1
```

```lean
theorem Yulang.GeneralRebaseWitnessAnchor297.around_covers {s : State roles} (plans : List (Plan roles)) (a : Prior s) :
    Covers (holds s) (questions plans) (values (around plans a))
```

```lean
theorem Yulang.GeneralRebaseWitnessAnchor297.exists_pool (s : State roles) (plans : List (Plan roles)) :
    ∃ pool : List (Prior s), pool.length ≤ plans.length + 1 ∧
      Covers (holds s) (questions plans) (values pool)
```

```lean
theorem Yulang.GeneralRebaseWitnessAnchor297.opposed_requires_two {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    (cover : Covers (holds s) (questions plans) xs) (p : Plan roles) (listed : p ∈ plans)
    (yes : ∃ a, Test s p .pass a) (no : ∃ a, Test s p .reject a) :
    2 ≤ xs.length
```


## lean/Yulang/GeneralRebaseWitnessContracts297.lean

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.install_coverage (covered : Covers (Holds s) (questions r s root checked) xs) :
    Covers (GeneralRebaseSourceQuestions297.holds s)
      (GeneralRebaseSourceQuestions297.questions (entries r s root checked)) xs
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.merge_coverage (covered : Covers (Holds s) (questions r s root checked) xs) :
    Covers (GeneralRebaseMergeQuestions297.counter s) (registeredPairs s) xs
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.head_exact (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c) (p : Plan roles)
    (listed : p ∈ entries r s root checked) :
    hit xs c.head p = true ↔ GeneralRebaseCandidatePrepared267.headCondition p
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.honest (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (f : Occurrence roles) (generated : Generated s.core.erased.current root f) :
    Honest ((callbacks xs c).head f) (atFocus (Encoded r) s root f (declChecked checked))
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.head_total (f : Occurrence roles) :
    GeneralRebaseCompleteHeadProbe267.Covered ((callbacks xs c).head f)
      (atFocus (Encoded r) s root f (declChecked checked))
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.merge_exact (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (first : Site roles) (one : first ∈ s.core.sites) (last : Site roles) (two : last ∈ s.core.sites) :
    (callbacks xs c).mergeInputs first last = true ↔ SameInputs (Models s) first last
```

```lean
theorem Yulang.GeneralRebaseWitnessContracts297.all_observer_contracts (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded r) s.core.erased.current.context)
    (diagnostics : ∀ f, ∀ p ∈ GeneralRebaseSourceObserver267.installAt r s root f checked (callbacks xs c),
       GeneralRebaseSourceSelect267.Guard r s f p.packet.declaration.id) :
    GeneralRebaseObserverSound267.Sound r s root checked (callbacks xs c) ∧
      GeneralRebaseObserverCoverage267.Covers r s root checked (callbacks xs c)
```


## lean/Yulang/GeneralRebaseWitnessExistence297.lean

```lean
theorem Yulang.GeneralRebaseWitnessExistence297.flag_exact (p : Prop) : flag p = true ↔ p
```

```lean
theorem Yulang.GeneralRebaseWitnessExistence297.all_checked (s : State roles) (plans : List (Plan roles)) (xs : List Assignment) :
    Observed s xs plans (checks s)
```

```lean
theorem Yulang.GeneralRebaseWitnessExistence297.finite_statement (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    ∃ xs : List Assignment, ∃ c : Checks roles,
      xs.length ≤ 3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length ∧
      Covers (Holds s) (questions r s root checked) xs ∧
        Observed s xs (entries r s root checked) c
```

```lean
theorem Yulang.GeneralRebaseWitnessExistence297.smaller_pool (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    ∃ xs : List Assignment, xs.length ≤
      2 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length + 1 ∧
      Covers (Holds s) (questions r s root checked) xs
```

```lean
theorem Yulang.GeneralRebaseWitnessExistence297.finite_raw_observer (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (owners : List Nat) (pool : List Output) :
    ∃ xs : List Assignment, ∃ c : Checks roles, ∃ gate : Occurrence roles → Bool,
      xs.length ≤ 3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length ∧
      ∀ target,
        GeneralRebaseStep258.Step (observe r s root checked xs c gate owners pool)
          (GeneralRebaseLiveProjection264.project owners pool s) target ↔
        ∃ after, (Boundary roles).Step r root s after ∧
          GeneralRebaseLiveProjection264.project owners pool after = target ∧
          target ≠ GeneralRebaseLiveProjection264.project owners pool s
```

Indexed 176 theorem declarations. Each has one standalone audit.
