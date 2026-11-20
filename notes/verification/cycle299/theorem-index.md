# Cycle 299: exact theorem signatures

## lean/Yulang/GeneralGeneratedDictionaryAcc299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.step_fuel (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : run read (n+1) x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.monotone_fuel (read : Read) (n m x : Nat) (d : Dictionary)
    (leq : n ≤ m) (hit : run read n x = some d) : run read m x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.child_sound {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    {read : Read} {decode : Nat → v.Demand}
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    {x a : Nat} (edge : Edge read a x) : Child (Local b r s) (decode a) (decode x)
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.pull_accessibility {α β} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (sound : ∀ a x, R a x → S (f a) (f x))
    (y : β) (marked : Acc S y) : ∀ x, f x = y → Acc R x
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.source_accessible {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    {read : Read} {decode : Nat → v.Demand}
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (x : Nat) (acc : Acc (Child (Local b r s)) (decode x)) : Acc (Edge read) x
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.success_accessible (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : Acc (Edge read) x
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.common_fuel (read : Read) (children : List Nat)
    (each : ∀ c ∈ children, ∃ n dc, run read n c = some dc) :
    ∃ n, ∀ c ∈ children, ∃ dc, run read n c = some dc
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.accessible_success (read : Read) (closed : Closed read) (x : Nat)
    (acc : Acc (Edge read) x) :
    ∀ row, read x = some row → ∃ n d, run read n x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryAcc299.iff_accessible (read : Read) (closed : Closed read) (x : Nat)
    {row : Entry} (hit : read x = some row) :
    (∃ n d, run read n x = some d) ↔ Acc (Edge read) x
```


## lean/Yulang/GeneralGeneratedDictionaryCoherent299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryCoherent299.selected_unique (a c : Dictionary) (d : v.Demand)
    (one : Classify b r s d (.selected a))
    (two : Classify b r s d (.selected c)) : a = c
```

```lean
theorem Yulang.GeneralGeneratedDictionaryCoherent299.ordered_unique (a c : List Dictionary) (ds : List v.Demand)
    (one : All₂ (fun d dict => Classify b r s d (.selected dict)) ds a)
    (two : All₂ (fun d dict => Classify b r s d (.selected dict)) ds c) : a = c
```

```lean
theorem Yulang.GeneralGeneratedDictionaryCoherent299.cross_table (first second : Read) (decode₁ decode₂ : Nat → v.Demand)
    (check₁ : Faithful (b:=b) (r:=r) (s:=s) first decode₁)
    (check₂ : Faithful (b:=b) (r:=r) (s:=s) second decode₂)
    (n m i j : Nat) (a c : Dictionary) (same : decode₁ i = decode₂ j)
    (one : run first n i = some a) (two : run second m j = some c) : a = c
```


## lean/Yulang/GeneralGeneratedDictionaryControls299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.cycle_not_accessible : ¬ Acc (Edge cyclic) 0
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.cycle_no_budget (cap : Nat) : run cyclic cap 0 = none
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.cycle_check_false : checkMemo cyclic [0] 1 = false
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.missing_not_closed : ¬ Closed missing
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.missing_result : run missing 5 0 = none
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.missing_check_false : checkMemo missing [0,1] 2 = false
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.retains_duplicate : run repeated 2 0 = some (.node 8 [.node 9 [],.node 9 []])
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.ordered_height : height (.node 8 [.node 9 [],.node 9 []]) = 2
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.exactly_two_or_more (n : Nat) :
    run repeated n 0 = some (.node 8 [.node 9 [],.node 9 []]) ↔ 2 ≤ n
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.no_false_rejection :
    compile GeneralGeneratedDisplayObserved299.lookup (fun _ => none) 0 = .unindexed ∧
      compile GeneralGeneratedDisplayObserved299.lookup (fun _ => none) 9 = .absent
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.diagnostic_distinction :
    compile (fun (_ : Nat) => (some (.pending : Frontier Unit))) (fun _ => none) 0 = .pending ∧
      compile (fun _ => (some (.rejected : Frontier Unit))) (fun _ => none) 0 = .rejected ∧
      compile (fun _ => (some (.ambiguous : Frontier Unit))) (fun _ => none) 0 = .ambiguous
```

```lean
theorem Yulang.GeneralGeneratedDictionaryControls299.rigid_depth_check :
    checkMemo GeneralGeneratedRigidNested299.table [0,1,2] 2 = false ∧
      checkMemo GeneralGeneratedRigidNested299.table [0,1,2] 3 = true ∧
      bitFirst GeneralGeneratedRigidNested299.table [0,1,2] 0 3 = some 3
```


## lean/Yulang/GeneralGeneratedDictionaryFiniteCap299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.acc_no_loop {α : Type} {R : α → α → Prop} {a : α} (acc : Acc R a) : ¬ R a a
```

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.no_return (read : Read) (x a : Nat) (acc : Acc (Edge read) x)
    (edge : Edge read a x) (y : Nat)
    (descendant : y = a ∨ Relation.TransGen (Edge read) y a) : y ≠ x
```

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.descends_known (read : Read) (closed : Closed read) (x c : Nat)
    (path : Relation.TransGen (Edge read) c x) :
    (∃ row, read x = some row) → (∃ row, read c = some row)
```

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.bounded_from (read : Read) (closed : Closed read) (x : Nat)
    (acc : Acc (Edge read) x) (remaining : List Nat)
    (within : ∀ y, y = x ∨ Relation.TransGen (Edge read) y x → y ∈ remaining)
    (row : Entry) (hit : read x = some row) :
    ∃ d, run read remaining.length x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.finite_cap (read : Read) (domain : List Nat) (closed : Closed read)
    (known : Known read domain) (x : Nat) (acc : Acc (Edge read) x)
    (row : Entry) (hit : read x = some row) :
    ∃ d, run read domain.length x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryFiniteCap299.check_length (read : Read) (domain : List Nat) (closed : Closed read)
    (known : Known read domain) :
    check read domain domain.length = true ↔
      ∀ x ∈ domain, (∃ row, read x = some row) ∧ Acc (Edge read) x
```


## lean/Yulang/GeneralGeneratedDictionaryHeight299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.tall_bound {α : Type} {P : α → Dictionary → Prop}
    {xs : List α} {ds : List Dictionary} (h : All₂ P xs ds)
    (n : Nat) (bound : ∀ x d, P x d → height d ≤ n) : tall ds ≤ n
```

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.lower_children {α : Type} {P Q : α → Dictionary → Prop}
    {xs : List α} {ds : List Dictionary} (h : All₂ P xs ds)
    (n : Nat) (next : ∀ x d, P x d → height d ≤ n → Q x d)
    (bound : tall ds ≤ n) : All₂ Q xs ds
```

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.lower_bound (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : height d ≤ n
```

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.replay_height (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (m : Nat) (enough : height d ≤ m) :
    run read m x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.height_threshold (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (m : Nat) : run read m x = some d ↔ height d ≤ m
```

```lean
theorem Yulang.GeneralGeneratedDictionaryHeight299.earliest_is_height (read : Read) (cap x k : Nat)
    (hit : earliest read x cap = some k) (n : Nat) (d : Dictionary)
    (out : run read n x = some d) : k = height d
```


## lean/Yulang/GeneralGeneratedDictionaryMemo299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryMemo299.lookup_present (f : Nat → Bool) (domain : List Nat) (i : Nat)
    (present : i ∈ domain) :
    lookup i (domain.map (fun j => (j,f j))) = f i
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMemo299.lookup_absent (f : Nat → Bool) (domain : List Nat) (i : Nat)
    (absent : i ∉ domain) :
    lookup i (domain.map (fun j => (j,f j))) = false
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMemo299.stage_exact (read : Read) (n : Nat) (prev : Nat → Bool)
    (correct : ∀ j, prev j = true ↔ ∃ d, run read n j = some d) (i : Nat) :
    stage read prev i = true ↔ ∃ d, run read (n+1) i = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMemo299.memo_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (n i : Nat) :
    lookup i (memo read domain n) = true ↔ ∃ d, run read n i = some d
```


## lean/Yulang/GeneralGeneratedDictionaryMemoCheck299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryMemoCheck299.checked_iff (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) : checkMemo read domain cap = true ↔ check read domain cap = true
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMemoCheck299.checked_length (read : Read) (domain : List Nat) (known : Known read domain)
    (closed : Closed read) :
    checkMemo read domain domain.length = true ↔
      ∀ x ∈ domain, (∃ row, read x = some row) ∧ Acc (Edge read) x
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMemoCheck299.bit_first_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (x cap : Nat) : bitFirst read domain x cap = earliest read x cap
```


## lean/Yulang/GeneralGeneratedDictionaryMinFuel299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryMinFuel299.earliest_none (read : Read) (i cap : Nat) (no : earliest read i cap = none) :
    ∀ j, j ≤ cap → run read j i = none
```

```lean
theorem Yulang.GeneralGeneratedDictionaryMinFuel299.earliest_some (read : Read) (i cap k : Nat) (found : earliest read i cap = some k) :
    k ≤ cap ∧ Exact read i k
```


## lean/Yulang/GeneralGeneratedDictionaryNodes299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryNodes299.from_evidenceAt (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (closed : Closed read)
    (atRoot : B4SkeletonV8.EvidenceAt b r s root) : Nodes b r s read decode
```

```lean
theorem Yulang.GeneralGeneratedDictionaryNodes299.same_model (read : Read) (decode : Nat → v.Demand) (nodes : Nodes b r s read decode)
    (m : v.Model) (valid : b.Models s m) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : b.Evidence r s m (decode x) d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryNodes299.constructs (read : Read) (decode : Nat → v.Demand) (rank : Nat → Nat)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (nodes : Nodes b r s read decode)
    (decreases : Ranked read rank) (closed : Closed read) (x : Nat) {row : Entry}
    (hit : read x = some row) :
    ∃ d, run read (rank x+1) x = some d ∧ Classify b r s (decode x) (.selected d) ∧
      ∀ m, b.Models s m → b.Evidence r s m (decode x) d
```


## lean/Yulang/GeneralGeneratedDictionaryRankBook299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.get_present (f : Nat → Option Nat) (domain : List Nat) (i : Nat) (present : i ∈ domain) :
    get i (domain.map (fun j => (j,f j))) = f i
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.get_missing (f : Nat → Option Nat) (domain : List Nat) (i : Nat) (absent : i ∉ domain) :
    get i (domain.map (fun j => (j,f j))) = none
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.earliest_at_cap (read : Read) (i cap : Nat) :
    (earliest read i cap).isSome = true ↔ ∃ d, run read cap i = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.earliest_outside (read : Read) (domain : List Nat) (known : Known read domain)
    (i n : Nat) (missing : i ∉ domain) : earliest read i n = none
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.ranks_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (i n : Nat) : get i (ranks read domain n) = earliest read i n
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.book_rank_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) : bookRank read domain cap = inferredRank read cap
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.book_check (read : Read) (domain : List Nat) (known : Known read domain) (cap : Nat) :
    ready read domain cap = true ↔ check read domain cap = true
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankBook299.book_ranked (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) (pass : ready read domain cap = true) :
    Ranked read (bookRank read domain cap)
```


## lean/Yulang/GeneralGeneratedDictionaryRankCheck299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryRankCheck299.checked_at (read : Read) (domain : List Nat) (cap : Nat)
    (pass : check read domain cap = true) {i : Nat} (member : i ∈ domain) :
    (∃ row, read i = some row) ∧ ∃ k, earliest read i cap = some k
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankCheck299.no_later (read : Read) (i cap k n : Nat)
    (atCap : earliest read i cap = some k) (hit : ∃ d, run read n i = some d) : k ≤ n
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankCheck299.checked_closed (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true) : Closed read
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankCheck299.checked_ranked (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true) :
    Ranked read (inferredRank read cap)
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankCheck299.checked_total (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true)
    (i : Nat) (e : Entry) (hit : read i = some e) :
    ∃ d, run read cap i = some d
```


## lean/Yulang/GeneralGeneratedDictionaryRankExists299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryRankExists299.found_at_cap (read : Read) (i cap : Nat)
    (hit : ∃ d, run read cap i = some d) : ∃ k, earliest read i cap = some k
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankExists299.all_tested_bound (read : Read) (domain : List Nat) (closed : Closed read)
    (covered : ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i) :
    ∃ cap, check read domain cap = true
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankExists299.finite_exact (read : Read) (domain : List Nat) (closed : Closed read) :
    (∃ cap, check read domain cap = true) ↔
      ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRankExists299.ranked_of_finite_accessibility (read : Read) (domain : List Nat)
    (known : Known read domain) (closed : Closed read)
    (covered : ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i) :
    ∃ cap, check read domain cap = true ∧ Ranked read (inferredRank read cap)
```


## lean/Yulang/GeneralGeneratedDictionaryRootedFixtures299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryRootedFixtures299.rooted_observed : Rooted observedTable 0
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRootedFixtures299.actual_from_rooted :
    Classify (boundary roles) registry after displayRoot (.selected (.node 1 [.node 3 []])) ∧
    (∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]))
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRootedFixtures299.actual_rank_book :
    get 0 (ranks observedTable [0,1] 2) = some 2 ∧
    get 1 (ranks observedTable [0,1] 2) = some 1 ∧ ready observedTable [0,1] 2 = true
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRootedFixtures299.actual_keys : keys unrelated 2 0 = [0,1]
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRootedFixtures299.clean_slice : (run rootSlice 2 0 = some (.node 2 [.node 4 []])) ∧
    Rooted rootSlice 0 ∧ Closed rootSlice
```


## lean/Yulang/GeneralGeneratedDictionaryRun299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryRun299.collect_exact (f : Nat → Option Dictionary) (xs : List Nat) (ds : List Dictionary) :
    collect f xs = some ds ↔ All₂ (fun x d => f x = some d) xs ds
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRun299.collect_exists (f : Nat → Option Dictionary) (xs : List Nat)
    (total : ∀ x ∈ xs, ∃ d, f x = some d) : ∃ ds, collect f xs = some ds
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRun299.run_exact (read : Read) (n x : Nat) (d : Dictionary) :
    run read (n+1) x = some d ↔ ∃ row ds, read x = some row ∧
      All₂ (fun child dict => run read n child = some dict) row.children ds ∧
      d = .node row.key ds
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRun299.total_with_fuel (read : Read) (rank : Nat → Nat) (decreases : Ranked read rank)
    (closed : Closed read) (n x : Nat) (enough : rank x < n)
    {row : Entry} (seen : read x = some row) : ∃ d, run read n x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryRun299.rank_suffices (read : Read) (rank : Nat → Nat) (decreases : Ranked read rank)
    (closed : Closed read) (x : Nat) {row : Entry} (seen : read x = some row) :
    ∃ d, run read (rank x + 1) x = some d
```


## lean/Yulang/GeneralGeneratedDictionaryScope299.lean

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.map_all {α β γ} {P : α → β → Prop} {Q : γ → β → Prop}
    (f : α → γ) (h : ∀ a d, P a d → Q (f a) d) {xs : List α} {ds : List β}
    (all : All₂ P xs ds) : All₂ Q (xs.map f) ds
```

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.all_left {α β} {P : α → β → Prop} {xs : List α} {ds : List β}
    (h : All₂ P xs ds) (x : α) (mem : x ∈ xs) : ∃ d, P x d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.run_has_row {read : Read} {n x : Nat} {d : Dictionary}
    (ok : run read n x = some d) : ∃ row, read x = some row
```

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.classifies (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : Classify b r s (decode x) (.selected d)
```

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.same_model (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (node : B4SkeletonV8.EvidenceAt b r s root)
    (m : v.Model) (valid : b.Models s m) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) : b.Evidence r s m (decode x) d
```

```lean
theorem Yulang.GeneralGeneratedDictionaryScope299.constructs (read : Read) (decode : Nat → v.Demand) (rank : Nat → Nat)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (scope : InScope b r s root read decode) (node : B4SkeletonV8.EvidenceAt b r s root)
    (decreases : Ranked read rank) (closed : Closed read) (x : Nat) {row : Entry}
    (hit : read x = some row) :
    ∃ d, run read (rank x+1) x = some d ∧ Classify b r s (decode x) (.selected d) ∧
      ∀ m, b.Models s m → b.Evidence r s m (decode x) d
```


## lean/Yulang/GeneralGeneratedDictionarySlice299.lean

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.below_keys (read : Read) (n x c y : Nat) (row : Entry)
    (hit : read x = some row) (mem : c ∈ row.children)
    (nested : y ∈ keys read n c) :
    y ∈ keys read (n+1) x
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.keys_path (read : Read) (n x i : Nat) (member : i ∈ keys read n x) :
    i = x ∨ Relation.TransGen (Edge read) i x
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.restricted_hit (read : Read) (keep : List Nat) (i : Nat) (row : Entry)
    (found : restrict read keep i = some row) : i ∈ keep ∧ read i = some row
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.retained_path (read : Read) (n x : Nat) (keep : List Nat)
    (coverage : ∀ i ∈ keys read n x, i ∈ keep) (i : Nat) (member : i ∈ keys read n x) :
    i = x ∨ Relation.TransGen (Edge (restrict read keep)) i x
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.rooted (read : Read) (n x : Nat) : Rooted (restrict read (keys read n x)) x
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.all_with_key {P Q : Nat → Dictionary → Prop}
    {xs : List Nat} {ds : List Dictionary} (given : All₂ P xs ds)
    (cast : ∀ i ∈ xs, ∀ d, P i d → Q i d) : All₂ Q xs ds
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.preserves (read : Read) (n x : Nat) (d : Dictionary)
    (ok : run read n x = some d) (keep : List Nat)
    (coverage : ∀ i ∈ keys read n x, i ∈ keep) :
    run (restrict read keep) n x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.at_root (read : Read) (n x : Nat) (d : Dictionary) (hit : run read n x = some d) :
    run (restrict read (keys read n x)) n x = some d
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.have_row (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (i : Nat) (visited : i ∈ keys read n x) :
    (∃ row, read i = some row)
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.knows_children (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (i : Nat) (visited : i ∈ keys read n x)
    (atI : Entry) (atOk : read i = some atI) (c : Nat) (child : c ∈ atI.children) :
    c ∈ keys read n x
```

```lean
theorem Yulang.GeneralGeneratedDictionarySlice299.closed_slice (read : Read) (n x : Nat) (d : Dictionary) (hit : run read n x = some d) :
    Closed (restrict read (keys read n x))
```


## lean/Yulang/GeneralGeneratedDisplayBothCurrent299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayBothCurrent299.providers : Providers registry after table decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayBothCurrent299.local_nodes : Nodes (boundary roles) registry after table decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayBothCurrent299.root_from_current (m) (held : Models after m) :
    (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []])
```

```lean
theorem Yulang.GeneralGeneratedDisplayBothCurrent299.child_from_current (m) (held : Models after m) :
    (boundary roles).Evidence registry after m displayChild (.node 3 [])
```

```lean
theorem Yulang.GeneralGeneratedDisplayBothCurrent299.instantiated :
    (∃ m, Models after m) ∧
    (Reachable (boundary roles) registry displayRoot after) ∧
    (∀ m, Models after m →
      (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) ∧
      (boundary roles).Evidence registry after m displayChild (.node 3 []))
```


## lean/Yulang/GeneralGeneratedDisplayComplete299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayComplete299.observed_closed : Closed observedTable
```

```lean
theorem Yulang.GeneralGeneratedDisplayComplete299.checked_all_rows (i : Nat) (e : Entry) (read : observedTable i = some e) (d : Dictionary) :
    run observedTable 2 i = some d ↔ Classify (boundary roles) registry after (decode i) (.selected d)
```

```lean
theorem Yulang.GeneralGeneratedDisplayComplete299.modeled (i : Nat) (d : Dictionary) (got : run observedTable 2 i = some d)
    (m) (valid : Models after m) : (boundary roles).Evidence registry after m (decode i) d
```

```lean
theorem Yulang.GeneralGeneratedDisplayComplete299.exact_and_modeled (i : Nat) (e : Entry) (seen : observedTable i = some e) (d : Dictionary) :
    run observedTable 2 i = some d ↔
      Classify (boundary roles) registry after (decode i) (.selected d) ∧
      ∀ m, Models after m → (boundary roles).Evidence registry after m (decode i) d
```

```lean
theorem Yulang.GeneralGeneratedDisplayComplete299.actual_accessibility :
    Acc (Child (Local (boundary roles) registry after)) displayRoot ∧
    Acc (Child (Local (boundary roles) registry after)) displayChild
```


## lean/Yulang/GeneralGeneratedDisplayObserved299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.roundtrip (g : Goal) (i : Nat) (hit : encode g = some i) : decode i = invocation g
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.observed (i : Nat) (f : Frontier Goal) (hit : lookup i = some f) :
    Local (boundary roles) registry after (decode i) (translate invocation f)
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.faithful : Faithful (b:=boundary roles) (r:=registry) (s:=after) observedTable decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.checked_rows : observedTable = table
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.known : Known observedTable [0,1]
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.known_pass : checkMemo observedTable [0,1] 2 = true
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.least_depth : bitFirst observedTable [0,1] 0 2 = some 2
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.no_child_below_child (d) : ¬ Child (Local (boundary roles) registry after) d displayChild
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.child_exact (d) : Child (Local (boundary roles) registry after) d displayRoot ↔ d = displayChild
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.semantically_accessible : Acc (Child (Local (boundary roles) registry after)) displayRoot
```

```lean
theorem Yulang.GeneralGeneratedDisplayObserved299.observed_result (m) (valid : Models after m) :
    (∃ d, run observedTable 2 0 = some d ∧
      Classify (boundary roles) registry after displayRoot (.selected d) ∧
      (boundary roles).Evidence registry after m displayRoot d)
```


## lean/Yulang/GeneralGeneratedDisplayParentCurrent299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.original_sites : emitted GeneralRebaseCompiledDisplay277.parent = [centerSite]
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.replay_sites : emitted parent = [centerSite]
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.new_raw_site (site) (seen : site ∈ (installCore after.core parent).erased.current.sites) :
    site ∈ after.core.erased.current.sites
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.no_additional_requests (focus) (out) :
    out ∈ requests (installCore after.core parent) focus ↔ out ∈ requests after.core focus
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.noRequests (focus) : requests (installCore after.core parent) focus = []
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.commonModel : InstallationModels after certificate model
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.compatible : GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current parent.packet
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.inspection_length :
    (GeneralNominalCenteredSteps.inspection parent).inspected.length =
      (GeneralNominalCenteredSteps.inspection parent).tests.length
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.positions : GeneralNominalVersionedCycles232.Safe after parent
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.alternatives : GeneralNominalVersionedMixedKernel234.AlternativesSafe compiled after parent.input
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.current : Current compiled after displayRoot certificate
```

```lean
theorem Yulang.GeneralGeneratedDisplayParentCurrent299.installable_but_committed :
    GeneralNominalVersionedMixedKernel234.Installable compiled after certificate ∧
      GeneralNominalVersionedMixedKernel234.Committed after certificate.plan
```


## lean/Yulang/GeneralGeneratedDisplayPhase299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.child_not_generated :
    ¬ GeneralNominalSaturationState.Generated before.core.erased.current displayRoot displayChild
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.before_not_authorized : ¬ Authorized before
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.after_authorized : Authorized after
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.exact_authorization (s : State roles) (route : Route s) :
    Authorized s ↔ s = after
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.initial_child_no_evidence (m : Assignment) (p : Payload) :
    ¬ (boundary roles).Evidence registry before m displayChild p
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.initial_parent_no_evidence (m : Assignment) (p : Payload) :
    ¬ (boundary roles).Evidence registry before m displayRoot p
```

```lean
theorem Yulang.GeneralGeneratedDisplayPhase299.genuine_phase_change :
    (boundary roles).Step registry displayRoot before after ∧
      (∀ m, Models after m ↔ Models before m) ∧
      (∀ m p, ¬ (boundary roles).Evidence registry before m displayRoot p) ∧
      ∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []])
```


## lean/Yulang/GeneralGeneratedDisplayTable299.lean

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.rows (x : Nat) (row : Entry) (hit : table x = some row) :
    (x = 0 ∧ row = ⟨1,[1]⟩) ∨ (x = 1 ∧ row = ⟨3,[]⟩)
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.ranked : Ranked table rank
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.closed : Closed table
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.faithful : Faithful (b:=boundary roles) (r:=registry) (s:=after) table decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.in_scope : InScope (boundary roles) registry after displayRoot table decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.nodes : Nodes (boundary roles) registry after table decode
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.computed_child : run table 1 1 = some (.node 3 [])
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.computed_root : run table 2 0 = some (.node 1 [.node 3 []])
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.insufficient : run table 1 0 = none
```

```lean
theorem Yulang.GeneralGeneratedDisplayTable299.actual_result :
    Reachable (boundary roles) registry displayRoot after ∧
    Classify (boundary roles) registry after displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []])
```


## lean/Yulang/GeneralGeneratedFrontierReceipt299.lean

```lean
theorem Yulang.GeneralGeneratedFrontierReceipt299.indices_exact (encode : α → Option Nat) (decode : Nat → β) (denote : α → β)
    (roundtrip : ∀ x i, encode x = some i → decode i = denote x)
    (children : List α) (row : List Nat) (hit : indices encode children = some row) :
    row.map decode = children.map denote
```

```lean
theorem Yulang.GeneralGeneratedFrontierReceipt299.row_exact (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (x : Nat) (row : Entry) (ok : readRows lookup encode x = some row) :
    ∃ children, lookup x = some (.selected row.key children) ∧
      indices encode children = some row.children
```

```lean
theorem Yulang.GeneralGeneratedFrontierReceipt299.faithful {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (decode : Nat → v.Demand) (denote : α → v.Demand)
    (observed : ∀ i f, lookup i = some f → Local b r s (decode i) (translate denote f))
    (roundtrip : ∀ x i, encode x = some i → decode i = denote x) :
    Faithful (b:=b) (r:=r) (s:=s) (readRows lookup encode) decode
```

```lean
theorem Yulang.GeneralGeneratedFrontierReceipt299.unindexed_not_rejected (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (x k : Nat) (children : List α) (seen : lookup x = some (.selected k children))
    (bad : indices encode children = none) :
    compile lookup encode x = .unindexed ∧ readRows lookup encode x = none
```


## lean/Yulang/GeneralGeneratedMixedCurrentNodes299.lean

```lean
theorem Yulang.GeneralGeneratedMixedCurrentNodes299.scoped_nodes (read : Read) (decode : Nat → Occurrence roles)
    (path : Reachable (boundary roles) registry root s)
    (faith : Faithful (b:=boundary roles) (r:=registry) (s:=s) read decode)
    (scope : InScope (boundary roles) registry s root read decode)
    (available : Providers registry s read decode) : Nodes (boundary roles) registry s read decode
```


## lean/Yulang/GeneralGeneratedMixedRooted299.lean

```lean
theorem Yulang.GeneralGeneratedMixedRooted299.child_generated (read : Read) (decode : Nat → Occurrence roles)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (inhabited : ∃ m, Models s m)
    (stable : ∀ x, (x = root ∨ (B roles).Generated registry s root x) → (B roles).Stable registry s x)
    (c x : Nat) (edge : Edge read c x)
    (reached : decode x = root ∨ (B roles).Generated registry s root (decode x)) :
    (B roles).Generated registry s root (decode c)
```

```lean
theorem Yulang.GeneralGeneratedMixedRooted299.along (read : Read) (decode : Nat → Occurrence roles)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (inhabited : ∃ m, Models s m)
    (stable : ∀ x, (x = root ∨ (B roles).Generated registry s root x) → (B roles).Stable registry s x)
    {c x : Nat} (down : Relation.TransGen (Edge read) c x) :
    (decode x = root ∨ (B roles).Generated registry s root (decode x)) →
    (B roles).Generated registry s root (decode c)
```

```lean
theorem Yulang.GeneralGeneratedMixedRooted299.scope_after_halt (read : Read) (decode : Nat → Occurrence roles) (i : Nat)
    (origin : decode i = root) (rooted : Rooted read i)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode) (inhabited : ∃ m, Models s m)
    (halted : ∀ next, ¬ (B roles).Step registry root s next) :
    InScope (B roles) registry s root read decode
```

```lean
theorem Yulang.GeneralGeneratedMixedRooted299.after_halt (read : Read) (decode : Nat → Occurrence roles) (i : Nat)
    (origin : decode i = root) (rooted : Rooted read i)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (halted : ∀ next, ¬ (B roles).Step registry root s next)
    (fuel : Nat) (payload : CommonRoleOutermostResolver.Dictionary)
    (runOk : run read fuel i = some payload) :
    Classify (B roles) registry s root (.selected payload) ∧
    ∀ m, Models s m → (B roles).Evidence registry s m root payload
```


## lean/Yulang/GeneralGeneratedRigidCompile299.lean

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.keys_exact (encode : Goal → Option Nat) (source : Nat → Option Goal)
    (roundtrip : ∀ g i, encode g = some i → source i = some g)
    (goals : List Goal) (indices : List Nat) (eq : keys encode goals = some indices) :
    indices.map source = goals.map some
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.row_exact (visible : List Impl) (source : Nat → Option Goal)
    (encode : Goal → Option Nat) (roundtrip : ∀ g i, encode g = some i → source i = some g)
    (i : Nat) (e : Entry) (read : fromGoals visible source encode i = some e) :
    ∃ goal chosen, source i = some goal ∧ candidates visible goal = [chosen] ∧
      chosen.key = e.key ∧ e.children.map source =
        (chosen.constraints.map (fun g => g.subst (matchingSubst chosen.head goal.args))).map some
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.roundtrip (g : Goal) (i : Nat) (seen : encode g = some i) :
    source i = some g
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.computed_table : fromGoals goodImpls source encode = table
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.missing_grandchild : fromGoals goodImpls source incomplete 1 = none
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.unfinished_is_no_result : run (fromGoals goodImpls source incomplete) 3 0 = none
```

```lean
theorem Yulang.GeneralGeneratedRigidCompile299.matches_elaboration :
    ∃ plan, RoleDictionaries.elaborate goodImpls goodImpls_wellFormed (decode 0) = .resolved plan ∧
      run (fromGoals goodImpls source encode) 3 0 = some (eraseKeys plan)
```


## lean/Yulang/GeneralGeneratedRigidNested299.lean

```lean
theorem Yulang.GeneralGeneratedRigidNested299.rows (i : Nat) (e : Entry) (hit : table i = some e) :
    (i = 0 ∧ e = ⟨listImpl.key,[1]⟩) ∨
    (i = 1 ∧ e = ⟨listImpl.key,[2]⟩) ∨
    (i = 2 ∧ e = ⟨intImpl.key,[]⟩)
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.faithful (i : Nat) (e : Entry) (hit : table i = some e) :
    localImpl i e.key e.children
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.ranked : Ranked table rank
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.closed : Closed table
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.full_nested :
    ∃ plan, elaborate goodImpls goodImpls_wellFormed (decode 0) = .resolved plan ∧
      run table 3 0 = some (eraseKeys plan)
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.computed_nested :
    run table 3 0 = some (.node listImpl.key [.node listImpl.key [.node intImpl.key []]])
```

```lean
theorem Yulang.GeneralGeneratedRigidNested299.short_budget : run table 2 0 = none
```


## lean/Yulang/GeneralGeneratedSelectedExact299.lean

```lean
theorem Yulang.GeneralGeneratedSelectedExact299.derivation_accessible (d : Dictionary) (focus : v.Demand)
    (derived : Classify b r s focus (.selected d)) :
    Acc (Child (Local b r s)) focus
```

```lean
theorem Yulang.GeneralGeneratedSelectedExact299.children_accessible (ds : List Dictionary) (cs : List v.Demand)
    (derived : All₂ (fun c d => Classify b r s c (.selected d)) cs ds)
    (child : v.Demand) (mem : child ∈ cs) :
    Acc (Child (Local b r s)) child
```

```lean
theorem Yulang.GeneralGeneratedSelectedExact299.bounded_exact (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) (d : Dictionary) :
    run read domain.length i = some d ↔ Classify b r s (decode i) (.selected d)
```

```lean
theorem Yulang.GeneralGeneratedSelectedExact299.no_result_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    run read domain.length i = none ↔
      ¬ ∃ d, Classify b r s (decode i) (.selected d)
```


## lean/Yulang/GeneralGeneratedSemanticAcc299.lean

```lean
theorem Yulang.GeneralGeneratedSemanticAcc299.source_child_exact (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (i : Nat) (row : Entry) (hit : read i = some row) (d : v.Demand) :
    Child (Local b r s) d (decode i) ↔ d ∈ row.children.map decode
```

```lean
theorem Yulang.GeneralGeneratedSemanticAcc299.semantic_accessible (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (n i : Nat) (d : Dictionary) (out : run read n i = some d) :
    Acc (Child (Local b r s)) (decode i)
```

```lean
theorem Yulang.GeneralGeneratedSemanticAcc299.semantic_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode) (closed : Closed read)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    (∃ n d, run read n i = some d) ↔ Acc (Child (Local b r s)) (decode i)
```

```lean
theorem Yulang.GeneralGeneratedSemanticAcc299.bounded_semantic_iff (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (closed : Closed read) (domain : List Nat) (known : Known read domain)
    (i : Nat) {row : Entry} (hit : read i = some row) :
    (∃ d, run read domain.length i = some d) ↔ Acc (Child (Local b r s)) (decode i)
```

Indexed 173 theorem declarations. Each has one standalone audit.
