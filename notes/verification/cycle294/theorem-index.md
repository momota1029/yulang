# Cycle 294: complete theorem / audit index

Exact Lean source signatures; Japanese summaries are in the cycle report.

## `lean/Yulang/GeneralSourceRoleCstAttestedGate294.lean`

```lean
theorem checked_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (address : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) :
    checked policy scope s address packet = some out ↔
      permits policy s.brand address.path packet = true ∧
      allows policy s.root address.path = true ∧ exportAt scope s address = some out
```

```lean
theorem whole_attached_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) (authoritative : List Diagnostic)
    (attached : packet = .reported s.brand authoritative) :
    checked .whole scope s a packet = some out ↔
      authoritative = [] ∧ TreePlain s.root ∧ exportAt scope s a = some out
```

```lean
theorem branch_attached_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (packet : Scan Brand)
    (out : Tracked Scope (Address Brand)) (authoritative : List Diagnostic)
    (attached : packet = .reported s.brand authoritative) :
    checked .selectedBranch scope s a packet = some out ↔
      (∀ d ∈ authoritative, IndependentPermission .selectedBranch a.path d) ∧
      BranchPlain s.root a.path ∧ exportAt scope s a = some out
```

```lean
theorem checked_cannot_create_projection {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (scan : Scan Brand)
    (out : Tracked Scope (Address Brand)) (done : checked policy scope s a scan = some out) :
    exportAt scope s a = some out
```

## `lean/Yulang/GeneralSourceRoleCstBindingControl294.lean`

```lean
theorem final_newline_compacts_same (pre : List Wire) :
    decodeList (pre ++ [.token "Newline" "\n"]) =
      decodeList (pre ++ [.token "Whitespace" "\n"])
```

```lean
theorem root_tail_kind_collision (pre : List Wire) :
    decode (.node "Root" (pre ++ [.token "Newline" "\n"])) =
      decode (.node "Root" (pre ++ [.token "Whitespace" "\n"])) ∧
    same (.node "Root" (pre ++ [.token "Newline" "\n"]))
      (.node "Root" (pre ++ [.token "Whitespace" "\n"])) = false
```

## `lean/Yulang/GeneralSourceRoleCstBoundOwners294.lean`

```lean
theorem owner_exists_exact (root : Tree) (d : Diagnostic) : ownerExists root d = true ↔
    ∃ p node, d.owner = some p ∧ follow p root = some node
```

```lean
theorem grounded_exact (policy : Policy) (root : Tree) (selected : Path) (d : Diagnostic) :
    grounded policy root selected d = true ↔ IndependentPermission policy selected d ∧
    ∃ p node, d.owner = some p ∧ follow p root = some node
```

```lean
theorem packet_exact {Brand : Type} [DecidableEq Brand] (policy : Policy)
    (s : Snapshot Brand) (selected : Path) (scan : Scan Brand) :
    packetOK policy s selected scan = true ↔
      ∃ ds, scan = .reported s.brand ds ∧ ∀ d ∈ ds,
        IndependentPermission policy selected d ∧
        ∃ p node, d.owner = some p ∧ follow p s.root = some node
```

```lean
theorem checked_bound_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (scan : Scan Brand)
    (out : Tracked Scope (Address Brand)) :
    checkedBound policy scope s a scan = some out ↔
      packetOK policy s a.path scan = true ∧ allows policy s.root a.path = true ∧
      exportAt scope s a = some out
```

```lean
theorem implies_independent_packet {Brand : Type} [DecidableEq Brand] (policy : Policy)
    (s : Snapshot Brand) (wanted : Path) (scan : Scan Brand)
    (ok : packetOK policy s wanted scan = true) :
    GeneralSourceRoleCstDiagnostics294.permits policy s.brand wanted scan = true
```

## `lean/Yulang/GeneralSourceRoleCstCleanBoundary294.lean`

```lean
theorem projected_selects_plain {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    ∃ selected, follow a.path s.root = some selected ∧ TreePlain selected
```

```lean
theorem projected_no_selected_marks {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    ∀ p k, (p,k) ∈ marks s.root → classify a.path p ≠ .selected
```

```lean
theorem branch_iff_ancestor_given_projection {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (projected : exportAt scope s a = some out) :
    allows .selectedBranch s.root a.path = true ↔ AncestorClear s.root a.path
```

```lean
theorem exact_corridor {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    guarded .selectedBranch scope s a = some out ↔
      exportAt scope s a = some out ∧ AncestorClear s.root a.path
```

## `lean/Yulang/GeneralSourceRoleCstCleanMembers294.lean`

```lean
theorem each_clean (xs : List Tree) :
    cleanList xs = true ↔ ∀ t ∈ xs, cleanTree t = true
```

```lean
theorem trivia_clean {t : Tree} (isTrivia : trivia t = true) : cleanTree t = true
```

```lean
theorem clean_full_from_visible (cs : List Tree) (h : cleanList (visible cs) = true) :
    cleanList cs = true
```

```lean
theorem node_if_clean (k : Kind) (cs : List Tree) (valid : Plain k)
    (h : cleanList (visible cs) = true) : cleanTree (.node k cs) = true
```

```lean
theorem rhs_clean {t : Tree} {v : GeneralSourceRoleSyntaxBoundary292.Rhs}
    (allowed : IsRhs t v) : cleanTree t = true
```

```lean
theorem declaration_clean {t : Tree} {s : GeneralSourceRoleSyntaxBoundary292.Shape}
    (allowed : IsType t s) : cleanTree t = true
```

```lean
theorem class_clean {t : Tree} {child : GeneralSourceRoleChildCoverage292.Child}
    (h : Classification t child) : cleanTree t = true
```

```lean
theorem statement_clean {site : List Nat} {t : Tree}
    {out : List Nat × GeneralSourceRoleChildCoverage292.Child}
    (allowed : IsStatement site t out) : cleanTree t = true
```

## `lean/Yulang/GeneralSourceRoleCstCleanProducer294.lean`

```lean
theorem argument_clean {t : Tree} {name : String}
    (h : ActualArgument t name) : cleanTree t = true
```

```lean
theorem head_clean {t : Tree} {name : String} {ps : List String}
    (h : ActualHead t name ps) : cleanTree t = true
```

```lean
theorem body_clean (base : Path) (cs : List Tree) (outs : List (Path × Child))
    (paired : Aligned (fun p => IsStatement (base ++ [p.1]) p.2) (significant cs) outs) :
    cleanTree (.node .indented cs) = true
```

```lean
theorem reinsert_prefix (cs : List (Nat × Tree))
    (proper : cleanList ((dropVisibility cs).map Prod.snd) = true) :
    cleanList (cs.map Prod.snd) = true
```

```lean
theorem role_clean {x head body : Tree} {i : Nat} (shape : roleParts x = some (head,i,body))
    (headOK : cleanTree head = true) (bodyOK : cleanTree body = true) : cleanTree x = true
```

```lean
theorem accepted_subtree_is_plain {Scope : Type} (scope : Scope) (site : Path) (x : Tree)
    (out : Tracked Scope Path) (success : extract scope site x = some out) :
    TreePlain x
```

## `lean/Yulang/GeneralSourceRoleCstDiagnosticFixture294.lean`

```lean
theorem mark_free_not_enough_for_diagnostic_admission :
    allows .whole ordinaryHeader.root site.path = true ∧
    (checked .whole () ordinaryHeader site cleanPacket).isSome = true ∧
    checked .whole () ordinaryHeader site withConflict = none
```

```lean
theorem selected_can_use_only_independent_unrelated_ownership :
    (checked .selectedBranch () ordinaryHeader site withConflict).isSome = true ∧
    checked .selectedBranch () ordinaryHeader site unknownSite = none
```

```lean
theorem absent_failed_foreign_distinct_from_success :
    checked .whole () ordinaryHeader site (.absent : Scan Nat) = none ∧
    checked .whole () ordinaryHeader site (.failed : Scan Nat) = none ∧
    checked .whole () ordinaryHeader site (.reported 11 []) = none ∧
    (checked .whole () ordinaryHeader site (.reported 10 [])).isSome = true
```

```lean
theorem same_wire_cannot_compute_attached_affected_scope :
    ¬ ∃ fromWire : Snapshot Nat → Bool,
        fromWire ordinaryHeader = (checked .whole () ordinaryHeader site cleanPacket).isSome ∧
        fromWire ordinaryHeader = (checked .whole () ordinaryHeader site withConflict).isSome
```

## `lean/Yulang/GeneralSourceRoleCstDiagnostics294.lean`

```lean
theorem permitted_exact (what : Policy) (selected : Path) (d : Diagnostic) :
    permitted what selected d = true ↔ IndependentPermission what selected d
```

```lean
theorem permits_exact {Brand : Type} [DecidableEq Brand] (what : Policy) (brand : Brand)
    (selected : Path) (scan : Scan Brand) : permits what brand selected scan = true ↔
       ∃ ds, scan = .reported brand ds ∧ ∀ d ∈ ds, IndependentPermission what selected d
```

```lean
theorem whole_report_exact {Brand : Type} [DecidableEq Brand] (brand : Brand)
    (selected : Path) (scan : Scan Brand) :
    permits .whole brand selected scan = true ↔ scan = .reported brand []
```

```lean
theorem unlocated_blocks_selected (selected : Path) (d : Diagnostic) (unknown : d.owner = none) :
    permitted .selectedBranch selected d = false
```

## `lean/Yulang/GeneralSourceRoleCstEqualSpans294.lean`

```lean
theorem equal_width_decode : decode equalWidthWire = some equalWidthTree
```

```lean
theorem equal_width_marks_both_retained :
    (original equalWidthWire equalWidthTree).map (fun o => o.occurrence.path) =
      [[1],[2],[3]] ∧
    (original equalWidthWire equalWidthTree).map (fun o => o.occurrence.extent) =
      [⟨3,3⟩,⟨3,3⟩,⟨3,6⟩] ∧
    (original equalWidthWire equalWidthTree).map (fun o => (o.originalTag,o.originalMode)) =
      [("Missing",.node),("Unknown",.token),("Error",.token)]
```

```lean
theorem zero_width_non_error_not_anchored :
    unique equalWidthWire equalWidthTree ⟨3,3⟩ = none ∧
    check equalWidthWire ⟨3,6⟩ [0] = true ∧
    check equalWidthWire ⟨3,6⟩ [3] = false
```

## `lean/Yulang/GeneralSourceRoleCstErrorRuns294.lean`

```lean
theorem split_exact (p parent : Path) (i : Nat) :
    splitLast p = some (parent,i) ↔ p = parent ++ [i]
```

```lean
theorem bridge_exact (a b : Origin) : bridge a b = true ↔ Neighbors a b
```

```lean
theorem runs_flatten (origins : List Origin) : (runs origins).flatten = origins
```

```lean
theorem every_run (origins row : List Origin) (picked : row ∈ runs origins) : TokenRun row
```

## `lean/Yulang/GeneralSourceRoleCstGroupAnchor294.lean`

```lean
theorem unique_exact (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin) :
    unique wire tree r = some row ↔ candidates wire tree r = [row]
```

```lean
theorem candidate_exact (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin) :
    row ∈ candidates wire tree r ↔
      row ∈ runs (original wire tree) ∧ extent row = some r ∧
      ∀ o ∈ row, o.originalTag = "Error" ∧ o.originalMode = .token
```

```lean
theorem unique_has_run (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin)
    (chosen : unique wire tree r = some row) : TokenRun row ∧ extent row = some r
```

```lean
theorem origin_for_each {wire : Wire} {tree : Tree} (mapping : Transfer wire tree)
    {range : Extent} {row : List Origin} (picked : unique wire tree range = some row)
    {o : Origin} (h : o ∈ row) :
    ∃ text, GeneralSourceRoleCstWirePaths293.atWire o.occurrence.path wire =
      some (.token "Error" text)
```

```lean
theorem outside_exact (s : Path) (row : List Origin) :
    outside s row = true ↔ ∀ item ∈ row,
      ¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s
```

## `lean/Yulang/GeneralSourceRoleCstGroupFixture294.lean`

```lean
theorem ambiguous_has_two_runs :
    decode twoRuns = some twoTrees ∧ (candidates twoRuns twoTrees ⟨0,0⟩).length = 2
```

```lean
theorem ambiguous_extent_refused : unique twoRuns twoTrees ⟨0,0⟩ = none
```

```lean
theorem unavailable_range_refused : unique twoRuns twoTrees ⟨0,1⟩ = none
```

## `lean/Yulang/GeneralSourceRoleCstMarkFixture294.lean`

```lean
theorem clean_agreement :
    (run () clean ⟨10,[0]⟩).admitted .whole = some expected ∧
    (run () clean ⟨10,[0]⟩).admitted .selectedBranch = some expected
```

```lean
theorem unrelated_marks_survive_projection :
    (run () after ⟨10,[0]⟩).wholeWireMarkFree = false ∧
    (run () after ⟨10,[0]⟩).selectedBranchMarkFree = true ∧
    (run () after ⟨10,[0]⟩).admitted .whole = none ∧
    (run () after ⟨10,[0]⟩).admitted .selectedBranch = some expected ∧
    ((run () after ⟨10,[0]⟩).found.map Prod.fst) = [.unrelated,.unrelated]
```

```lean
theorem ancestor_really_blocks_selected_branch :
    (run () wrappedError ⟨10,[0,0]⟩).projected.isSome = true ∧
    ((run () wrappedError ⟨10,[0,0]⟩).found.map Prod.fst) = [.ancestor] ∧
    (run () wrappedError ⟨10,[0,0]⟩).admitted .selectedBranch = none
```

```lean
theorem no_marks_not_same_as_valid_address :
    (run () clean ⟨11,[0]⟩).wholeWireMarkFree = true ∧
    (run () clean ⟨11,[0]⟩).projected = none ∧
    (run () clean ⟨10,[5]⟩).admitted .selectedBranch = none
```

## `lean/Yulang/GeneralSourceRoleCstMarkPolicy294.lean`

```lean
theorem branch_exact (root : Tree) (s : Path) : branchClear root s = true ↔ BranchPlain root s
```

```lean
theorem whole_exact (root : Tree) (s : Path) : allows .whole root s = true ↔ TreePlain root
```

```lean
theorem whole_implies_branch (root : Tree) (s : Path) (ok : allows .whole root s = true) :
    allows .selectedBranch root s = true
```

```lean
theorem guarded_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    guarded policy scope s a = some out ↔
      allows policy s.root a.path = true ∧ exportAt scope s a = some out
```

```lean
theorem selected_gate_preserves_whole_success {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (strict : guarded .whole scope s a = some out) :
    guarded .selectedBranch scope s a = some out
```

## `lean/Yulang/GeneralSourceRoleCstMarkReport294.lean`

```lean
theorem entries_empty (root : Tree) : entries root = [] ↔ marks root = []
```

```lean
theorem entries_branch_exact (root : Tree) (s : Path) :
    ((entries root).all fun x => classify s x.path == .unrelated) = true ↔ BranchPlain root s
```

```lean
theorem listed_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (z : Zone) (e : Entry) :
    (z,e) ∈ (run scope s a).found ↔
      z = classify a.path e.path ∧
      ∃ node, GeneralSourceRoleCstSpan293.locate e.path s.root 0 = some (node,e.extent) ∧
        node.kind = e.kind ∧ ¬ Plain e.kind
```

```lean
theorem admission_preserved {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (policy : Policy) :
    (run scope s a).admitted policy = guarded policy scope s a
```

## `lean/Yulang/GeneralSourceRoleCstMarkScope294.lean`

```lean
theorem selected_exact (s p : Path) :
    classify s p = .selected ↔ ∃ tail, p = s ++ tail
```

```lean
theorem ancestor_exact (s p : Path) :
    classify s p = .ancestor ↔ (¬ s <+: p) ∧ p <+: s
```

```lean
theorem unrelated_exact (s p : Path) :
    classify s p = .unrelated ↔ (¬ s <+: p) ∧ ¬ p <+: s
```

```lean
theorem below_exact {r selected : Tree} {s : Path} (picked : follow s r = some selected)
    (tail : Path) (k : Kind) :
    (s ++ tail,k) ∈ marks r ↔ (tail,k) ∈ marks selected
```

```lean
theorem selected_plain_iff {r selected : Tree} {s : Path} (picked : follow s r = some selected) :
    TreePlain selected ↔ ∀ p k, (p,k) ∈ marks r → classify s p ≠ .selected
```

## `lean/Yulang/GeneralSourceRoleCstMarkSpans294.lean`

```lean
theorem reach_has_extent {root : Tree} {p : Path} {t : Tree}
    (h : follow p root = some t) :
    ∃ span, locate p root 0 = some (t,span)
```

```lean
theorem entry_exact (root : Tree) (e : Entry) :
    e ∈ entries root ↔
      ∃ node, locate e.path root 0 = some (node,e.extent) ∧
        node.kind = e.kind ∧ ¬ Plain e.kind
```

```lean
theorem mark_has_entry (root : Tree) (p : Path) (k : Kind)
    (here : (p,k) ∈ marks root) : ∃ e ∈ entries root, e.path = p ∧ e.kind = k
```

```lean
theorem entry_bounds (root : Tree) (e : Entry) (h : e ∈ entries root) :
    e.extent.low ≤ e.extent.high ∧ e.extent.high ≤ width root
```

## `lean/Yulang/GeneralSourceRoleCstMarkUnique294.lean`

```lean
theorem own_paths (k : Kind) : (paths (own k)).Nodup
```

```lean
theorem child_path_first (cs : List Tree) (base : Nat) (p : Path)
    (h : p ∈ paths (childMarks base cs)) :
    ∃ i tail, p = (base+i)::tail
```

```lean
theorem own_path_nil (k : Kind) (p : Path) (h : p ∈ paths (own k)) : p = []
```

```lean
theorem prepend_paths (ms : List (Path × Kind)) (n : Nat) :
    paths (ms.map (fun (p,k) => (n::p,k))) = (paths ms).map (List.cons n)
```

```lean
theorem marks_paths_nodup (root : Tree) : (paths (marks root)).Nodup
```

```lean
theorem child_paths_nodup (cs : List Tree) (base : Nat) : (paths (childMarks base cs)).Nodup
```

## `lean/Yulang/GeneralSourceRoleCstMarks294.lean`

```lean
theorem own_exact (k p : Kind) (loc : Path) :
    (loc,p) ∈ own k ↔ loc = [] ∧ p = k ∧ ¬ Plain k
```

```lean
theorem marks_exact (root : Tree) (p : Path) (k : Kind) :
    (p,k) ∈ marks root ↔ ∃ t, follow p root = some t ∧ t.kind = k ∧ ¬ Plain k
```

```lean
theorem child_marks_exact (cs : List Tree) (base : Nat) (p : Path) (k : Kind) :
    (p,k) ∈ childMarks base cs ↔
      ∃ i tail child, p = (base+i)::tail ∧ cs[i]? = some child ∧
        ∃ t, follow tail child = some t ∧ t.kind = k ∧ ¬ Plain k
```

```lean
theorem no_marks_exact (root : Tree) : marks root = [] ↔ TreePlain root
```

## `lean/Yulang/GeneralSourceRoleCstMaximalRuns294.lean`

```lean
theorem separation_cons (x a : Origin) (tail next : List Origin) :
    separated (x::a::tail) next ↔ separated (a::tail) next
```

```lean
theorem no_empty_run (input : List Origin) : [] ∉ runs input
```

```lean
theorem grouped_boundaries (input : List Origin) : MaximalBoundaries (runs input)
```

```lean
theorem adjacent_boundary {groups : List (List Origin)} (h : MaximalBoundaries groups)
    (before after : List (List Origin)) (a b : List Origin)
    (shape : groups = before ++ a::b::after) : separated a b
```

```lean
theorem no_bridge_across_runs (input : List Origin) (before after : List (List Origin))
    (a b : List Origin) (shape : runs input = before ++ a::b::after) :
    ∃ x y, a.getLast? = some x ∧ b.head? = some y ∧ ¬ Neighbors x y
```

## `lean/Yulang/GeneralSourceRoleCstMissingAmbiguity294.lean`

```lean
theorem no_extent_only_decider (w : Wire) (p : Path) (a b : MissingAnchor)
    (sameRange : a.span = b.span)
    (aVer : verified w a = true) (bVer : verified w b = true)
    (aBlocked : independentlyOutside w p a = false)
    (bOutside : independentlyOutside w p b = true) :
    ¬ ∃ guess : Extent → Bool, ∀ e, verified w e = true →
      guess e.span = independentlyOutside w p e
```

```lean
theorem select_path_allowed_iff (w : Wire) (p : Path) (item : MissingAnchor)
    (ok : verified w item = true) :
    independentlyOutside w p item = true ↔ ¬ p <+: item.path ∧ ¬ item.path <+: p
```

```lean
theorem missing_scope_needs_more_than_extent :
    ¬ ∃ guess : Extent → Bool, ∀ e, verified equalOffsets e = true →
      guess e.span = independentlyOutside equalOffsets [0] e
```

## `lean/Yulang/GeneralSourceRoleCstMissingReceipt294.lean`

```lean
theorem row_matches_exact (e : MissingAnchor) (o : Origin) : rowMatches e o = true ↔
    o.originalTag = "Missing" ∧ o.originalMode = .node ∧
      o.occurrence.path = e.path ∧ o.occurrence.extent = e.span
```

```lean
theorem verified_exact (wire : Wire) (e : MissingAnchor) :
    verified wire e = true ↔
    ∃ cs root o, wire = .node "Root" cs ∧ Transfer wire root ∧
      e.span.low = e.span.high ∧ visitPath e.path wire = true ∧
      o ∈ original wire root ∧ rowMatches e o = true
```

```lean
theorem verified_names_original_missing (wire : Wire) (e : MissingAnchor)
    (h : verified wire e = true) :
      ∃ body, GeneralSourceRoleCstWirePaths293.atWire e.path wire = some (.node "Missing" body)
```

```lean
theorem outside_exact (wire : Wire) (p : Path) (e : MissingAnchor) :
    independentlyOutside wire p e = true ↔ verified wire e = true ∧
      (¬ p <+: e.path) ∧ (¬ e.path <+: p)
```

## `lean/Yulang/GeneralSourceRoleCstMixedReceipt294.lean`

```lean
theorem acceptable_exact (policy : Policy) (wire : Wire) (root : Tree) (focus : Path)
    (e : Evidence) : acceptable policy wire root focus e = true ↔ e.Scoped policy wire root focus
```

```lean
theorem valid_exact {Brand : Type} [DecidableEq Brand] (policy : Policy) (wire : Wire)
    (s : Snapshot Brand) (focus : Path) (r : Receipt Brand) : valid policy wire s focus r = true ↔
      ∃ events, r = .reported s.brand events ∧ ∀ e ∈ events, e.Scoped policy wire s.root focus
```

```lean
theorem whole_valid_exact {Brand : Type} [DecidableEq Brand] (wire : Wire)
    (s : Snapshot Brand) (p : Path) (r : Receipt Brand) :
    valid .whole wire s p r = true ↔ r = .reported s.brand []
```

```lean
theorem export_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (wire : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand)) : exportChecked policy scope wire brand a r = some out ↔
      ∃ root events, Transfer wire root ∧ r = .reported brand events ∧
        (∀ e ∈ events, e.Scoped policy wire root a.path) ∧
        allows policy root a.path = true ∧ exportAt scope ⟨brand,root⟩ a = some out
```

## `lean/Yulang/GeneralSourceRoleCstOriginalMarks294.lean`

```lean
theorem decoded_label {w : Wire} {t : Tree} (matched : Transfer w t) :
    kind (tagAndMode w).1 = some t.kind
```

```lean
theorem original_exact (wire : Wire) (tree : Tree) (conversion : Transfer wire tree) (o : Origin) :
    o ∈ original wire tree ↔ ∃ raw node,
      atWire o.occurrence.path wire = some raw ∧
      GeneralSourceRoleCstSpan293.locate o.occurrence.path tree 0 = some (node,o.occurrence.extent) ∧
      Transfer raw node ∧ node.kind = o.occurrence.kind ∧ ¬ Plain node.kind ∧
      tagAndMode raw = (o.originalTag,o.originalMode)
```

```lean
theorem original_byte_width (wire : Wire) (tree : Tree) (conversion : Transfer wire tree) (o : Origin)
    (member : o ∈ original wire tree) :
    ∃ raw, atWire o.occurrence.path wire = some raw ∧
      o.occurrence.extent.high = o.occurrence.extent.low + (spelling raw).utf8ByteSize
```

## `lean/Yulang/GeneralSourceRoleCstPathFidelity294.lean`

```lean
theorem ordered_path_map {α β : Type} (read : α → Option β) (input : List α)
    (start : α → Path) (out : β → Path)
    (correct : ∀ a ∈ input, ∃ b, read a = some b ∧ out b = start a) :
    (input.filterMap read).map out = input.map start
```

```lean
theorem entries_same_paths (root : Tree) :
    (entries root).map Entry.path = paths (marks root)
```

```lean
theorem original_same_paths (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    (original wire tree).map (fun o => o.occurrence.path) = paths (marks tree)
```

```lean
theorem original_paths_nodup (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    ((original wire tree).map (fun o => o.occurrence.path)).Nodup
```

```lean
theorem original_count (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    (original wire tree).length = (marks tree).length
```

## `lean/Yulang/GeneralSourceRoleCstRangeReceipt294.lean`

```lean
theorem check_exact (wire : Wire) (range : Extent) (s : Path) :
    check wire range s = true ↔
      ∃ root row, Transfer wire root ∧ unique wire root range = some row ∧
        ∀ item ∈ row, ¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s
```

```lean
theorem checked_range_sound (wire : Wire) (range : Extent) (s : Path)
    (ok : check wire range s = true) :
    ∃ root row, Transfer wire root ∧
      unique wire root range = some row ∧
      ∀ item ∈ row,
        (¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s) ∧
        ∃ val, GeneralSourceRoleCstWirePaths293.atWire item.occurrence.path wire =
            some (.token "Error" val)
```

```lean
theorem prefix_only_cannot_validate_owner :
    (checked .selectedBranch () ordinaryHeader site ungroundedPacket).isSome = true ∧
    checkedBound .selectedBranch () ordinaryHeader site ungroundedPacket = none ∧
    (checkedBound .selectedBranch () ordinaryHeader site withConflict).isSome = true
```

```lean
theorem invalid_snapshot_refuses_range :
    check (.node "!not-a-tag" [.token "Error" "-"]) ⟨0,1⟩ [1] = false
```

```lean
theorem ambiguous_attachment_refuses_range : check twoRuns ⟨0,0⟩ [1] = false
```

## `lean/Yulang/GeneralSourceRoleCstReportWire294.lean`

```lean
theorem value_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (j : Json)
    (scope : Scope) (brand : Brand) (selected : Address Brand) (r : Report Scope Brand) :
    value fuel j scope brand selected = .ok r ↔
      ∃ wire root, encode wire = j ∧ depth wire ≤ fuel ∧ Transfer wire root ∧
        run scope ⟨brand,root⟩ selected = r
```

```lean
theorem input_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (text : String)
    (scope : Scope) (brand : Brand) (selected : Address Brand) (r : Report Scope Brand) :
    input fuel text scope brand selected = .ok r ↔
      ∃ j, Json.parse text = .ok j ∧ value fuel j scope brand selected = .ok r
```

## `lean/Yulang/GeneralSourceRoleCstRunControls294.lean`

```lean
theorem recorded_range_model :
    runs [a,b,c] = [[a,b,c]] ∧ extent [a,b,c] = some ⟨49,58⟩
```

```lean
theorem no_crossing_different_owner :
    bridge (tokenAt [0,1] 0 1) (tokenAt [2,2] 1 2) = false
```

```lean
theorem ordinal_gap_even_if_spans_touch :
    bridge (tokenAt [1] 0 1) (tokenAt [3] 1 2) = false
```

```lean
theorem byte_gap_even_if_ordinals_touch :
    bridge (tokenAt [1] 0 1) (tokenAt [2] 2 3) = false
```

```lean
theorem normalized_error_is_not_original_error_token :
    bridge a (tokenAt [2] 50 51 "Unknown") = false ∧
    bridge a {b with originalMode
```

## `lean/Yulang/GeneralSourceRoleCstRunExtent294.lean`

```lean
theorem cover {row : List Origin} (h : TokenRun row) :
    (∀ x ∈ row, x.occurrence.extent.low ≤ x.occurrence.extent.high) →
    ∃ e, extent row = some e ∧ e.high = e.low + (row.map size).sum
```

## `lean/Yulang/GeneralSourceRoleCstRunVisibility294.lean`

```lean
theorem visible_exact (p : Path) (w : Wire) : visible p w = true ↔ Visible p w
```

```lean
theorem visible_points_to_error {p : Path} {w : Wire} (h : Visible p w) :
    ∃ src, atWire p w = some (.token "Error" src) ∧ src.isEmpty = false
```

## `lean/Yulang/GeneralSourceRoleCstScopeRefine294.lean`

```lean
theorem unrelated_descends {p q m : Path} (step : p <+: q)
    (clear : (¬ p <+: m) ∧ ¬ m <+: p) : (¬ q <+: m) ∧ ¬ m <+: q
```

```lean
theorem branch_descends (root : Tree) {p q : Path} (step : p <+: q)
    (safe : branchClear root p = true) : branchClear root q = true
```

```lean
theorem visible_range_descends (w : Wire) (range : Extent) {p q : Path} (step : p <+: q)
    (pass : checkVisible w range p = true) : checkVisible w range q = true
```

```lean
theorem evidence_descends (w : Wire) (root : Tree) {p q : Path} (step : p <+: q)
    (e : Evidence) (safe : e.Scoped .selectedBranch w root p) :
    e.Scoped .selectedBranch w root q
```

```lean
theorem reported_scope_descends {Brand : Type} [DecidableEq Brand] (w : Wire)
    (s : Snapshot Brand) {p q : Path} (step : p <+: q) (packet : Receipt Brand)
    (ok : valid .selectedBranch w s p packet = true) :
    valid .selectedBranch w s q packet = true
```

## `lean/Yulang/GeneralSourceRoleCstStrictTransport294.lean`

```lean
theorem empty_receipt_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (out : Tracked Scope (Address Brand)) :
    project policy scope w brand a (.reported brand []) = some out ↔
      ∃ root, Transfer w root ∧ guarded policy scope ⟨brand,root⟩ a = some out
```

```lean
theorem whole_receipt_exact {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand)) :
    project .whole scope w brand a r = some out ↔ r = .reported brand [] ∧
      ∃ root, Transfer w root ∧ guarded .whole scope ⟨brand,root⟩ a = some out
```

```lean
theorem whole_to_selected {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand))
    (ok : project .whole scope w brand a r = some out) :
    project .selectedBranch scope w brand a r = some out
```

## `lean/Yulang/GeneralSourceRoleCstVisibleRange294.lean`

```lean
theorem visible_range_exact (wire : Wire) (r : Extent) (p : Path) :
    checkVisible wire r p = true ↔
      ∃ children root row, wire = .node "Root" children ∧ Transfer wire root ∧
        unique wire root r = some row ∧
        (∀ item ∈ row, (¬ p <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: p) ∧
          Visible item.occurrence.path wire)
```

```lean
theorem opacity_is_not_token_run : GeneralSourceRoleCstRangeReceipt294.check depthWrapped ⟨0,3⟩ [1] = true ∧
    checkVisible depthWrapped ⟨0,3⟩ [1] = false
```

```lean
theorem error_node_suppresses_direct_tokens :
    GeneralSourceRoleCstRangeReceipt294.check suppresses ⟨0,3⟩ [1] = true ∧
    checkVisible suppresses ⟨0,3⟩ [1] = false
```

```lean
theorem empty_token_is_not_a_rust_run :
    GeneralSourceRoleCstRangeReceipt294.check emptyToken ⟨0,0⟩ [1] = true ∧
    checkVisible emptyToken ⟨0,0⟩ [1] = false
```

## `lean/Yulang/GeneralSourceRoleCstVisibleReceipt294.lean`

```lean
theorem project_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (packet : Receipt Brand)
    (out : Tracked Scope (Address Brand)) :
    project policy scope w brand a packet = some out ↔
    exportChecked policy scope w brand a packet = some out ∧
      ∃ sender events, packet = .reported sender events ∧ ∀ range,
        .errorGroupRange range ∈ events → checkVisible w range a.path = true
```

## `lean/Yulang/GeneralSourceRoleCstWireBinding294.lean`

```lean
theorem same_exact (a b : Wire) : same a b = true ↔ a = b
```

```lean
theorem same_list_exact (cs ds : List Wire) : sameList cs ds = true ↔ cs = ds
```

```lean
theorem use_bound_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (retained : Wire) (brand : Brand) (a : Address Brand)
    (external : BoundReceipt Brand) (out : Tracked Scope (Address Brand)) :
    useBound policy scope retained brand a external = some out ↔
    external.fromWire = retained ∧ project policy scope retained brand a external.diagnostics = some out
```

```lean
theorem compact_equality_cannot_bind_wire :
    GeneralSourceRoleCstWire293.decode (.token "Unknown" "@") =
      GeneralSourceRoleCstWire293.decode (.token "Error" "@") ∧
    same (.token "Unknown" "@") (.token "Error" "@") = false
```

Indexed 140 theorem declarations; every one appears in exactly one standalone audit.
