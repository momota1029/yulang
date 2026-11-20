# Cycle 296: complete theorem / audit index

Exact Lean source signatures; Japanese summaries are in the cycle report.

## `lean/Yulang/GeneralSourceRoleCstCatalogAgreement296.lean`

```lean
theorem own_environment_fits (c : Catalog) (qs : List Query) :
    Fits c qs (environment c)
```

```lean
theorem fits_iff_reads_agree (c : Catalog) (qs : List Query) (e : Environment)
    (complete : Supported c qs) :
    Fits c qs e ↔ SameReplies (environment c) e qs
```

```lean
theorem supported_role_exact (c : Catalog) (r : Role) (e : Environment)
    (complete : Supported c (queryList (environment c) r)) :
    Fits c (queryList (environment c) r) e ↔ Agree (environment c) e r
```

```lean
theorem producer_trace_authority {c : Catalog} {r : Role} {t : Trace}
    (issued : produce c r = .ok t) (e : Environment) :
    Fits c (queryList (environment c) r) e ↔ capture e r = t
```

```lean
theorem queried_keys_stable {c : Catalog} {r : Role} {t : Trace}
    (issued : produce c r = .ok t) (e : Environment)
    (fits : Fits c (queryList (environment c) r) e) :
    queryList (environment c) r = queryList e r
```

## `lean/Yulang/GeneralSourceRoleCstCatalogControl296.lean`

```lean
theorem exact_finite_exports :
    run .selectedBranch 5 both 71 first (packet first) binder 2 = .ok ⟨binderTrace,parameterTable⟩ ∧
    run .selectedBranch 5 both 71 second (packet second) constructor 2 = .ok ⟨ctorTrace,charTable⟩
```

```lean
theorem unobserved_and_explicit_absence_differ :
    run .selectedBranch 5 both 71 first (packet first) justRole 2 =
      .error (.evidence (.missing (.output 2 "value"))) ∧
    run .selectedBranch 5 both 71 first (packet first) absentOutput 2 = .error .oldExport
```

```lean
theorem duplicate_and_conflicting_rows_rejected :
    run .selectedBranch 5 both 71 first (packet first) conflicting 2 =
      .error (.evidence (.ambiguous (.output 2 "value"))) ∧
    run .selectedBranch 5 both 71 first (packet first) duplicated 2 =
      .error (.evidence (.ambiguous (.output 2 "value")))
```

```lean
theorem footprint_is_local :
    run .selectedBranch 5 both 71 first (packet first) irrelevant 2 = .ok ⟨binderTrace,parameterTable⟩ ∧
    run .selectedBranch 5 both 71 second (packet second) binder 2 =
      .error (.evidence (.missing (.constructor "char")))
```

```lean
theorem cannot_retarget_catalog_export :
    run .selectedBranch 5 both 71 second (packet first) constructor 2 = .error .selection
```

## `lean/Yulang/GeneralSourceRoleCstCatalogEntry296.lean`

```lean
theorem value_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : Json) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    fromValue fuel source names policy scope brand selected sealed fallback = .ok out ↔
      ∃ w c, source = encode w ∧ depth w ≤ fuel ∧ names = encodeCatalog c ∧
        run policy scope w brand selected sealed c fallback = .ok out
```

```lean
theorem text_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : String) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    fromText fuel source names policy scope brand selected sealed fallback = .ok out ↔
      ∃ s n w c, Json.parse source = .ok s ∧ Json.parse names = .ok n ∧
        s = encode w ∧ depth w ≤ fuel ∧ n = encodeCatalog c ∧
        run policy scope w brand selected sealed c fallback = .ok out
```

## `lean/Yulang/GeneralSourceRoleCstCatalogExport296.lean`

```lean
theorem run_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported) :
    run policy scope w brand a sealed c fallback = .ok out ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        produce c r.role = .ok out.trace ∧
        runTracked (fun _ => environment c) fallback [p] = some out.table
```

```lean
theorem evidence_failure_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (why : Issue) :
    run policy scope w brand a sealed c fallback = .error (.evidence why) ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        produce c r.role = .error why
```

## `lean/Yulang/GeneralSourceRoleCstCatalogFailure296.lean`

```lean
theorem fails_at_prefix (c : Catalog) (pre rest : List Query) (q : Query) (why : Issue)
    (earlier : Supported c pre) (bad : Bad c q why) :
    requireAll c (pre ++ q::rest) = .error why
```

```lean
theorem first_failure (c : Catalog) (qs : List Query) (why : Issue) :
    requireAll c qs = .error why ↔ ∃ pre q rest, qs = pre ++ q::rest ∧
      Supported c pre ∧ Bad c q why
```

## `lean/Yulang/GeneralSourceRoleCstCatalogFootprint296.lean`

```lean
theorem produced_member_exact (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) :
    (q,v) ∈ t ↔ q ∈ queryList (environment c) r ∧ lookup c q = .known v
```

```lean
theorem trace_does_not_invent_row (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) (entry : (q,v) ∈ t) :
    (q,v) ∈ c
```

```lean
theorem coalesced_footprint_exact (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) :
    (q,v) ∈ coalesce t ↔ q ∈ queryList (environment c) r ∧ lookup c q = .known v
```

## `lean/Yulang/GeneralSourceRoleCstCatalogOrder296.lean`

```lean
theorem fiber_perm {c d : Catalog} (h : c.Perm d) (q : Query) :
    (fiber c q).Perm (fiber d q)
```

```lean
theorem lookup_perm {c d : Catalog} (h : c.Perm d) (q : Query) :
    lookup c q = lookup d q
```

```lean
theorem require_congr_on_keys {c d : Catalog} (qs : List Query)
    (same : ∀ q ∈ qs, lookup c q = lookup d q) :
    requireAll c qs = requireAll d qs
```

```lean
theorem produce_local {c d : Catalog} (r : Role)
    (same : ∀ q ∈ queryList (environment c) r, lookup c q = lookup d q) :
    produce c r = produce d r
```

```lean
theorem run_local {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat)
    (same : ∀ p r, handoff policy scope w brand a sealed = some p → symbolic p = some r →
      ∀ q ∈ queryList (environment c) r.role, lookup c q = lookup d q) :
    run policy scope w brand a sealed c fallback = run policy scope w brand a sealed d fallback
```

```lean
theorem run_perm {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat) (same : c.Perm d) :
    run policy scope w brand a sealed c fallback = run policy scope w brand a sealed d fallback
```

## `lean/Yulang/GeneralSourceRoleCstCatalogQueryWire296.lean`

```lean
theorem fields_exact (xs : List Json) (q : Query) :
    decodeFields xs = some q ↔ xs = encodeFields q
```

```lean
theorem query_exact (j : Json) (q : Query) :
    decodeQuery j = some q ↔ j = encodeQuery q
```

## `lean/Yulang/GeneralSourceRoleCstCatalogReplay296.lean`

```lean
theorem agrees_replays {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat)
    (out : Exported) (built : run policy scope w brand a sealed c fallback = .ok out)
    (reference : S → Environment) :
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      (Fits c (queryList (environment c) r.role) (reference r.scope) ↔
        checked policy scope w brand a ⟨sealed,out.trace⟩ reference fallback = some out.table)
```

## `lean/Yulang/GeneralSourceRoleCstCatalogScalar296.lean`

```lean
theorem nat_exact (j : Json) (n : Nat) : decodeNat j = some n ↔ j = encodeNat n
```

```lean
theorem value_exact (j : Json) (v : Option Nat) :
    decodeValue j = some v ↔ j = encodeValue v
```

## `lean/Yulang/GeneralSourceRoleCstCatalogTrace296.lean`

```lean
theorem require_exact (c : Catalog) (qs : List Query) (tr : Trace) :
    requireAll c qs = .ok tr ↔ Supported c qs ∧ values (environment c) qs = tr
```

```lean
theorem produce_exact (c : Catalog) (r : Role) (tr : Trace) :
    produce c r = .ok tr ↔ Supported c (queryList (environment c) r) ∧
      capture (environment c) r = tr
```

## `lean/Yulang/GeneralSourceRoleCstCatalogWire296.lean`

```lean
theorem row_fields_exact (xs : List Json) (p : Row) :
    decodeRowFields xs = some p ↔ xs = [encodeQuery p.1,encodeValue p.2]
```

```lean
theorem row_exact (j : Json) (p : Row) : decodeRow j = some p ↔ j = encodeRow p
```

```lean
theorem aligned_rows_exact (js : List Json) (c : Catalog) :
    Aligned (fun j p => j = encodeRow p) js c ↔ js = c.map encodeRow
```

```lean
theorem rows_exact (js : List Json) (c : Catalog) :
    collect decodeRow js = some c ↔ js = c.map encodeRow
```

```lean
theorem catalog_fields_exact (js : List Json) (c : Catalog) :
    decodeCatalogFields js = some c ↔ js = [.str schema,.arr (c.map encodeRow).toArray]
```

```lean
theorem catalog_exact (j : Json) (c : Catalog) :
    decodeCatalog j = some c ↔ j = encodeCatalog c
```

## `lean/Yulang/GeneralSourceRoleCstCoalesce296.lean`

```lean
theorem coalesce_mem (t : Trace) (p : Query × Option Nat) : p ∈ coalesce t ↔ p ∈ t
```

```lean
theorem coalesce_nodup (t : Trace) : (coalesce t).Nodup
```

```lean
theorem fiber_empty_of_no_pair (c : Catalog) (q : Query)
    (absent : ∀ v, (q,v) ∉ c) : fiber c q = []
```

```lean
theorem singleton_fiber (c : Catalog) (q : Query) (v : Option Nat)
    (uniqueRows : c.Nodup) (seen : (q,v) ∈ c)
    (oneValue : ∀ x, (q,x) ∈ c → x = v) :
    fiber c q = [v]
```

## `lean/Yulang/GeneralSourceRoleCstIssueControl296.lean`

```lean
theorem issued_contains_only_demanded_rows :
    issue .selectedBranch 5 both 71 first (41 : Nat) (packet first) irrelevant 2 = .ok issued
```

```lean
theorem replay_binds_scope_revision_and_fallback :
    accept issued.packet both 5 71 first .selectedBranch 41 (packet first) 2 =
      .ok issued.exportResult ∧
    accept issued.packet both 5 71 first .selectedBranch 42 (packet first) 2 =
      .error .mismatchedScope ∧
    accept issued.packet both 5 71 first .selectedBranch 41 (packet first) 3 =
      .error .mismatchedScope ∧
    accept issued.packet both 5 71 second .selectedBranch 41 (packet second) 2 =
      .error .mismatchedScope
```

```lean
theorem issue_does_not_clear_fresh_recovery_gate :
    accept issued.packet both 5 71 first .selectedBranch 41 noDiagnosticObservation 2 =
      .error (.selected .selection)
```

## `lean/Yulang/GeneralSourceRoleCstIssuePacket296.lean`

```lean
theorem issue_exact {S B R : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (epoch : R) (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Issued S B R) :
    issue policy scope w brand a epoch sealed c fallback = .ok out ↔
      run policy scope w brand a sealed c fallback = .ok out.exportResult ∧
      out.packet = ⟨w,scope,a,policy,epoch,fallback,coalesce out.exportResult.trace⟩
```

```lean
theorem issued_replays_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (epoch : R) (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Issued S B R)
    (ready : issue policy scope w brand a epoch sealed c fallback = .ok out) :
    accept out.packet w scope brand a policy epoch sealed fallback = .ok out.exportResult ∧
      (∀ row ∈ out.packet.catalog, row ∈ c)
```

## `lean/Yulang/GeneralSourceRoleCstIssuedScope296.lean`

```lean
theorem checks_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (a : Address B) (policy : Policy) (rev : R) (fallback : Nat) :
    checks p w scope a policy rev fallback = true ↔ p.retained = w ∧ p.scope = scope ∧
      p.selected = a ∧ p.policy = policy ∧ p.revision = rev ∧ p.fallbackArity = fallback
```

```lean
theorem accept_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (brand : B) (a : Address B) (policy : Policy)
    (rev : R) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    accept p w scope brand a policy rev sealed fallback = .ok out ↔
      checks p w scope a policy rev fallback = true ∧ run policy scope w brand a sealed p.catalog fallback = .ok out
```

```lean
theorem changed_revision_rejected {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (brand : B) (a : Address B) (policy : Policy)
    (rev : R) (sealed : Boundary S B) (fallback : Nat) (h : p.revision ≠ rev) :
    accept p w scope brand a policy rev sealed fallback = .error .mismatchedScope
```

## `lean/Yulang/GeneralSourceRoleCstKnownOnSuccess296.lean`

```lean
theorem resolved_body_keys_found {e : Environment} {xs : List String} {b : Body}
    {v : Option Roles.Term} (h : ResolvedBody e xs b v) : FoundAll e (bodyQueries b)
```

```lean
theorem resolved_output_keys_found {e : Environment} {xs : List String}
    {r : Nat} {o : Output} {field : Nat × Option Roles.Term}
    (h : OutputWitness e r xs o field) : FoundAll e (outputQueries e r o)
```

```lean
theorem lowered_role_keys_found {e : Environment} {r : Role} {row : BareRow}
    (h : RowWitness e r row) : FoundAll e (queryList e r)
```

```lean
theorem success_has_no_absent_replies {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (wire : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (ok : run policy scope wire brand a sealed c fallback = .ok out)
    (q : Query) (v : Option Nat) (member : (q,v) ∈ out.trace) : ∃ n, v = some n
```

## `lean/Yulang/GeneralSourceRoleCstMinimalCatalog296.lean`

```lean
theorem coalesce_preserves_unique (t : Trace) (unique : t.Nodup) : coalesce t = t
```

```lean
theorem coalesce_idempotent (t : Trace) : coalesce (coalesce t) = coalesce t
```

```lean
theorem least_among_same_selected_table {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (bound : Boundary S B) (c d : Catalog) (fallback : Nat) (out other : Exported)
    (first : run policy scope w brand a bound c fallback = .ok out)
    (second : run policy scope w brand a bound d fallback = .ok other)
    (same : out.table = other.table) :
    ∀ row ∈ coalesce out.trace, row ∈ d
```

## `lean/Yulang/GeneralSourceRoleCstNameCatalog296.lean`

```lean
theorem known_exact (c : Catalog) (q : Query) (v : Option Nat) :
    lookup c q = .known v ↔ fiber c q = [v]
```

```lean
theorem empty_exact (c : Catalog) (q : Query) :
    lookup c q = .unobserved ↔ fiber c q = []
```

```lean
theorem ambiguous_exact (c : Catalog) (q : Query) :
    lookup c q = .ambiguous ↔ 2 ≤ (fiber c q).length
```

```lean
theorem reply_from_catalog (c : Catalog) (q : Query) :
    reply (environment c) q = provisional c q
```

```lean
theorem known_reply (c : Catalog) (q : Query) (v : Option Nat)
    (h : lookup c q = .known v) : reply (environment c) q = v
```

```lean
theorem member_of_fiber (c : Catalog) (q : Query) (v : Option Nat) :
    v ∈ fiber c q ↔ (q,v) ∈ c
```

## `lean/Yulang/GeneralSourceRoleCstRecoveredCatalog296.lean`

```lean
theorem captured_key_known (e : Environment) (r : Role) (q : Query)
    (read : q ∈ queryList e r) : lookup (coalesce (capture e r)) q = .known (reply e q)
```

```lean
theorem catalog_releases_exact_capture (e : Environment) (r : Role) :
    produce (coalesce (capture e r)) r = .ok (capture e r)
```

```lean
theorem recover_catalog_exact (r : Role) (row : BareRow) (c : Catalog) :
    recoverCatalog r row = some c ↔
      ∃ t, recover r row = some t ∧ c = coalesce t ∧ produce c r = .ok t
```

```lean
theorem inverted_from_lowered {e : Environment} {r : Role} {row : BareRow}
    (lowered : resolveRole e r = some row) :
    recoverCatalog r row = some (coalesce (capture e r))
```

```lean
theorem recovered_catalog_relowers {r : Role} {row : BareRow} {c : Catalog}
    (evidence : recoverCatalog r row = some c) :
    resolveRole (environment c) r = some row
```

## `lean/Yulang/GeneralSourceRoleCstRecoveredControl296.lean`

```lean
theorem repeated_queries_share_unique_catalog_observation :
    recoverCatalog repeatedChar compatibleRow = some compactCatalog ∧
    produce compactCatalog repeatedChar = .ok fullOccurrenceTrace ∧
    lookup compactCatalog (.constructor "char") = .known (some 3)
```

```lean
theorem contradictory_recovered_ids_refused :
    (recover repeatedChar conflictingRow).isSome = true ∧
    recoverCatalog repeatedChar conflictingRow = none
```

```lean
theorem binder_must_match_actual_positional_index :
    recoverCatalog binderRole wronglyPlaced = none
```

```lean
theorem shape_does_not_authorize_numeric_ids :
    recoverCatalog binderRole ordinary = some [(.role "Index",some 2),(.output 2 "value",some 0)] ∧
    recoverCatalog binderRole alternate = some [(.role "Index",some 42),(.output 42 "value",some 17)]
```

```lean
theorem reports_first_failure_in_query_order :
    requireAll [(.role "X",some 1)] [.role "X",.output 1 "f",.constructor "char"] =
      .error (.missing (.output 1 "f"))
```

## `lean/Yulang/GeneralSourceRoleCstReifyBody296.lean`

```lean
theorem from_resolved {e : Environment} {xs : List String} {b : Body} {v : Option Roles.Term}
    (ok : ResolvedBody e xs b v) :
    bodyEvidence xs b v = some (values e (bodyQueries b))
```

```lean
theorem from_output {e : Environment} {r : Nat} {xs : List String} {o : Output}
    {field : Nat × Option Roles.Term} (h : OutputWitness e r xs o field) :
    fieldEvidence r xs o field = some (values e (outputQueries e r o))
```

```lean
theorem values_match (e : Environment) (qs : List Query) : Matches e (values e qs)
```

```lean
theorem matches_cons (e : Environment) (q : Query) (v : Option Nat) (t : Trace) :
    Matches e ((q,v)::t) ↔ reply e q = v ∧ Matches e t
```

```lean
theorem body_replay {e : Environment} {xs : List String} {b : Body} {v : Option Roles.Term}
    {t : Trace} (decoded : bodyEvidence xs b v = some t) (known : Matches e t) :
    ResolvedBody e xs b v
```

```lean
theorem field_replay {e : Environment} {r : Nat} {xs : List String} {o : Output}
    {field : Nat × Option Roles.Term} {t : Trace}
    (decoded : fieldEvidence r xs o field = some t) (known : Matches e t) :
    OutputWitness e r xs o field
```

## `lean/Yulang/GeneralSourceRoleCstReifyRow296.lean`

```lean
theorem fields_from_aligned {e : Environment} {r : Nat} {xs : List String}
    {os : List Output} {fs : List (Nat × Option Roles.Term)}
    (ok : Aligned (OutputWitness e r xs) os fs) :
    fields r xs os fs = some (values e (os.flatMap (outputQueries e r)))
```

```lean
theorem fields_replay {e : Environment} {r : Nat} {xs : List String}
    {os : List Output} {fs : List (Nat × Option Roles.Term)} {t : Trace}
    (got : fields r xs os fs = some t) (fits : Matches e t) :
    Aligned (OutputWitness e r xs) os fs
```

```lean
theorem recover_from_witness {e : Environment} {r : Role} {row : BareRow} (ok : RowWitness e r row) :
    recover r row = some (capture e r)
```

```lean
theorem recover_from_existing_lowerer {e : Environment} {r : Role} {row : BareRow}
    (ok : resolveRole e r = some row) :
    recover r row = some (capture e r)
```

```lean
theorem recover_replays {e : Environment} {r : Role} {row : BareRow} {t : Trace}
    (found : recover r row = some t) (fits : Matches e t) : resolveRole e r = some row
```

## `lean/Yulang/GeneralSourceRoleCstSelectedEvidence296.lean`

```lean
theorem selected_old_table_inverts {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (fallback : Nat) (table : RoleSource)
    (old : compile policy scope w brand a sealed env fallback = some table) :
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      extractCatalog policy scope w brand a sealed table = some (coalesce (capture (env r.scope) r.role))
```

```lean
theorem extracted_table_replays {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (table : RoleSource) (c : Catalog)
    (obtained : extractCatalog policy scope w brand a sealed table = some c) :
    ∃ t, run policy scope w brand a sealed c table.fallbackArity = .ok ⟨t,table⟩
```

```lean
theorem extract_after_finite_export {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (success : run policy scope w brand a sealed c fallback = .ok out) :
    extractCatalog policy scope w brand a sealed out.table = some (coalesce out.trace)
```

## `lean/Yulang/GeneralSourceRoleCstTableEvidence296.lean`

```lean
theorem from_table_exact {S H : Type} (p : Tracked S H) (tab : RoleSource) (c : Catalog) :
    fromTable p tab = some c ↔ Valid tab ∧ ∃ r row, symbolic p = some r ∧
      tab.rows = [row] ∧ recoverCatalog r.role (forgetRow row) = some c
```

```lean
theorem actual_table_inverts {S H : Type} (env : S → Environment) (fallback : Nat)
    (p : Tracked S H) (tab : RoleSource) (done : runTracked env fallback [p] = some tab) :
    ∃ r, symbolic p = some r ∧
      fromTable p tab = some (GeneralSourceRoleCstCoalesce296.coalesce (capture (env r.scope) r.role))
```

```lean
theorem table_replays {S H : Type} (p : Tracked S H) (tab : RoleSource) (c : Catalog)
    (made : fromTable p tab = some c) :
    ∃ r trace, symbolic p = some r ∧
      GeneralSourceRoleCstCatalogTrace296.produce c r.role = .ok trace ∧
      runTracked (fun _ => environment c) tab.fallbackArity [p] = some tab
```

## `lean/Yulang/GeneralSourceRoleCstTrackedRow296.lean`

```lean
theorem tracked_row_exact {S H : Type} (env : S → Environment) (f : Nat)
    (p : Tracked S H) (tab : RoleSource) :
    runTracked env f [p] = some tab ↔ ∃ r row, symbolic p = some r ∧
      tab.rows = [row] ∧ tab.fallbackArity = f ∧ Valid tab ∧
      resolveRole (env r.scope) r.role = some (forgetRow row)
```

## `lean/Yulang/GeneralSourceRoleCstTrimCatalog296.lean`

```lean
theorem trim_preserves_full_export {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (success : run policy scope w brand a sealed c fallback = .ok out) :
    run policy scope w brand a sealed (coalesce out.trace) fallback = .ok out ∧
      ∀ row ∈ coalesce out.trace, row ∈ c
```

```lean
theorem selected_table_determines_trace {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat) (out other : Exported)
    (first : run policy scope w brand a sealed c fallback = .ok out)
    (second : run policy scope w brand a sealed d fallback = .ok other)
    (same : out.table = other.table) : out.trace = other.trace
```

Indexed 93 theorem declarations; every one appears in exactly one standalone audit.
