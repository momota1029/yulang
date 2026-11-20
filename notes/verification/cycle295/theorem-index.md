# Cycle 295: complete theorem / audit index

Exact Lean source signatures; Japanese summaries are in the cycle report.

## `lean/Yulang/GeneralSourceRoleCstExactTags295.lean`

```lean
theorem compact_role_exact (n : String) : compact n = Kind.role ↔ n = "RoleDeclaration"
```

```lean
theorem compact_type_exact (n : String) : compact n = Kind.typeDecl ↔ n = "TypeDeclaration"
```

```lean
theorem compact_head_exact (n : String) : compact n = Kind.head ↔ n = "TypeExpression"
```

```lean
theorem exact_role_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .role cs)) :
    ∃ inner, w = .node "RoleDeclaration" inner
```

```lean
theorem exact_type_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .typeDecl cs)) :
    ∃ inner, w = .node "TypeDeclaration" inner
```

```lean
theorem exact_head_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .head cs)) :
    ∃ inner, w = .node "TypeExpression" inner
```

## `lean/Yulang/GeneralSourceRoleCstExplicitRead295.lean`

```lean
theorem selected_explicit_preserved {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (arity : Nat)
    (table : RoleSource) (_ : compile policy scope w brand a sealed env arity = some table)
    (impls : AssocEnv) (wf : WellFormed impls.cores) (goal : Goal) (name : Nat)
    (done : resolve impls.cores wf goal = .resolved) (impl : AssocImpl)
    (member : impl ∈ impls.impls) (unique : candidates impls.cores goal = [impl.impl])
    (rhs : Term) (explicit : impl.assoc.lookup name = some rhs) :
    assocOf impls (roleTable table) wf goal name =
      some (rhs.subst (matchingSubst impl.impl.head goal.args))
```

```lean
theorem default_and_explicit_reads_differ :
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind actualRead) = some int ∧
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind fun table =>
      assocOf (singletonEnv strImpl) (roleTable table) str_paterson (index str int) 0) = some char
```

## `lean/Yulang/GeneralSourceRoleCstHeadOrigin295.lean`

```lean
theorem head_at_ordinal {root head body : Tree} {b : Nat}
    (parts : roleParts root = some (head,b,body)) :
    ∃ i, follow [i] root = some head
```

```lean
theorem selected_head_from_original {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (p : Tracked S (Address B))
    (picked : select policy scope w brand a packet = some p) :
    p.scope = scope ∧ ∃ i raw head name params,
      atWire (a.path ++ [i]) w = some raw ∧ Transfer raw head ∧
        ActualHead head name params ∧ p.head = toHead name params
```

## `lean/Yulang/GeneralSourceRoleCstNamingControl295.lean`

```lean
theorem unguarded_context_can_change_key :
    ((compile .selectedBranch 5 both 71 first (packet first) shiftedRole 2).map
      (fun r => r.rows.map RoleRow.role)) = some [12]
```

```lean
theorem checked_compares_actual_output_requests :
    (check .selectedBranch 5 both 71 first (packet first) naming shiftedOutput) = false ∧
    checkedCompile .selectedBranch 5 both 71 first (packet first) naming shiftedOutput 2 = none
```

```lean
theorem constructor_scope_used_only_by_second :
    (check .selectedBranch 5 both 71 first (packet first) naming shiftedCtor) = true ∧
    (check .selectedBranch 5 both 71 second (packet second) naming shiftedCtor) = false
```

```lean
theorem unrelated_lookups_do_not_change_selected_export :
    checkedCompile .selectedBranch 5 both 71 first (packet first) naming irrelevant 2 =
      some parameterTable
```

## `lean/Yulang/GeneralSourceRoleCstNamingGate295.lean`

```lean
theorem check_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) :
    check policy scope w brand a sealed reference current = true ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        Agree (reference r.scope) (current r.scope) r.role
```

```lean
theorem checked_reference_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) (fallback : Nat) (table : RoleSource) :
    checkedCompile policy scope w brand a sealed reference current fallback = some table ↔
      check policy scope w brand a sealed reference current = true ∧
      compile policy scope w brand a sealed reference fallback = some table
```

## `lean/Yulang/GeneralSourceRoleCstNamingPacket295.lean`

```lean
theorem capture_at_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (naming : S → Environment) (trace : Trace) :
    captureAt policy scope w brand a sealed naming = some trace ↔
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      capture (naming r.scope) r.role = trace
```

```lean
theorem checked_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (actual : S → Environment) (fallback : Nat) (table : RoleSource) :
    checked policy scope w brand a sealed actual fallback = some table ↔
      captureAt policy scope w brand a sealed.selected actual = some sealed.naming ∧
        compile policy scope w brand a sealed.selected actual fallback = some table
```

```lean
theorem captured_naming_same_result {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (packet : FiniteBoundary S B)
    (reference actual : S → Environment) (fallback : Nat) (table : RoleSource)
    (named : captureAt policy scope w brand a packet.selected reference = some packet.naming)
    (ok : checked policy scope w brand a packet actual fallback = some table) :
    compile policy scope w brand a packet.selected reference fallback = some table
```

## `lean/Yulang/GeneralSourceRoleCstNamingPacketFixture295.lean`

```lean
theorem exactly_consumed :
    captureAt .selectedBranch 5 both 71 first (packet first) naming = some binderTrace ∧
    captureAt .selectedBranch 5 both 71 second (packet second) naming = some ctorTrace
```

```lean
theorem altered_shape_denied :
    checked .selectedBranch 5 both 71 first ⟨packet first,[]⟩ naming 2 = none ∧
    checked .selectedBranch 5 both 71 first ⟨packet first,binderTrace.reverse⟩ naming 2 = none ∧
    checked .selectedBranch 5 both 71 first ⟨packet first,ctorTrace⟩ naming 2 = none
```

```lean
theorem consumed_constructor_value_checked :
    checked .selectedBranch 5 both 71 second pinnedSecond naming 2 = some charTable ∧
    checked .selectedBranch 5 both 71 second pinnedSecond shiftedCtor 2 = none ∧
    checked .selectedBranch 5 both 71 first pinnedFirst shiftedCtor 2 = some parameterTable
```

```lean
theorem exact_packet_respects_locality :
    checked .selectedBranch 5 both 71 first pinnedFirst irrelevant 2 = some parameterTable
```

## `lean/Yulang/GeneralSourceRoleCstNamingRequests295.lean`

```lean
theorem same_replies_cons (e f : Environment) (x : Query) (xs : List Query) :
    SameReplies e f (x::xs) ↔ reply e x = reply f x ∧ SameReplies e f xs
```

```lean
theorem query_body_exact (e f : Environment) (b : Body) :
    SameReplies e f (bodyQueries b) ↔ BodyAgree e f b
```

```lean
theorem query_output_exact (e f : Environment) (n : Nat) (o : Output) :
    SameReplies e f (outputQueries e n o) ↔ OutputAgree e f n o
```

```lean
theorem query_role_exact (e f : Environment) (r : Role) :
    SameReplies e f (queryList e r) ↔ Agree e f r
```

## `lean/Yulang/GeneralSourceRoleCstNamingScope295.lean`

```lean
theorem tracked_symbolic {S H : Type} (p : Tracked S H) (env : S → Environment)
    (fallback : Nat) :
    runTracked env fallback [p] =
      (symbolic p).bind (fun r => lower env fallback [r])
```

```lean
theorem tracked_env_congr {S H : Type} (p : Tracked S H) (fallback : Nat)
    (before after : S → Environment)
    (same : ∀ r, symbolic p = some r → Agree (before r.scope) (after r.scope) r.role) :
    runTracked before fallback [p] = runTracked after fallback [p]
```

```lean
theorem compile_env_congr {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (before after : S → Environment) (fallback : Nat)
    (same : ∀ p, handoff policy scope w brand a sealed = some p →
      ∀ r, symbolic p = some r → Agree (before r.scope) (after r.scope) r.role) :
    compile policy scope w brand a sealed before fallback =
      compile policy scope w brand a sealed after fallback
```

## `lean/Yulang/GeneralSourceRoleCstNamingTrace295.lean`

```lean
theorem values_keys (e : Environment) (qs : List Query) :
    (values e qs).map Prod.fst = qs
```

```lean
theorem values_agree_exact (e f : Environment) (qs : List Query) :
    values e qs = values f qs ↔ SameReplies e f qs
```

```lean
theorem output_query_shape {e f : Environment} (id : Nat) (o : Output)
    (h : OutputAgree e f id o) : outputQueries e id o = outputQueries f id o
```

```lean
theorem flat_map_eq {A B : Type} (f g : A → List B) (xs : List A)
    (ok : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g
```

```lean
theorem query_shape {e f : Environment} (r : Role) (ok : Agree e f r) :
    queryList e r = queryList f r
```

```lean
theorem captures_eq_agree (e f : Environment) (r : Role) :
    capture e r = capture f r ↔ Agree e f r
```

## `lean/Yulang/GeneralSourceRoleCstNamingWitness295.lean`

```lean
theorem body_match_exact (e f : Environment) (b : Body) :
    bodyMatch e f b = true ↔ BodyAgree e f b
```

```lean
theorem output_match_exact (e f : Environment) (r : Nat) (o : Output) :
    outputMatch e f r o = true ↔ OutputAgree e f r o
```

```lean
theorem role_match_exact (e f : Environment) (r : Role) :
    roleMatch e f r = true ↔ Agree e f r
```

## `lean/Yulang/GeneralSourceRoleCstOtherRole295.lean`

```lean
theorem other_role_is_fallback (table : RoleSource) (row : RoleRow)
    (just : table.rows = [row]) (r : Nat) (different : r ≠ row.role) :
    roleTable table r = fallback table.fallbackArity
```

```lean
theorem no_other_role_data {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (arity : Nat)
    (table : RoleSource) (done : compile policy scope w brand a sealed env arity = some table) :
    ∃ row : RoleRow, table.rows = [row] ∧ ∀ r, r ≠ row.role → roleTable table r = fallback arity
```

## `lean/Yulang/GeneralSourceRoleCstOutcomePrecise295.lean`

```lean
theorem never_unsupported_symbolic {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback ≠ .error .unsupportedSymbolic
```

```lean
theorem naming_mismatch_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback = .error .namingMismatch ↔
      ∃ t, captureAt policy scope w brand a packet.selected env = some t ∧ t ≠ packet.naming
```

```lean
theorem old_export_rejection_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a packet env fallback = .error .oldExportRejected ↔
      captureAt policy scope w brand a packet.selected env = some packet.naming ∧
      compile policy scope w brand a packet.selected env fallback = none
```

## `lean/Yulang/GeneralSourceRoleCstRawType295.lean`

```lean
theorem parts_role_node {t h b : Tree} {i : Nat} (parts : roleParts t = some (h,i,b)) :
    ∃ cs, t = .node .role cs
```

```lean
theorem selected_original_role_node {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (out : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ cs, atWire a.path w = some (.node "RoleDeclaration" cs)
```

```lean
theorem selected_original_head_node {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (out : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ i cs n ps, atWire (a.path ++ [i]) w = some (.node "TypeExpression" cs) ∧
      out.head = GeneralSourceRoleCstShapes293.toHead n ps
```

```lean
theorem type_evidence_original_node {w : Wire} {t : Tree}
    {shape : GeneralSourceRoleSyntaxBoundary292.Shape}
    (exact : Transfer w t) (proof : GeneralSourceRoleCstTypeRules293.IsType t shape) :
    ∃ cs, w = .node "TypeDeclaration" cs
```

## `lean/Yulang/GeneralSourceRoleCstRequiredControl295.lean`

```lean
theorem required_slot_separate_from_nondeclaration :
    compile .selectedBranch 5 retained 71 first permitted naming 2 = some requiredTable ∧
    (roleTable requiredTable 2).assoc 0 = some none ∧
    (roleTable requiredTable 2).assoc 1 = none
```

```lean
theorem required_omitted_not_a_default :
    ((compile .selectedBranch 5 retained 71 first permitted naming 2).bind actualRead) = none ∧
    ¬ AssocWellFormed (singletonEnv omittedImpl) (roleTable requiredTable)
```

```lean
theorem both_selected_still_not_a_joint_same_key_export :
    ((handoff .selectedBranch 5 both 71 first (packet first)).bind fun p =>
      (handoff .selectedBranch 5 both 71 second (packet second)).bind fun q =>
        runTracked naming 2 [p,q]) = none
```

## `lean/Yulang/GeneralSourceRoleCstRowExtent295.lean`

```lean
theorem read_locates_own_type {S B : Type} [DecidableEq B] [DecidableEq S]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (built : compile policy scope w brand a sealed env fallback = some table)
    (role name : Nat) (term : Option Roles.Term) (found : (roleTable table role).assoc name = some term) :
    ∃ (p : Tracked S (Address B)) (site : Address B) (shape : Shape)
      (root selected t : Tree) (raw : Wire) (outer inner : Extent),
      OriginAt env [p] role name term a site ∧ Transfer w root ∧
      locate a.path root 0 = some (selected,outer) ∧ locate site.path root 0 = some (t,inner) ∧
      atWire site.path w = some raw ∧ Transfer raw t ∧ IsType t shape ∧
      outer.low ≤ inner.low ∧ inner.high ≤ outer.high ∧
      inner.high = inner.low + (spelling raw).utf8ByteSize
```

## `lean/Yulang/GeneralSourceRoleCstSealOrigin295.lean`

```lean
theorem kept_export {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (packet : Selection Brand) (out : Tracked Scope (Address Brand))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ root, Transfer w root ∧
      GeneralSourceRoleCstRustSnapshot293.exportAt scope ⟨brand,root⟩ a = some out
```

```lean
theorem selected_site {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (packet : Selection Brand) (out : Tracked Scope (Address Brand))
    (accepted : select policy scope w brand a packet = some out) :
    out.atRole = a ∧ a = packet.address ∧ ∃ role raw,
      atWire a.path w = some raw ∧ Transfer raw role
```

## `lean/Yulang/GeneralSourceRoleCstSelectedCompile295.lean`

```lean
theorem handoff_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand)
    (out : Tracked Scope (Address Brand)) :
    handoff policy scope w brand a sealed = some out ↔ scope = sealed.allowedScope ∧
      select policy scope w brand a sealed.selected = some out
```

```lean
theorem compile_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand)
    (env : Scope → Environment) (fallback : Nat) (table : RoleSource) :
    compile policy scope w brand a sealed env fallback = some table ↔
      ∃ p, scope = sealed.allowedScope ∧
        select policy scope w brand a sealed.selected = some p ∧
        runTracked env fallback [p] = some table
```

```lean
theorem rejected_never_compiles {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (reject : handoff policy scope w brand a sealed = none) :
    compile policy scope w brand a sealed env fallback = none
```

```lean
theorem compile_origin {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (ok : compile policy scope w brand a sealed env fallback = some table) :
    scope = sealed.allowedScope ∧ a = sealed.selected.address ∧
      ∃ p, p.atRole = a ∧ select policy scope w brand a sealed.selected = some p ∧
        runTracked env fallback [p] = some table
```

## `lean/Yulang/GeneralSourceRoleCstSelectedControl295.lean`

```lean
theorem reusable_view_found_both :
    (useBound .selectedBranch 5 both 71 first diag).isSome = true ∧
    (useBound .selectedBranch 5 both 71 second diag).isSome = true
```

```lean
theorem selected_controls :
    compile .selectedBranch 5 both 71 first (packet first) naming 2 = some parameterTable ∧
    compile .selectedBranch 5 both 71 second (packet first) naming 2 = none ∧
    compile .selectedBranch 5 both 71 second (packet second) naming 2 = some charTable
```

```lean
theorem wrong_context_denied :
    compile .selectedBranch 6 both 71 first (packet first) naming 2 = none ∧
    compile .whole 5 both 71 first (packet first) naming 2 = none ∧
    compile .selectedBranch 5 both 72 first (packet first) naming 2 = none
```

```lean
theorem reader_differs_by_selected_declaration :
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind actualRead) = some int ∧
    ((compile .selectedBranch 5 both 71 second (packet first) naming 2).bind actualRead) = none ∧
    ((compile .selectedBranch 5 both 71 second (packet second) naming 2).bind actualRead) = some char
```

## `lean/Yulang/GeneralSourceRoleCstSelectedDefault295.lean`

```lean
theorem old_read_omitted_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (built : compile policy scope w brand a sealed env fallback = some table)
    (impls : AssocEnv) (wf : WellFormed impls.cores) (goal : Goal) (name : Nat)
    (success : resolve impls.cores wf goal = .resolved) (impl : AssocImpl)
    (present : impl ∈ impls.impls) (selected : candidates impls.cores goal = [impl.impl])
    (omitted : impl.assoc.lookup name = none) (value : Term) :
    ∃ entry, entry.atRole = a ∧ a = sealed.selected.address ∧
      (assocOf impls (roleTable table) wf goal name = some value ↔
        ∃ body, AnchoredAssoc w env entry a goal.role name (some body) ∧
          body.subst (defaultSubst goal.args) = value)
```

## `lean/Yulang/GeneralSourceRoleCstSelectedEnd295.lean`

```lean
theorem text_exports_one_original_role {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (text : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (ok : fromText fuel text policy scope brand a packet env fallback = .ok table) :
    ∃ (j : Json) (w : Wire) (children : List Wire) (row : RoleRow) (name : String)
      (arguments : List String),
      Json.parse text = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        a = packet.selected.selected.address ∧ scope = packet.selected.allowedScope ∧
        atWire a.path w = some (.node "RoleDeclaration" children) ∧
        table.rows = [row] ∧ Valid table ∧ row.arity = arguments.length ∧
        (env scope).role name = some row.role
```

```lean
theorem text_read_has_raw_type {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (text : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (ok : fromText fuel text policy scope brand a packet env fallback = .ok table)
    (role name : Nat) (term : Option Roles.Term) (found : (roleTable table role).assoc name = some term) :
    ∃ (j : Json) (w : Wire) (children : List Wire) (site : Address B)
      (root selected member : Tree) (outer inner : Extent),
      Json.parse text = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        Transfer w root ∧ atWire site.path w = some (.node "TypeDeclaration" children) ∧
        locate a.path root 0 = some (selected,outer) ∧ locate site.path root 0 = some (member,inner) ∧
        outer.low ≤ inner.low ∧ inner.high ≤ outer.high
```

## `lean/Yulang/GeneralSourceRoleCstSelectedExtent295.lean`

```lean
theorem locate_append (p q : Path) (root : Tree) (start : Nat) :
    locate (p ++ q) root start =
      (locate p root start).bind (fun hit => locate q hit.1 hit.2.low)
```

```lean
theorem subextent {root parent child : Tree} {start : Nat} {p q : Path}
    {outer inner : Extent}
    (base : locate p root start = some (parent,outer))
    (nested : locate (p ++ q) root start = some (child,inner)) :
    outer.low ≤ inner.low ∧ inner.high ≤ outer.high
```

```lean
theorem selected_member_contained {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (payload : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some payload)
    (item : Address B × Child) (member : item ∈ payload.body) :
    ∃ root selected t raw outer inside, Transfer w root ∧
      locate a.path root 0 = some (selected,outer) ∧
      locate item.1.path root 0 = some (t,inside) ∧
      atWire item.1.path w = some raw ∧ Transfer raw t ∧ Classification t item.2 ∧
      outer.low ≤ inside.low ∧ inside.high ≤ outer.high ∧
      inside.high = inside.low + (spelling raw).utf8ByteSize
```

## `lean/Yulang/GeneralSourceRoleCstSelectedJson295.lean`

```lean
theorem value_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (j : Json) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) (table : RoleSource) :
    fromValue fuel j policy scope brand a sealed env arity = .ok table ↔
      ∃ w, encode w = j ∧ depth w ≤ fuel ∧
        checked policy scope w brand a sealed env arity = some table
```

```lean
theorem text_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (str : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) (table : RoleSource) :
    fromText fuel str policy scope brand a sealed env arity = .ok table ↔
      ∃ j w, Json.parse str = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        checked policy scope w brand a sealed env arity = some table
```

## `lean/Yulang/GeneralSourceRoleCstSelectedMembers295.lean`

```lean
theorem member_prefix {Scope : Type} {scope : Scope} {site : Path} {t : Tree} {out : Tracked Scope Path}
    (chosen : GeneralSourceRoleCstRustRole293.extract scope site t = some out)
    (item : Path × Child) (h : item ∈ out.body) :
    ∃ b stmt leaf, item.1 = site ++ [b,stmt,leaf]
```

```lean
theorem exported_member_prefix {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (value : Tracked Scope (Address Brand))
    (chosen : exportAt scope s a = some value) (item : Address Brand × Child)
    (found : item ∈ value.body) :
    item.1.brand = a.brand ∧ ∃ b stmt leaf, item.1.path = a.path ++ [b,stmt,leaf]
```

```lean
theorem selected_member_is_exact_original {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (wanted : Address Brand)
    (packet : Selection Brand) (p : Tracked Scope (Address Brand))
    (picked : select policy scope w brand wanted packet = some p)
    (item : Address Brand × Child) (member : item ∈ p.body) :
    item.1.brand = wanted.brand ∧ (∃ b stmt leaf, item.1.path = wanted.path ++ [b,stmt,leaf]) ∧
      ∃ t raw, atWire item.1.path w = some raw ∧ Transfer raw t ∧ Classification t item.2
```

## `lean/Yulang/GeneralSourceRoleCstSelectedOutcome295.lean`

```lean
theorem ok_iff_checked {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy) (scope : S)
    (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (env : S → Environment) (fallback : Nat) (table : RoleSource) :
    run policy scope w brand a sealed env fallback = .ok table ↔
      checked policy scope w brand a sealed env fallback = some table
```

```lean
theorem rejects_selection_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) :
    run policy scope w brand a sealed env fallback = .error .selectionOrRecovery ↔
      handoff policy scope w brand a sealed.selected = none
```

```lean
theorem rejects_changed_naming {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (fallback : Nat) (trace : GeneralSourceRoleCstNamingTrace295.Trace)
    (supplied : captureAt policy scope w brand a sealed.selected env = some trace)
    (wrong : trace ≠ sealed.naming) :
    run policy scope w brand a sealed env fallback = .error .namingMismatch
```

## `lean/Yulang/GeneralSourceRoleCstSelectedReadback295.lean`

```lean
theorem exact_for_entry {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Selection Brand) (env : Scope → Environment) (fallback : Nat)
    (p : Tracked Scope (Address Brand)) (table : RoleSource)
    (produced : select policy scope w brand a sealed = some p)
    (roleSite : p.atRole = a) (attached : runTracked env fallback [p] = some table)
    (role name : Nat) (term : Option Roles.Term) :
    (roleTable table role).assoc name = some term ↔ AnchoredAssoc w env p a role name term
```

```lean
theorem anchor_declaration {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (ok : compile policy scope w brand a sealed env fallback = some table)
    (role name : Nat) (term : Option Roles.Term) :
    ∃ p, p.atRole = a ∧ a = sealed.selected.address ∧
     ((roleTable table role).assoc name = some term ↔ AnchoredAssoc w env p a role name term)
```

## `lean/Yulang/GeneralSourceRoleCstSelectedRow295.lean`

```lean
theorem aligned_singleton {A B : Type} {rel : A → B → Prop} {item : A} {items : List B}
    (ok : Aligned rel [item] items) : ∃ other, items = [other] ∧ rel item other
```

```lean
theorem map_singleton {A B : Type} {f : A → B} {xs : List A} {y : B}
    (h : xs.map f = [y]) : ∃ x, xs = [x] ∧ f x = y
```

```lean
theorem tracked_single_row {S H : Type} (env : S → Environment) (fallback : Nat)
    (p : Tracked S H) (table : RoleSource) (ok : runTracked env fallback [p] = some table) :
    table.fallbackArity = fallback ∧ Valid table ∧
      ∃ (r : RoleRow) (n : String) (params : List String), table.rows = [r] ∧
        HeadShape p.head n params ∧ (env p.scope).role n = some r.role ∧ r.arity = params.length
```

```lean
theorem compile_single_row {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Boundary S B) (env : S → Environment) (fallback : Nat)
    (out : RoleSource) (h : compile policy scope w brand a packet env fallback = some out) :
    out.fallbackArity = fallback ∧ Valid out ∧
    ∃ (p : Tracked S (Address B)) (row : RoleRow) (name : String) (args : List String), p.atRole = packet.selected.address ∧ out.rows = [row] ∧
      HeadShape p.head name args ∧ (env p.scope).role name = some row.role ∧
      row.arity = args.length
```

## `lean/Yulang/GeneralSourceRoleCstSelectedSeal295.lean`

```lean
theorem select_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (out : Tracked Scope (Address Brand)) :
    select policy scope w brand asked p = some out ↔
      asked = p.address ∧ policy = p.policy ∧
        p.receipt.fromWire = w ∧
        GeneralSourceRoleCstVisibleReceipt294.project policy scope w brand asked p.receipt.diagnostics =
          some out
```

```lean
theorem different_address_none {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (neq : asked ≠ p.address) : select policy scope w brand asked p = none
```

```lean
theorem different_policy_none {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (neq : policy ≠ p.policy) : select policy scope w brand asked p = none
```

## `lean/Yulang/GeneralSourceRoleCstSymbolicChildren295.lean`

```lean
theorem type_admitted {t : Tree} {sh : Shape} (ok : IsType t sh) :
    ∃ o, Admitted .roleBodyDirect sh o
```

```lean
theorem classified_compatible {t : Tree} {c : Child} (ok : Classification t c) : Compatible c
```

```lean
theorem collect_compatible (children : List Child)
    (ok : ∀ c ∈ children, Compatible c) :
    ∃ shapes outputs, Collects children shapes ∧
      Aligned (Admitted .roleBodyDirect) shapes outputs
```

## `lean/Yulang/GeneralSourceRoleCstSymbolicTotal295.lean`

```lean
theorem generated_head (n : String) (ps : List String) : HeadShape (toHead n ps) n ps
```

```lean
theorem compatible_to_symbolic {S H : Type} (p : Tracked S H) (n : String) (ps : List String)
    (head : HeadShape p.head n ps) (good : ∀ c ∈ p.body.map Prod.snd, Compatible c) :
    ∃ out, symbolic p = some out ∧ out.scope = p.scope ∧ out.role.spelling = n ∧
      out.role.binders = ps
```

```lean
theorem selected_goes_symbolic {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (chosen : Selection B)
    (p : Tracked S (Address B)) (produced : select policy scope w brand a chosen = some p) :
    ∃ out, symbolic p = some out ∧ out.scope = scope
```

```lean
theorem handoff_goes_symbolic {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (p : Tracked S (Address B)) (produced : handoff policy scope w brand a sealed = some p) :
    ∃ out, symbolic p = some out ∧ out.scope = scope
```

Indexed 92 theorem declarations; every one appears in exactly one standalone audit.
