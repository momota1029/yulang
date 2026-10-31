# EFFECT-PERMISSION-CONSTRUCTOR-REALIZATION-20261028/r1 — proof handoff revision 1

Contract SHA-256: `ffa32721d0c293d50f4a1a972e3da6955b4f0344c2ed6de037843ea8d73a2e35`.
Baseline: `6f9d7314f`, branch `yulang3`. Assignment/worker:
`/root/effect_permission_constructor_realization_proof`, actual active-work
acknowledgement sent to primary in this session. Registered lean_prover leaf;
requested model/effort bounded lean_prover; effective model/effort metadata
UNKNOWN. Sole author, no descendants. Outcome: **checked SourceOrigin repair;
constructed-but-unchecked event refinement; original parents OPEN**.

## Fixed original claim and authority

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5: every supported original source program, every lawful finite
construction history, every actual retained extrusion occurrence; preserve
original source typing, required principal coverage, soundness, progress and
termination with one joint original scoped witness, complete Call/effects,
recursive sharing and all correlated evidence. Its original all-source claim
remains OPEN. The current qualification correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: SCCs in each fixed
Value-birth-level induced graph; equal numeric levels do not identify scopes.
No result in this packet changes qualification or proves the source equality lift.

The governing effect specification is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5,
including §§1.1–1.2: negative concrete annotations grant local subtraction;
actual handler inflow determines subtraction; symbolic dependencies and
independent same-row lineages remain. The §6 example remains retracted.
Top-level inference principles §§1–5 retain ordinary generation/accumulation/
propagation. These actual sources, the original parent, both skill references,
root AGENTS/pre-sprint, sprint rules and contract were read before construction.
No research draft or old checker receipt supplied semantic authority.

Lean boundaries inspected: `YulangClosure.SourceProblem.InferenceSoundness`
and `SourceScopedCoverage` in Contracts are propositions, not concrete source
instances; `LocalLaws` contains independent assumptions. The unchanged
`OriginalEffectHygiene` and `WholeMetatheory` do not close the annotation/native
bridge. No new LocalLaws premise or circular typing relation was introduced.

## Exact changes and source crosswalk

Repository writes are exactly:

- `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean`: replace
  the impossible `symbolVar = none` branch at line 163 with
  `exact False.elim (symbolic.2 rfl)`. All 12 original named theorems now pass
  the bundled checker on their final unchanged hash.
- `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean`:
  partial event refinement candidate. **Its final build FAILS; no new theorem
  is delivered as checked or axiom-audited.**
- this handoff only.

All Rust locators in the table use the byte-preserved baseline files copied
under scratch (`baseline-candidate_effect.rs` and `baseline-candidate_scheme.rs`),
not concurrently instrumented Rust bytes. The crosswalk is inspected source
correspondence; it has no independent authentication or universal native simulation.

| Frozen Rust owner | Candidate Lean representation / intended refinement | Exact limitation |
| --- | --- | --- |
| candidate_effect.rs:1365–1384 scoped effect lookup | `EffectMemo.hit/miss`, `effect_memo_refines`; real `(scope,name)` lookup; miss records `nextEffect` and increments exactly once | Native key/ID encoding, level state, resource checks and journal/sample effects are absent. First allocation seam is `fresh_effect_at_level(level)` at 1373. |
| candidate_effect.rs:1328–1362 value/hole lookup | `ValueEvents.symbolVar` uses computed `scopedValue`, preserving scope and separate value/hole tables | No lower value/hole event relation or actual term-store allocation theorem was added. |
| candidate_effect.rs:2256–2269, 2282–2309 tail then view then allocation | `SignatureEvent.closed/tailed`, `ViewEvent.hit/miss`; a tail miss precedes view lookup; a hit preserves existing payload; every signature event allocates its port | Family=None and annotation context only. `candidate_signature_view` at 2292–2305 creates real attachment/context state absent from ViewData. Native allocation, bound insertion, and term construction remain OPEN. |
| candidate_effect.rs:1558–1565 paired delegated calls | `SignaturePairEvent.pair`, `signature_pair_event_refines`; positive then negative state threading and both row births | `SignatureBound` is data only. The actual `candidate_insert_bound` transition at 2310–2318 is not represented or proved; it cannot be inferred from a returned descriptor. |
| candidate_effect.rs:1518–1569 omitted/singleton/concrete/delegated branches | `PortEvent`; singleton symbolic shortcut precedes delegation; negative nonempty concrete port computes one shared row, retained owner/scope/parameter/occurrence and concrete members | Native success is not implied by an origin observer at 1536: checked byte accounting follows it before `permissions.push` at 1547. Allocation/retained-path/ID decoding is OPEN. |
| candidate_effect.rs:1435–1508 Function/Tuple/leaf ordering | `ValueEvents`/`TupleEvents`; argument value, result value, argument effect, result effect; composed polarity and complete retained paths; `value_events_refine`/`tuple_events_refine` intend to derive prior Construction | No claim that native histories are exhaustive. Source preflight, scalar/term/HIR decoding, tuple element effect checks, records/variants/methods/optional fields remain omitted from this local relation and required by the full parent. |
| same retained entries | `event_origins_and_births` intends to give `Origin shape p entry.path entry.allocatedRow entry.metadata`, `Owned c entry.metadata`, and `entry.allocatedRow ∈ births` for the SAME entry | A birth list records modeled fresh-effect allocation calls, not global freshness/uniqueness without a native State invariant. No distinct-entry collapse or new source restriction is used. |
| finite catalog consumer | `event_catalog_export` intends to apply refinement to SourceOrigin.constructed_catalog_export | This is finite-catalog mathematics only and currently unchecked. Live capture, published root membership and exported native port are not conclusions. |

Modeled cases: scoped effect memo hit/miss; fresh omitted port; singleton symbol;
negative nonempty concrete grant; explicit covariant signatures with zero/one
symbolic tail; annotation-local view hit/miss; two delegated allocations;
Function recursion and nonempty Tuple with index-shifted paths; opaque scalar
and computed scoped value/hole calls. Failed native resource/refusal paths are
not modeled as successful events. This does not remove any accepted case from
the original source language. No theorem claims every successful native call
has an Event/Construction history, and no event takes Origin as a hypothesis.

## Checks, finite bound and retained failures

Installed Lake resolved read-only with `elan which lake` from the pinned project:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions from all three helpers:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Exactly three serialized helper invocations; the primary explicitly released
each frozen argv/hash after checking the shared verification slot/headroom.
The second invocation waited for Cargo cessation. Each used one CPU via
`taskset -c 0`, `LEAN_NUM_THREADS=1`, pinned project `-j1 -M1024`, helper/outer
60-second deadlines, TMPDIR inside the leased scratch. No shared cache,
default-target build, root import, manifest/toolchain/dependency mutation,
installation, Cargo command, Git mutation, child launch or external contact
was performed by this leaf.

| Invocation | Final checked/attempted source | Exit | Wall | Peak RSS KiB | Result |
| --- | --- | --- | --- | --- | --- |
| 1/3 | SourceOrigin `db37f9d…` | 0 | 9.11s | 969360 | Focused build + all 12 exact printed types and complete transitive axiom audits PASS |
| 2/3 | ConstructorRealization `ddde27ab…` | 1 | 4.40s | 731944 | Multiline record-update syntax errors at :28 and :46; cascading unknown relations; no audit |
| 3/3 | ConstructorRealization `893dcc04…` | 1 | 1.00s | 762304 | Indexed cases binder-count errors; no audit |

Aggregate measured wrapper wall time 14.51s, user+system CPU 6.74s; maximum
969360 KiB < 1 GiB. All three allowed invocation slots are exhausted. The
unused fraction of the 180-second budget does not authorize another attempt.
Reasoning/read time was not separately instrumented. No resource renewal is
requested. SourceOrigin retains one existing unused-simp warning at :172.

For N=1,2,3 the exact wrapper was:

```text
/usr/bin/time -v -o <scratch>/check-N.time timeout 60 taskset -c 0 python3 <scratch>/run-check-N.py
```

`<scratch>` is exactly
`/tmp/yulang-effect-permission-constructor-realization-20261028-r1/lean-project`.
Each immutable `check-N-argv.json` carries the complete argument array. The
wrapper loads it, calls subprocess.run with combined stdout/stderr into
`check-N.log`, and exits with the helper's actual exit. Helper 1 builds only
`+YulangClosure.FormalPermissionSourceOrigin`; helpers 2/3 build only
`+YulangClosure.FormalPermissionConstructorRealization`, then would audit the
12 old plus 11 new theorem names. Neither failed build reached that audit.
All helper subprocess versions and exits are in their raw logs. No checker
receipt for the new module or default target is invented.

Before the first edit, the exact prior failed source `3e8ae8ba…` and original
check.log/argv/command were copied to `preserved-failure/` (files mode 444,
directory 555). Before syntax repair, invocation-2 source/log/time/argv/wrapper
were copied to `preserved-check-2/`, equally immutable. Final failure bytes and
all corresponding evidence are in `preserved-check-3/`, equally immutable.
The prior committed failure remains in Git history. Original and all new raw
failures are retained; no failed log was overwritten by a success.

First final Lean failure, verbatim:

```text
error: YulangClosure/FormalPermissionConstructorRealization.lean:34:2: Too many variable names provided at alternative `hit`: 3 provided, but 2 expected
error: YulangClosure/FormalPermissionConstructorRealization.lean:34:49: Unknown identifier `found`
error: YulangClosure/FormalPermissionConstructorRealization.lean:34:20: unsolved goals
case hit
scope name row✝ : Nat
s : State
row : s.effects (scope, name) = some row✝
⊢ (match s.effects (scope, name) with
        | some row => (row, s.effects, s.nextEffect)
        | none =>
          (s.nextEffect, fun k => if k = (scope, name) then some s.nextEffect else s.effects k, s.nextEffect + 1)).fst =
      row✝ ∧
    { nextValue := s.nextValue,
        nextEffect :=
          (match s.effects (scope, name) with
              | some row => (row, s.effects, s.nextEffect)
              | none =>
                (s.nextEffect, fun k => if k = (scope, name) then some s.nextEffect else s.effects k,
                  s.nextEffect + 1)).2.snd,
        nextView := s.nextView, values := s.values, holes := s.holes,
        effects :=
          (match s.effects (scope, name) with
              | some row => (row, s.effects, s.nextEffect)
              | none =>
                (s.nextEffect, fun k => if k = (scope, name) then some s.nextEffect else s.effects k,
                  s.nextEffect + 1)).2.fst,
        views := s.views, viewData := s.viewData } =
      s
```

The analogous `miss` alternative at :35 expects one name, not two; the ViewEvent
alternatives at :70–77 have the same surplus names. A precise **unexecuted**
repair candidate is `hit s row found` → `hit s found`, `miss s absent` →
`miss absent`, and the corresponding ViewEvent case alternatives. This is not
applied after the bound and is not claimed sufficient without a future check.
The full actual goals (including all closed/tailed view cases) are retained in
`check-3.log`. There is no proved counterexample to the semantic refinement;
this is an elaboration failure and leaves all new claims open.

Source scan of the four-module dependency cone found no source proof holes,
project axioms, native-evaluation assumptions or kernel bypasses; its only
word-match was the English comment “transitions admit” in unchanged LiveCapture.
That source scan does not substitute for a transitive audit. The 12 repaired
SourceOrigin theorem audits follow verbatim; the 11 new declarations have
**NOT_AUDITED** transitive axiom status and **no completed printed-type audit**.

## Complete accepted theorem types and transitive axiom results

Every name below has prefix `YulangClosure.FormalPermissionSourceOrigin`.
This is raw successful invocation-1 output on final `db37f9d…` bytes, not source
statements substituted for checker output:

```text
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.memo_hit
YulangClosure.FormalPermissionSourceOrigin.memo_hit : ∀ (table : Nat × Nat → Option Nat) (key : Nat × Nat)
  (next row : Nat),
  table key = Option.some row → YulangClosure.FormalPermissionSourceOrigin.memo table key next = (row, table, next)
'YulangClosure.FormalPermissionSourceOrigin.memo_hit' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.memo_hit
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.memo_miss
YulangClosure.FormalPermissionSourceOrigin.memo_miss : ∀ (table : Nat × Nat → Option Nat) (key : Nat × Nat)
  (next : Nat),
  table key = Option.none →
    (YulangClosure.FormalPermissionSourceOrigin.memo table key next).fst = next ∧
      (YulangClosure.FormalPermissionSourceOrigin.memo table key next).snd.snd = next + 1 ∧
        (YulangClosure.FormalPermissionSourceOrigin.memo table key next).snd.fst key = Option.some next
'YulangClosure.FormalPermissionSourceOrigin.memo_miss' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.memo_miss
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation
YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation : ∀
  (c : YulangClosure.FormalPermissionSourceOrigin.Context) (position : Nat) (concrete : List Nat)
  (s : YulangClosure.FormalPermissionSourceOrigin.State),
  (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).fst.positive =
      YulangClosure.FormalPermissionCaptureConstruction.Effect.row s.nextEffect ∧
    (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).fst.negative =
        YulangClosure.FormalPermissionCaptureConstruction.Effect.row (s.nextEffect + 1) ∧
      (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).snd.snd.nextEffect =
        s.nextEffect + 2
'YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.port_origin
@YulangClosure.FormalPermissionSourceOrigin.port_origin : ∀ {c : YulangClosure.FormalPermissionSourceOrigin.Context}
  {p : Bool} {source : YulangClosure.FormalPermissionSourceOrigin.SourcePort}
  {s : YulangClosure.FormalPermissionSourceOrigin.State} {out : YulangClosure.FormalPermissionSourceOrigin.PortResult},
  YulangClosure.FormalPermissionSourceOrigin.constructPort c p source s = Option.some out →
    ∀ {entry : YulangClosure.FormalPermissionLiveCapture.Emission},
      entry ∈ out.entries →
        p = Bool.false ∧
          out.ports =
              YulangClosure.FormalPermissionCaptureConstruction.sharedPorts entry.row (Option.some entry.metadata) ∧
            entry.row = s.nextEffect ∧
              entry.metadata.concrete ≠ [] ∧ YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.port_origin' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.port_origin
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.construction_origins
@YulangClosure.FormalPermissionSourceOrigin.construction_origins : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.Construction c p s shape entries t →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries →
        YulangClosure.FormalPermissionCaptureConstruction.Origin shape p entry.path entry.allocatedRow entry.metadata ∧
          YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.construction_origins' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.construction_origins
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins
@YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {elements : List YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.TupleConstruction c p s elements entries t →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries →
        YulangClosure.FormalPermissionCaptureConstruction.Origin
            (YulangClosure.FormalPermissionCaptureConstruction.Shape.tuple elements) p entry.path entry.allocatedRow
            entry.metadata ∧
          YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export
@YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.Construction c Bool.false s shape entries t →
    YulangClosure.FormalPermissionCaptureConstruction.projectAll shape entries =
      Option.some
        (List.map
          (fun e =>
            { metadata := e.metadata, path := e.path,
              port :=
                YulangClosure.FormalPermissionCaptureConstruction.image shape
                  (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.effect
                    (YulangClosure.FormalPermissionCaptureConstruction.Effect.row e.allocatedRow) Bool.false) })
          entries)
'YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity
YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity : ∀
  (d : YulangClosure.FormalPermissionSourceOrigin.Domain),
  d.liveRow = d.parameterBase + d.context.parameter ∧
    d.negativeRoot = YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value d.shape Bool.false
'YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo
YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (s : YulangClosure.FormalPermissionSourceOrigin.Live) (e : YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (rest : List YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  s.capture.pending = e :: rest →
    YulangClosure.FormalPermissionSourceOrigin.Live.popWrite canon s =
      Option.some
        {
          capture :=
            YulangClosure.FormalPermissionLiveCapture.Capture.internAll canon
              (have __src := s.capture;
              { keys := __src.keys, pending := rest, expanded := s.capture.expanded ++ [e] })
              (YulangClosure.FormalPermissionCaptureConstruction.children e),
          writes :=
            s.writes ++
              [(s.capture.index e,
                  YulangClosure.FormalPermissionCaptureConstruction.expand
                    (fun child =>
                      (YulangClosure.FormalPermissionLiveCapture.Capture.internAll canon
                            (have __src := s.capture;
                            { keys := __src.keys, pending := rest, expanded := s.capture.expanded ++ [e] })
                            (YulangClosure.FormalPermissionCaptureConstruction.children e)).index
                        (canon child))
                    e)] }
'YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.discovery_membership
YulangClosure.FormalPermissionSourceOrigin.discovery_membership : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (store : YulangClosure.FormalPermissionSourceOrigin.DiscoveryStore)
  (kind : YulangClosure.FormalPermissionSourceOrigin.Discovery) (index : Nat)
  (s : YulangClosure.FormalPermissionSourceOrigin.Live)
  (e : YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  e ∈ YulangClosure.FormalPermissionSourceOrigin.Discovery.requests store kind index →
    canon e ∈ (YulangClosure.FormalPermissionSourceOrigin.Live.discover canon store kind index s).capture.keys
'YulangClosure.FormalPermissionSourceOrigin.discovery_membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.discovery_membership
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication
YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (s : YulangClosure.FormalPermissionLiveCapture.Capture)
  (a r : YulangClosure.FormalPermissionCaptureConstruction.Shape)
  (ae re : YulangClosure.FormalPermissionCaptureConstruction.Ports),
  canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false) =
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false →
    canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false) ∈ s.keys →
      YulangClosure.FormalPermissionLiveCapture.publish s (a.function ae r re) =
        Option.some
          (s.index
            (canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false)))
'YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival
YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival : ∀
  (first second : YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  List.idxOf first [] = List.idxOf second [] ∧ ¬first ∈ []
'YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival
```

## Parent application and exact remaining premises/owners

What follows now: the corrected `port_origin` proves its unchanged local
statement, and `construction_origins`/`tuple_construction_origins` derive the
structural Origin and shared source identity from an explicit prior Construction.
`constructed_catalog_export` applies that derived Origin to the finite catalog.
Each theorem retains every printed hypothesis. This repairs the previous final
failure but does not establish a concrete native instance or original source
soundness. The new events cannot yet be used to discharge Construction because
their refinement theorem fails to elaborate.

First formal premise: finish and audit `effect_memo_refines` at :34 (then the
view cases in `signature_event_refines` :70–77), followed by all 11 final
new theorem type/transitive-axiom audits. Owner: primary proof intake, requiring
a fresh bounded packet; no execution authorization remains here.

First native premise remains successful-constructor decoding into the SAME
State/Context/shape/path/allocated row and complete source identities. On a
memo miss, the exact first unproved allocation transition is
candidate_effect.rs:1373 `fresh_effect_at_level(level)` and its level/journal/
resource state; on a delegated view miss it is `candidate_signature_view` at
2292–2305, before the returned port's real `candidate_insert_bound` at
2310–2318. Owner: primary source/proof lane. Finite Rust observations can
supply evidence but cannot prove all-successful-history decoding.

Subsequent capture gaps remain OPEN, owner primary capture/proof lane:

- `Capture::expand_node` EffectRow branch at candidate_scheme.rs:1947–1950
  calls `self.row(RowKey::Effect(i))`; the old Node.row model stores a raw key,
  while native `row` at :1743–1770 computes a representative and graph-row
  index plus level/local metadata. This is the first concrete row-index seam.
- EffectOperand tail discovery at :1969–1979 is absent from structural children;
  successful row expansion at :2147 onward and interleaved cursor recurrence
  :2683–2691 are not decoded from actual stores into DiscoveryStore.
- Bound/evidence snapshot interning at :2122–2140 and context-payload traversal
  :2694–2705 remain unrepresented by supplied finite request lists.
- Actual pending.pop, child interning and assigned node-array writes remain
  simulation obligations; a model write log is not a native write receipt.
- Canonical representative transport at `intern` :1714 and exact negative
  formal-domain key membership at :2809–2818 remain distinct. Equal idxOf
  values can describe two absent endpoints (the checked negative result).
- Endpoint arrival, final negative root publication and actual
  formal_effect_permissions export membership remain OPEN. No allocation or
  Origin theorem alone establishes them.

Mutual TODO `CONSTRUCTOR-EVENT-DECODING-1`: original all-source parent; first
missing evidence is native State/key/identifier/term decoding and successful
allocation/view/bound transition correspondence. Proposed output: a checked
native-to-event simulation preserving the SAME metadata/path/row; falsifier:
a source-approved successful transition incompatible with these event updates.
Owner primary source/proof lane, no lease requested by this TODO.

Mutual TODO `CONSTRUCTOR-EVENT-CAPTURE-1`: first missing evidence is native
representative-row indexing and real row/bound/evidence/context extraction;
input exact native successful capture trace/store and canonical key meaning;
output live node-array/cursor simulation plus exact arrival/publication proof.
Owner primary capture/proof lane. Neither TODO authorizes source restriction,
new dependencies, a production change or stronger premises.

Conditional mathematics, kernel acceptance, independent review, inspected
source correspondence and production authority remain separate. Fresh
independent review is NOT_RUN by this producer. No parent A/B, whole-language
soundness, principality, progress, termination, source/native or production
gate closes. This is a preservation checkpoint pending primary adjudication;
the failed event module must not be promoted as checked proof.

## Frozen byte hashes and scratch ownership

| Dependency / artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean` | `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd` |
| `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean` | `893dcc04d23491b64230a2ebad956c3da88eb3e8b6146479a4aa616abc5f2e58` |
| `notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean` | `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e` |
| `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean` | `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c` |
| `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean` | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| `notes/theory/lean/YulangClosure/WholeMetatheory.lean` | `65777d3da4fb2a28b25e961049afb88f3ed750c30d04ae73bdc907ef5f93de26` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `tasks/agent-loop/sprints/effect-permission-constructor-realization-20261028-r1.md` | `ffa32721d0c293d50f4a1a972e3da6955b4f0344c2ed6de037843ea8d73a2e35` |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` |

Baseline Rust copies retain contract hashes: candidate_effect.rs `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`; candidate_scheme.rs `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`.

All scratch files are inside the one leased scratch root. `frozen-manifest.json` SHA-256 `f35f6db371d90291a0ed2d3ea7af31b668188718673734160f51b6288b13e6c3` inventories exact config/input/source/log/time/argv/wrapper/failure bytes. Generated `.lake/` outputs (including partial failed build traces) are scratch-only and this leaf's owned outputs. No shared generated output was written. Main raw log hashes:

- `check-1.log`: `b52baa4d14fa6d64ecc726f96c29be979781aba8cdafe7316b2ef2a1460e7150`.
- `check-2.log`: `282aeb60399db81e740d51a32f94ecc9c3e0b9375d2a81143c108283bdc49035`.
- `check-3.log`: `4c4be4cb64c4942f67b52a41aa53a0172800a16cd3c0d7f53ba9bfbced868f92`.


## Stop receipt

Worker STOPPED; all proof-file and scratch writes stop after this final handoff
revision and its hash notification. No Lean/helper/Cargo process remains in
this lane; no descendants or unresolved child leases. Exactly three helper
invocations are consumed, with no further retry. The primary owns any fresh
lease, repair/check budget, independent review, shared-state update and Git
integration. No scheduling, compiler, root-import, configuration, dependency,
question or other worker file was edited. No self-certification.
