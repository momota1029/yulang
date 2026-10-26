# Native relation interner r4 — fresh independent compiler review

Date: 2026-10-26. Reviewer: `/root/value_drain_review_r4`.
Review revision: 1. **ACCEPT for the stated physical interner construction.**
No blocking, major or minor target finding; no source or note repair requested.
The original whole native correspondence and `SourceProblem.InferenceSoundness`
remain **OPEN** at the explicit original parent obligations.

## Isolation, authority and frozen bytes

The reviewer did not author this component, supplied no construction repair and
started no descendants. Exact repository write lease: this receipt only.
Scratch and verification copies are confined to
`/workspace/scratch/f98087c7ac1a/relation-interner-review-r4`.
No Git operation, producer/shared status/import/configuration mutation or read
of the active downstream `NativeValueRelationExecution` was performed.

The assigned1200-second review started13:29:13 UTC, with a maximum of two
focused Lean bundles, each at most120 seconds, one CPU/thread and `-j1 -M1024`.
The existing AGENTS/pre-sprint proof-closure contract, authority and sprint rules,
Authoritative top-level inference principles, and `yulang-lean-proofs` skill and
source/execution references apply. Their pinned hashes match the versions already
read by this reviewer. The unchanged original Contracts roots distinguish
inference soundness, source-scoped witness construction and native correspondence;
a component result does not close those proposition-defined obligations.

The producer's supplied baseline is `6b26127636b988614c676270c37a428464948f37`.
All frozen source, artifact and input hashes were independently checked without
using Git. The complete source and construction note were read, together with
the actual owning Rust bodies and the exact theorem statements.

| Accepted repository artifact | SHA-256 |
| --- | --- |
| NativeRelationInterner.lean | `1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a` |
| 2026-10-26-native-relation-interner.md | `3ecf306f7db724b49b0dd3dd7465c5898ef048b3821c572dcc324cd309c64954` |
| 20261026-native-relation-interner-r4.md | `5527a70143a75f00ef55479c4a35d4cb579885e5ed584577bad4e5b7f87778f2` |

Producer freeze SHA-256:
`539a6ef402169754ab6d6dae9552014c8980888142322e1c4ada99065249d1f5`.
Artifact manifest SHA-256:
`1592518c73bb7c6155f93bfcc02318d9c4847eaba12db989b2e2c7bbca52fb2e`.
All25 fixed inputs,149 retained artifact files and the actual eight-module source
import cone match their recorded hashes. The active downstream module is absent
from that import cone and excluded from this verdict.

## 1. Native operation correspondence

Line locators refer to the frozen `crates/yu-solver/src` bytes, not a moving source.

| Native owner | Reviewed correspondence |
| --- | --- |
| `candidate_context.rs:267–296` | RawKey keeps the complete Value/Effect pair, Context, optional source set and physical flow ID. Flow keeps transformer plus all five demand fields. None and Some0 are distinct. |
| `candidate_context.rs:2786–2791,3062–3071` | Context assertion precedes three source-ordered guards. Nonidentity Effect self-relation rejects before the Effect demand guard; Value transformer and Effect demand produce ReceiptMismatch. Context assertion is explicitly represented as a panic/assertion cut, not falsely described as a Rust Err. |
| `candidate_context.rs:3072–3080` | Default full Flow uses ID0. Existing nondefault Flow is looked up before enabled/4096/work/reservation checks. New Flow checks enabled and record limit, charges work, reserves vector then map, checks the one-based ID, then appends/inserts. The construction preserves this exact order. |
| `candidate_source.rs:195–196,216–221` | Work uses checked addition and the65,536 limit. A successful charge occurs before later reservations, so later failure preserves it. Guarded external inventory increments are represented; failed increments can stutter on the projected fields. |
| `candidate_context.rs:3082–3094` | Full relation-key reuse precedes u32 conversion and all three reservations. Fresh allocation reserves relation vector, full-key map and pair map before inserting the pair head, retaining its previous value, appending the record and inserting the complete key. |
| `candidate_context.rs:2880–2882` | Decoding reads physical relation storage, then ID0/default or the exact nondefault Flow vector position. It does not read Entry.origin. Missing physical slots produce failure/none. |
| `candidate_context.rs:2047–2077,2148–2155` | Checkpoint captures the relation frontier. Rollback drains its suffix in reverse, removes full keys and restores each saved previous pair head. It retains the attempted Flow vector/map and work charge; no nonexistent Flow checkpoint is invented. |

The production mutation search found the Flow push/map insertion in the reviewed
constructor and no production Flow-vector truncation/removal/clear in this
rollback. Test-only corruption is not treated as valid native construction.
Standard exact-key map semantics and allocator result observations are explicit
model contracts. This is not a verification of Rust's standard HashMap internals,
allocator implementation, heap capacities or exact failed-reserve memory changes.

`Resources` must be populated with actual enabled state, Context count, platform
usize maximum and the outcomes of five distinct reservation calls at their source
cuts. It does not certify that those calls succeed. Unused later observations do
not influence an earlier returned outcome. The64-bit default maximum matches the
pinned target, while the parameter remains explicit.

## 2. Construction of complete-key reflection

The important bridge is genuinely constructed:

1. `Store.decode` reads only RawKey and the Flow vector; it never reads the ghost
   complete key. `stored_key_decodes` proves that this physical result equals the
   retained allocation origin using the actual Flow interner equations.
2. `physical_complete_key` and `physical_arena_cache` derive full physical-key
   equality and the same index as the accepted decoded Arena. They do not assume
   a chosen reflection table or a matching Arena result.
3. The materialized `Native` operations read `flowCache`, `relationCache` and
   `pairCache`. `Native.addRelation` saves the actual materialized previous pair
   head. Coherence with the reconstructed vector cache is derived from empty
   maps, exact inserts and actual reverse undo operations.
4. `NativeRun` admits calls including their error mutations and guarded inventory
   increments. `NativeHistory` constructs the reachable state through commits and
   cancellations. `native_history_refinement` derives both map coherence and
   vector history. Coherent is not an assumption of the final public success root.
5. `native_ok_refines_arena` takes the constructed history and the actual
   `(n.call resources key).2 = .ok id`. It constructs the precise actual output
   Arena and raw relation ID. Its conclusion also exposes Allowed, the Context
   bound and complete physical decoder readback. No semantic child/body success,
   matching-output witness or additional reflection premise supplies that result.

Entry.origin and the monotonically increasing birth clock are proof annotations
created at actual allocation. Physical lookup, guards, capacity decisions,
reservation order and pair-map restoration do not consult them. The independent
spoofed-origin probe additionally checks physical decoding and key reuse after
deliberately changing those ghost fields outside the valid-history domain. This
is a negative circularity test, not a claim that the forged state is reachable.

The exact theorem is instantiated after a real constructed cancel/retry history
in the independent probes. Its resulting equality is to the accepted
`NativeValuePorts.Arena.relation` operation with the computed actual output and
ID0; no separately assumed output agreement is needed.

## 3. Failure effects, cancellation and lifetime claims

Fresh Flow reservation failures after charging retain work but append no Flow.
Later relation conversion/reservation failure retains both the already appended
Flow/map and the charge. No projected relation record appears before all relation
reservations succeed. The current code models each failure position explicitly.

`RelationTrace` derives fresh keys and each previous pair-head value from the
actual constructor sequence. `relation_trace_undo` processes the suffix in reverse
and proves restored key/pair maps. `native_cancel_maps_and_flows` establishes
saved relation-vector/key-map/pair-map equality together with retained attempted
Flow vector/map and work. It does not state complete state rollback.

A raw relation index can be reused after cancellation. The birth clock is retained
and the examples give the same raw ID with a different complete key and later
birth. `same_id_across_forward_calls` is correctly restricted to a forward Run;
it is not promoted to identity across cancellation. Retained Flow raw fields do
not establish timeless semantic identity of their external Context/source/scope
objects; their lifetime interpretations remain separate owners.

Bounds are derived from history: at most4096 nondefault Flows, relation length at
most2^32, work at most65,536; returned relation ID is strictly below2^32 and a
materialized nondefault Flow ID lies in1..4096 with real vector readback. These
are the existing implementation guards, not newly chosen source restrictions.

## 4. Complete census and retained evidence

The final all-origin audit selects the actual module index, rejects originating
axioms, prints each full type and transitive axiom list, and checks the approved
standard-axiom whitelist. The independent verifier parsed588 unique balanced
begin/end blocks, including private/generated declarations, verified every full
type and axiom report against origin-inventory.json, and separately extracted all
109 authored theorem names from the source. All records and counts agree.

| Inventory | Verified count |
| --- | ---: |
| Originating declarations | 588 |
| Originating theorem constants | 244 |
| Authored roots | 109 |
| Private originating declarations | 18 |
| Private originating theorem constants | 12 |
| Theorems with no axioms | 97 |
| Theorems with only propext | 65 |
| Theorems with only Quot.sound | 3 |
| Theorems with propext and Quot.sound | 35 |
| Theorems with all three standard axioms | 44 |

All-declaration distribution is372 none,134 propext,3 Quot.sound,35
propext/Quot.sound and44 propext/Quot.sound/Classical.choice. No project axiom,
sorryAx, unchecked native-evaluation assumption or kernel bypass occurs. The
changed source has no proof hole or bypass match. The census has397,560 bytes,
SHA-256 `9b71e6d2aa0154f6949f71a50d56ed8d1c321576ad24908c309f95f50e4c55be`,
no replacement character, omitted type term, duplicate block or unreported root.

All eleven producer check receipts, exact source snapshots and log hashes were
reconciled. Check01 is the retained pre-Lean input-path failure, not a measured
zero-cost proof attempt; its sentinel is excluded from producer timing totals.
Failed elaborations02–06,08–09 remain preserved. Final10/11 use the same final
source; check11 includes the complete census and no warning/error. This review
does not erase the earlier failures or count a source snapshot as a successful
checker invocation.

## 5. Independent focused checks

An isolated copy of the eight-module cone and verified dependency cache was used.
The first bundle confirmed Lake5.0.0-src+eb6cafb / Lean4.35.0, recompiled the exact
frozen NativeRelationInterner with empty diagnostics, then failed only in the
reviewer's scratch file at a nested record-update layout. The target source was
unchanged and its recompilation succeeded. The failing probe bytes and complete
log remain as `check01-probe.lean` and `check01.log`.

The second, final authorized bundle checked only that corrected scratch probe;
all eleven review theorems pass with full types/axiom reports and no warning/error:

- default Flow bypasses later resource conditions;
- a constructed65,536-work state still reuses its existing Flow and relation when
  enabled and every reservation flag are false;
- Flow-map reservation failure leaves only the work charge;
- pair-map reservation failure leaves the allocated Flow but no relation/key/head;
- a constructed three-record same-pair history reverses a two-record suffix and
  restores the exact old head, while retaining the Flow map;
- optional source None differs from Some0;
- changing the last demand field, inputRoute, creates a distinct physical Flow/key;
- physical decode ignores a deliberately spoofed ghost origin;
- actual cancelled retry directly instantiates the exact Arena refinement theorem.

Two of two permitted Lean bundles were used. Total measured wall time was
15.809844 seconds, with peak sampled aggregate
RSS 990236672 bytes. Both bundles had
one CPU/thread, `-j1 -M1024`, a119-second total deadline and1280MiB aggregate
ceiling. No full/default rebuild, performance experiment or source regression
suite was needed for this unchanged proof component.

| Reviewer evidence | SHA-256 |
| --- | --- |
| check_integrity.py | `fc3e6c42206983e73e39748e97be11f4b4cc43f63df9ce1ca8fd609d1168a804` |
| integrity.json | `b108f39da772907213b89b2e842f0e23e787ed1a75a5ba3542107a3774878000` |
| check01.log, retained failed probe bundle | `208a3656d77197e5a2dc233a1892697d2ce7c49b9c9e442361019726f6d42e23` |
| check01-probe.lean | `7171cd8484ebe0f5955b866198b85988b0b2599b651c6c8deebe46fe3b088dd5` |
| Final ReviewNativeRelationInterner.lean | `4c6d0123b24b0cc09c8f5b7c45a0b396cccd5df2f7599c97d6599bed68aceda0` |
| check02.log | `d8b167a9b19d46f42ac9a4fa1504a51a2f58df3ac322850586ac12ad1c676bf2` |
| final-evidence.json | `d48d626ed4750095b58b29c29d43950d7a573a30e8587ceb1867de0fb8f70534` |

## 6. Parent application and exact remaining owners

This component supplies the physical relation-interning/complete-key reflection
step to the already accepted Value admission Arena. The next owner must identify
the actual full child key and intermediate Context/transformer vectors and compose
that exact result with admission/enqueue in one committed native history. The
active downstream module is not reviewed or certified here.

One concrete initialization boundary deserves explicit retention:
`candidate_source.rs:223–246`, `ScopeInventory::from_plan`, initializes work_used
from `plan.scoped_work_used`, then charges region/scope/input counts. Mapping a
real initialized Context into NativeHistory must account for that retained work;
it cannot assume every actual enabled Context begins with work0. The generic
history permits bounded inventory increments, and successful native initialization
must supply their actual counter/readback. The primary acknowledged this exact
supplier as a separate integration obligation; no scope extension or proof change
was needed in the frozen component.

Other unchanged original owners are the actual whole-execution event interpretation,
authentic Context count/vector, source-set and transformer/scope object meanings,
remaining Value/Effect operation semantics and diagnostic acceptance, and the same
original scoped source witness. Natural source behavior is not narrowed, and no
new algorithm, check, annotation requirement or semantic decision is introduced.
This result does not prove inference termination or close the full original
`SourceProblem.InferenceSoundness` merely because its finite interner computation
and constructor history are checked.

## Exact independent receipts and final probe output

```json
[
  {
    "started_utc": "2026-10-26T13:32:23.385126+00:00",
    "wall_seconds": 11.794784754994907,
    "commands": [
      {
        "command": [
          "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
          "--version"
        ],
        "exit": 0,
        "seconds": 0.11252948499895865
      },
      {
        "command": [
          "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
          "--no-cache",
          "env",
          "lean",
          "--version"
        ],
        "exit": 0,
        "seconds": 0.19911363199935295
      },
      {
        "command": [
          "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
          "--no-cache",
          "env",
          "lean",
          "-j1",
          "-M1024",
          "YulangClosure/NativeRelationInterner.lean",
          "-o",
          ".lake/build/lib/lean/YulangClosure/NativeRelationInterner.olean"
        ],
        "exit": 0,
        "seconds": 10.460651224006142
      },
      {
        "command": [
          "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
          "--no-cache",
          "env",
          "lean",
          "-j1",
          "-M1024",
          "ReviewNativeRelationInterner.lean"
        ],
        "exit": 1,
        "seconds": 1.022051392996218
      }
    ],
    "exit": 1,
    "termination": null,
    "peak_aggregate_rss_bytes": 990236672,
    "aggregate_ceiling_mib": 1280,
    "cpu_affinity": [
      8
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "pids": [
      161445,
      161450,
      161455,
      161458,
      161463,
      161583,
      161588
    ],
    "log_sha256": "208a3656d77197e5a2dc233a1892697d2ce7c49b9c9e442361019726f6d42e23",
    "probe_sha256": "7171cd8484ebe0f5955b866198b85988b0b2599b651c6c8deebe46fe3b088dd5",
    "source_sha256": "1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a"
  },
  {
    "started_utc": "2026-10-26T13:33:53.260057+00:00",
    "wall_seconds": 4.0150596809980925,
    "commands": [
      {
        "command": [
          "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
          "--no-cache",
          "env",
          "lean",
          "-j1",
          "-M1024",
          "ReviewNativeRelationInterner.lean"
        ],
        "exit": 0,
        "seconds": 4.014761374004593
      }
    ],
    "exit": 0,
    "termination": null,
    "peak_aggregate_rss_bytes": 903966720,
    "aggregate_ceiling_mib": 1280,
    "cpu_affinity": [
      8
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "pids": [
      162036,
      162042
    ],
    "log_sha256": "d8b167a9b19d46f42ac9a4fa1504a51a2f58df3ac322850586ac12ad1c676bf2",
    "probe_sha256": "4c6d0123b24b0cc09c8f5b7c45a0b396cccd5df2f7599c97d6599bed68aceda0",
    "source_sha256": "1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a"
  }
]
```

```text
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 ReviewNativeRelationInterner.lean
NativeRelationInternerReview.default_still_bypasses : ∀ (n : YulangClosure.NativeRelationInterner.Native),
  n.internFlow NativeRelationInternerReview.blocked { } = (n, YulangClosure.NativeRelationInterner.Result.ok 0)
'NativeRelationInternerReview.default_still_bypasses' depends on axioms: [propext]
NativeRelationInternerReview.full_work_history : YulangClosure.NativeRelationInterner.NativeHistory
  NativeRelationInternerReview.fullWork
'NativeRelationInternerReview.full_work_history' does not depend on any axioms
NativeRelationInternerReview.reuse_ignores_all_later_failure_flags : (NativeRelationInternerReview.fullWork.call
        NativeRelationInternerReview.blocked YulangClosure.NativeRelationInterner.Examples.key).snd =
    YulangClosure.NativeRelationInterner.Result.ok 0 ∧
  (NativeRelationInternerReview.fullWork.call NativeRelationInternerReview.blocked
              YulangClosure.NativeRelationInterner.Examples.key).fst.store.workUsed =
      65536 ∧
    (NativeRelationInternerReview.fullWork.call NativeRelationInternerReview.blocked
                YulangClosure.NativeRelationInterner.Examples.key).fst.store.relations.length =
      1
'NativeRelationInternerReview.reuse_ignores_all_later_failure_flags' does not depend on any axioms
NativeRelationInternerReview.flow_map_failure_keeps_charge_only : have answer :=
  { }.call { flowMap := false } YulangClosure.NativeRelationInterner.Examples.key;
answer.snd = YulangClosure.NativeRelationInterner.Result.error YulangClosure.NativeRelationInterner.Failure.exhausted ∧
  answer.fst.store.workUsed = 1 ∧
    answer.fst.store.flows = [] ∧
      answer.fst.store.relations = [] ∧
        answer.fst.flowCache YulangClosure.NativeRelationInterner.Examples.key.flow = none
'NativeRelationInternerReview.flow_map_failure_keeps_charge_only' does not depend on any axioms
NativeRelationInternerReview.pair_map_failure_keeps_flow_not_relation : have answer :=
  { }.call { pairMap := false } YulangClosure.NativeRelationInterner.Examples.key;
answer.snd = YulangClosure.NativeRelationInterner.Result.error YulangClosure.NativeRelationInterner.Failure.exhausted ∧
  answer.fst.store.workUsed = 1 ∧
    answer.fst.store.flows = [YulangClosure.NativeRelationInterner.Examples.key.flow] ∧
      answer.fst.store.relations = [] ∧
        answer.fst.flowCache YulangClosure.NativeRelationInterner.Examples.key.flow = some 1 ∧
          answer.fst.relationCache
                (YulangClosure.NativeRelationInterner.encode YulangClosure.NativeRelationInterner.Examples.key 1) =
              none ∧
            answer.fst.pairCache YulangClosure.NativeRelationInterner.Examples.key.pair = none
'NativeRelationInternerReview.pair_map_failure_keeps_flow_not_relation' does not depend on any axioms
NativeRelationInternerReview.three_same_pair_history : YulangClosure.NativeRelationInterner.NativeHistory
  NativeRelationInternerReview.third
'NativeRelationInternerReview.three_same_pair_history' does not depend on any axioms
NativeRelationInternerReview.reversed_suffix_restores_real_old_head : NativeRelationInternerReview.third.pairCache
      YulangClosure.NativeRelationInterner.Examples.key.pair =
    some 2 ∧
  Option.map YulangClosure.NativeRelationInterner.Entry.previous
        NativeRelationInternerReview.third.store.relations[1]? =
      some (some 0) ∧
    Option.map YulangClosure.NativeRelationInterner.Entry.previous
          NativeRelationInternerReview.third.store.relations[2]? =
        some (some 1) ∧
      NativeRelationInternerReview.restored.pairCache YulangClosure.NativeRelationInterner.Examples.key.pair = some 0 ∧
        NativeRelationInternerReview.restored.relationCache
              (YulangClosure.NativeRelationInterner.encode NativeRelationInternerReview.secondKey 1) =
            none ∧
          NativeRelationInternerReview.restored.relationCache
                (YulangClosure.NativeRelationInterner.encode NativeRelationInternerReview.thirdKey 1) =
              none ∧
            NativeRelationInternerReview.restored.relationCache
                  (YulangClosure.NativeRelationInterner.encode YulangClosure.NativeRelationInterner.Examples.key 1) =
                some 0 ∧
              NativeRelationInternerReview.restored.flowCache YulangClosure.NativeRelationInterner.Examples.key.flow =
                some 1
'NativeRelationInternerReview.reversed_suffix_restores_real_old_head' depends on axioms: [propext]
NativeRelationInternerReview.absent_sources_differs_from_zero : (NativeRelationInternerReview.noSourceState.call { }
        NativeRelationInternerReview.zeroSources).snd =
    YulangClosure.NativeRelationInterner.Result.ok 1 ∧
  NativeRelationInternerReview.noSourceState.store.readback 0 = some NativeRelationInternerReview.noSources ∧
    (NativeRelationInternerReview.noSourceState.call { } NativeRelationInternerReview.zeroSources).fst.store.readback
        1 =
      some NativeRelationInternerReview.zeroSources
'NativeRelationInternerReview.absent_sources_differs_from_zero' depends on axioms: [propext]
NativeRelationInternerReview.last_demand_field_changes_physical_intern : (YulangClosure.NativeRelationInterner.Examples.physicalFirst.call
        { } NativeRelationInternerReview.changedRoute).snd =
    YulangClosure.NativeRelationInterner.Result.ok 1 ∧
  (YulangClosure.NativeRelationInterner.Examples.physicalFirst.call { }
              NativeRelationInternerReview.changedRoute).fst.flowCache
        NativeRelationInternerReview.changedRoute.flow =
      some 2 ∧
    (YulangClosure.NativeRelationInterner.Examples.physicalFirst.call { }
                NativeRelationInternerReview.changedRoute).fst.store.readback
        1 =
      some NativeRelationInternerReview.changedRoute
'NativeRelationInternerReview.last_demand_field_changes_physical_intern' depends on axioms: [propext]
NativeRelationInternerReview.decoder_does_not_read_ghost_origin : NativeRelationInternerReview.spoofedGhost.store.readback
      0 =
    some YulangClosure.NativeRelationInterner.Examples.key ∧
  (NativeRelationInternerReview.spoofedGhost.call NativeRelationInternerReview.blocked
        YulangClosure.NativeRelationInterner.Examples.key).snd =
    YulangClosure.NativeRelationInterner.Result.ok 0
'NativeRelationInternerReview.decoder_does_not_read_ghost_origin' depends on axioms: [propext]
NativeRelationInternerReview.cancelled_retry_constructs_exact_arena : (YulangClosure.NativeRelationInterner.Examples.physicalCancelled.store.arena
        [] []).relation
    YulangClosure.NativeRelationInterner.Examples.key =
  ((YulangClosure.NativeRelationInterner.Examples.physicalCancelled.call
              YulangClosure.NativeRelationInterner.Examples.retryResources
              YulangClosure.NativeRelationInterner.Examples.key).fst.store.arena
      [] [],
    0)
'NativeRelationInternerReview.cancelled_retry_constructs_exact_arena' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[exit 0]
```

## Cessation

At 2026-10-26T13:36:26.104328+00:00, accepted artifact hashes and the complete source cone were rechecked.
Every reviewer checker process had exited; no descendant or unresolved sublease
exists. This receipt is the only repository write. **WRITES STOPPED.**
Primary retains adjudication, integration, shared status and Git/push ownership.
