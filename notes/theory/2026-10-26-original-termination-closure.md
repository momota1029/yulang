# Original inference termination: persistent raw-pair extrusion ownership

Date: 2026-10-26. Source baseline:
`99f18bdc54df8057f5a6d5d4bec5dc449336c234`.

**Result:** a checked native-cache projection proves that a successful changed
Value extrusion is published at most once for each raw endpoint pair in an
uncancelled history. The proof uses the existing native dispatch, retains the
whole request payload, and permits arbitrary generation, canonical-map,
Context, source-set and deferred-demand observations. This removes repeated
allocation for the same raw pair from the global supply problem.

**Original whole-inference termination remains OPEN.** This result neither
assumes nor derives a finite final row set or a finite future raw-pair supply.
Six bounded original-source probes returned; none established divergence.

## 1. Original claim and unchanged authority

The target remains `YulangClosure.SourceProblem.InferenceTermination`, defined
in `notes/theory/lean/YulangClosure/Contracts.lean:151–154`:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

The original supported source domain is retained, including untypable inputs,
recursive source definitions, polymorphic uses, Function/tuple/record/variant
structure and contextual effects. The target concerns inference execution,
not termination of the program being inferred.

The governing source remains
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, together with
the birth-level SCC correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md`. No algorithm, source
restriction, resource cap or semantic decision is changed here.

The new module is
`notes/theory/lean/YulangClosure/OriginalTerminationClosure.lean`. Its namespace
does not certify closure of the original contract. The module explicitly says
that it is a component of that obligation.

## 2. A stronger native guard than generation-sensitive completion

The earlier `NativeInferenceProgress` analysis correctly observed that
`pair_is_current` is sensitive to the processing relation and intrusion
generation. It does not follow that each newly admitted relation/generation
can allocate another extrusion of the same raw Value pair.

There is a second, persistent owner:

| Native source, at the baseline | Relevant behavior |
|---|---|
| `lib.rs:4381–4398`, `TypedPairMemo::Value` | The raw Value-pair memo retains `retained_extrusion_rewrite` separately from diagnostic completion. |
| `lib.rs:13507–13518`, `pair_is_current` | A current complete relation can suppress dispatch; this is the generation-sensitive guard. |
| `lib.rs:14459–14492`, `dispatch_live_item` | After duplicate and canonical routing, a retained raw-pair rewrite is reused before any body or new extrusion. |
| `lib.rs:14714–14761` | The changed extrusion branch records the raw pair, retains the replacement, enqueues the rewritten pair and returns. |
| `lib.rs:15275–15293`, `retain_candidate_value_rewrite` | Missing memos and conflicting targets reject; the same target is a no-op; an absent target is installed. |
| `lib.rs:15342–15369`, `record_typed_pair_admission` | Replacement updates direct witness/completion. It preserves retained diagnostic children and the retained extrusion target. |
| `candidate_intrusion.rs:388–425` | Reuse can activate old parent/copy groups under new source evidence without creating replacement rows again. |

This distinction is material. New relation identities and new generations
may repeat diagnostic/propagation work, but do not erase an already recorded
extrusion target for the same raw pair. Canonicalization can produce a
different raw pair; the theorem does not identify those keys.

The existing `NativeValueStructure.dispatch` is used unchanged. Its
`dispatch_body_iff` exposes the exact native precedence. In candidate mode,
entry into any body requires an absent retained rewrite. A saved target can
instead lead to duplicate, canonical or retained routing, depending on the
earlier guards. No theorem here forces the retained branch when the duplicate
or canonical branch has priority.

## 3. Checked declarations and exact premises

`ValueMemo D` represents the rewrite coordinate and the diagnostic update
payload, namely the direct-witness/completion part. Other native fields are
outside this projection. `recordAdmission` preserves the old rewrite when
replacing a memo. `recordRewrite` transcribes the native missing/conflicting/
same/new cases. The main persistence results are:

```lean
recordAdmission_retained :
  retained (recordAdmission store pair diagnostic) = retained store

recordRewrite_exact :
  recordRewrite store pair target = some after →
  retained after pair = some target ∧
  (∀ key, key ≠ pair → retained after key = retained store key) ∧
  (∀ key old, retained store key = some old →
    retained after key = some old)
```

The imported native routing is connected directly:

```lean
retained_excludes_body :
  routing.candidate = true →
  routing.retained request.pair = some target →
  dispatch tables routing request ≠ .body body

fallback_requires_unwritten :
  routing.candidate = true →
  dispatch tables routing request = .body (.fallback operation) →
  routing.retained request.pair = none
```

`retained_excludes_context_fallback` applies the same exclusion after the
actual `NativeValueStructure.afterContext` function. It does not skip Context
or treat discharge as a completed Value body.

`RewriteState.births` is a proof-only log of successful **changed-extrusion
publications**. It is not a preallocated table or a native work cap.
`RewriteStep` contains replacing admission, projection-preserving events and
changed publication. A changed publication requires the actual imported
dispatch equation, candidate mode, agreement of the observed retained map,
a different target, and a successful exact retained-write equation. The
dispatch observation can precede the intervening diagnostic admission:
`recordAdmission_retained` proves that the relevant map is unchanged across
that admission. No stale current-pair completion assumption is needed.

The history theorems establish:

```lean
changed_extrusion_parents_nodup :
  RewriteRun RewriteState.initial s →
  (s.births.map Prod.fst).Nodup

changed_extrusion_targets_persistent :
  RewriteRun RewriteState.initial s →
  ∀ pair target, (pair, target) ∈ s.births →
    retained s.store pair = some target
```

`prior_changed_extrusion_excludes_later_body` then feeds that persistent
target back into the imported native dispatch for every later request with
the same raw pair. The later current-pair predicate, canonical map, levels,
Context, source set and deferred demand may differ. Their actual earlier
routing branches remain intact.

All eleven authored theorem roots are:

1. `recordAdmission_retained`
2. `recordRewrite_exact`
3. `retained_excludes_body`
4. `retained_excludes_context_fallback`
5. `fallback_requires_unwritten`
6. `rewrite_initial_valid`
7. `rewrite_step_valid`
8. `rewrite_run_valid`
9. `changed_extrusion_parents_nodup`
10. `changed_extrusion_targets_persistent`
11. `prior_changed_extrusion_excludes_later_body`

Their fully qualified prefix is
`YulangClosure.OriginalTerminationClosure`. Complete printed types and
transitive axiom lists are retained with the assignment's checker receipt.

### Boundaries of this projection

The result is about successful changed-extrusion publication, not every
attempted call to `candidate_extrude` and not every row allocated before a
failure. It does not assume that the extrusion callback succeeds. A native
successful publication supplies that event; a failed private attempt is a
different terminal/error path.

Rollback removes newly created typed pairs and restores journaled old memos
(`lib.rs:9796–9810`; `candidate_intrusion.rs:465–500`). It is deliberately not
an event of `RewriteStep`. An arbitrary externally repeated cancel/retry can
repeat physical work and is not excluded by this theorem. Applying the result
across native checkpoints requires the actual committed/private-attempt
history extraction. That extraction is not declared proved.

The whole native graph is also not a field of `RewriteState`. In particular,
this relation is not substituted for `inferStep`, and its `unchanged` event
must not be used to argue global accessibility. The no-duplication conclusion
is a finite-prefix invariant, not a well-foundedness result.

## 4. Ordinary Context callbacks enqueue; retained restoration nests drains

A source call-chain audit narrows a separate part of the progress problem.
The ordinary closure passed to `candidate_zero_word_filters` by
`candidate_context_execute_relation` is at
`candidate_context.rs:3827–3885`. Its branches call
`candidate_apply_effect` or `candidate_replay_bound`.

`candidate_apply_effect` (`candidate_extrusion.rs:1147–1177`) either returns,
inserts/replays a row bound, or calls `candidate_check_effect_operand`
(`candidate_effect.rs:1237–1313`). The latter enumerates the actual finite
support members/tail, enqueues children, reports a conflict, or rejects. It
does not synchronously execute those children.

`candidate_replay_bound` (`candidate_extrusion.rs:1070–1112`) drives each
generated replay operation with **`provenance = None`**. That branch of
`candidate_context_consume_replay_child`
(`candidate_context.rs:4186–4200`) enqueues a child. Once every child has been
queued while some remain outstanding, `candidate_context_drive_replay`
(`4206–4227`) returns `Queued`. The enclosing worklist consumer owns completion.
This call chain does not recursively invoke `step_typed_drain` for each
ordinary Context filter before publishing its discharge.

The synchronous/nested branch is real, but different: retained restoration
passes `Some((occurrence, cause))` and steps its owned child drain through
`candidate_context_step_replay_child` (`4097–4184`). FreshUse restoration must
still be included in the global transition system. The saved
`checking_filters` scope and discharge-after-callback order are preserved;
the audit does not move publication earlier.

This is source evidence about the actual call chain, not a new Lean theorem
that every native callback or drain completes. It avoids assigning an
unobserved recursive drain edge to the ordinary filter closure.

## 5. Bounded source search and a rejected false lead

The primary supplied the unchanged `yu-playground` binary built from the
baseline. Six probes used only inference and graph observation, each with a
20-second wall/CPU bound and a 1-GiB address-space bound. All returned exit 0,
in approximately 0.7–1.3 seconds. The source cases were:

| Case | Source feature |
|---|---|
| `nested-recursion` | Original `my loop x = { my helper y = loop y; helper x }`. |
| `nested-tuple` | Recursive call changes its argument to `(y, y)` through a local helper. |
| `self-application` | `my self x = x x; my answer = self self`. |
| `recursive-helper` | `my loop x = { my helper y = loop (helper y); helper x }`. |
| `effect-bridge` | The actual annotated higher-order source from `candidate_context_tests.rs:4145`. |
| `effect-bridge-scoped` | The same source with the native scoped experiment enabled. |

Full source, output, exact arguments, statuses, limits and hashes are retained
under `termination-closure-r3/`, with the summary in `native-probes.json`.
No timeout, nontermination, source restriction or universal inference theorem
is inferred from these observations. The CLI's graph-display/scoped limits
were not used as a semantic termination argument.

One apparent cycle was specifically rejected. `Work::EffectView` does create
a fresh view even when its tail is unchanged (`candidate_extrusion.rs:337–370`;
`candidate_effect.rs:859–908`). But original signature construction puts those
views behind EffectRow ports (`candidate_effect.rs:2161–2296`). A row already
at the target level is reused before its bounds are followed
(`candidate_extrusion.rs:102–108`). The next whole-Value extrusion therefore
does not necessarily revisit that view. No source-reachable repeatable cycle
was constructed from this observation.

## 6. Application to the original global obligation

The new result removes the following proposed source of unbounded births:

> Arbitrarily many different relation contexts or merge generations can
> force fresh changed extrusions for one fixed raw Value endpoint pair.

The native cache prevents that behavior within the stated uncancelled history.
The remaining allocation supply problem is now **new raw endpoint pairs**,
including those created by source FreshUse, new Value structures/rows and
canonicalization after merges. That is a strictly different obligation from
generation-sensitive repeated completion.

A possible structural argument must use the native difference between active
bound replay and silent extrusion parent links. The parent link is inserted
inside `candidate_extrude` without immediately replaying every opposite bound;
selected copied bounds are installed in the lower-level copy. Incoming
allowance restoration has its own explicit final replay. It is therefore
plausible to separate finite high-level core events from demands involving
new lower-level rows. It is **not yet proved** that this separation survives
all mixed old bounds after level-lowering merges, capture-incidence callbacks
and source FreshUse. A bare decreasing parent/copy level is insufficient.

The exact next global theorem must derive finite demand/copy ancestry from
the original source schedule and these native constructors. It must not take
a finite final row count, future event supply or total-drain transcript as an
assumption. After that, generation-sensitive relation completion, exact
Context/Replay supply and nested retained-drain return order must be composed
into the original `Acc` conclusion.

The repository currently has no concrete assignment to `inferInitial` or
`inferStep`; only the abstract `SourceProblem` fields and separate owner
projections exist. A faithful whole state must join the source action cursor
and active-use stack, live graph/captures, term and row stores, levels and
representatives, pending intrusion parents, complete relation keys/memos,
Context tables, scoped identities, worklist, replay operation cursors and
typed-drain stack. This missing composition is an implementation/proof task,
not evidence that the original mathematical claim is false. This packet does
not substitute an always-enabled abstraction for that original machine.

## 7. Validation status

Validation uses the pinned Lean 4.35.0 toolchain, `LEAN_NUM_THREADS=1`, project
arguments `-j1 -M1024`, an isolated baseline project and a 120-second limit per
focused checker invocation. No shared `.lake`, compiler, configuration,
root-import, central status or Git mutation was made by this worker.

The exact final theorem/declaration census, complete axiom lists, failures and
repairs, source/dependency hashes, timing and frozen artifact hashes are in
`tasks/agent-loop/inbox/20261026-original-termination-closure-r3.md`. Kernel
acceptance, source correspondence, independent review and whole-language
termination remain separate judgments. The result is not self-certified.
