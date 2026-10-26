# Independent review: native drain stages and first boundary

## Review status

**PASS for both exact frozen source/note pairs as bounded local control
suppliers.** Independent direct checks and complete imported-origin audits
passed for `OriginalDrainStages` and `OriginalFirstDrainBoundary`. Their notes
accurately retain the distinctions between a finite projected event prefix,
original Rust extraction, the native active polling cut, and whole inference
termination. No blocking mathematical, kernel, or stated-scope correspondence
finding remains.

This verdict does not certify `OriginalDrainFrontier`, source-specific NQ,
source extraction, Replay/physical-history alignment or any of the four
whole-language closure goals. The initialization-cut limitation is material
and remains explicit below; the frozen First note acknowledges it rather than
claiming it was discharged.

This reviewer did not author either target. The exact write lease is this
review note and `/tmp/yulang-drain-stage-boundary-review/`; target sources,
paired notes, imports, shared cache, compiler code and Git remain untouched.

## Frozen reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalDrainStages.lean` | `9e116f95b8ed001485b2f6b699478c847a53420adb11c70b577b1c0f4e07d61d` |
| `notes/theory/2026-10-27-original-drain-stages.md` | `c2e5cacf8406d04792e7b72e103dbda32da0c4772cbf43e10886e90d1ca09611` |
| `notes/theory/lean/YulangClosure/OriginalFirstDrainBoundary.lean` | `d2c7096ff19b072fea0646b2ed12a4096e26ee03b31eb71997c64e9af43f0a1a` |
| `notes/theory/2026-10-27-original-first-drain-boundary.md` | `670ded719afe414e41776fa1265e42ab08328f69504ea2a1d57ff713549437c8` |
| `OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `NativeDrainOwnership.lean` | `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |

All four supplied source/note hashes were checked before their respective
review and after direct and audit checks. All 871 Stage Lean lines and its
complete 364-line note, then all 274 First Lean lines and its complete
168-line note, were read. The second target was not accessed until the parent
sent both frozen hashes and the actual imports-ready signal.
The review read the actual native declaration, initializer, frame preparation,
normal stage loop, all four structural dispatch functions, terminal driver,
legacy-route early return, relevant structured dispatch installation, and
Some-Replay error truncation.

## Stage mathematical claims

The central `Frame.Shape` invariant is derived from initialization and computed
updates. It is not a transition-constructor input or an assumed native success
certificate. `execute_valid` propagates it over a supplied finite list of
successful projected events. `initialized_boundary_is_transport` then uses
the unchanged `OriginalDrainBoundary.EmptyBoundary` predicate:

```lean
(executed : execute events initial = .ok state) →
(boundary : OriginalDrainBoundary.EmptyBoundary owner state.project) →
∃ frame rest, state.frames = frame :: rest ∧ frame.owner = owner ∧
  frame.core.index = rest.length ∧ frame.core.birth = owner.birth ∧
  frame.stage = .transport ∧ frame.core.current = none ∧ state.queue = []
```

The conclusion identifies the actual projected top frame, its original
birth/index owner, and its native stage. It does not existentially choose
another control state or replace the frozen boundary definition. The supplied
finite event list is execution evidence for this projection, not original Rust
trace extraction or accessibility of original inference.

`initialized_resume_same_frame` retains the entire supplied saved frame:

```lean
(initialized : execute history initial = .ok start) →
(held : saved ∈ start.frames) →
(returned : resume saved.owner events start = .ok last) →
∃ rest, last.frames = saved :: rest
```

The saved owner includes birth and index. Membership plus the derived stack
index invariant excludes identifying a distinct later top frame by slot alone.
`resume` stops when that owner reaches the top; exhausting its finite event
list sooner is an error. Its recursion on the list does not prove that a
nested native drain will return.

## Native correspondence: all fourteen stages

| Stage | Independently checked actual update |
| --- | --- |
| Transport | Current present: transport the mutable relation and enter Context. Current absent: settlement test precedes pop; installing an item retains Transport; empty/dirty retains Transport; empty/clean enters Diagnostics. |
| Context | Record successful Context consumption and enter Dispatch while retaining current. |
| Dispatch | Retain the actual structural continuation installed by dispatch; clear current only after testing all four continuation fields. |
| FunctionAdmission | Exhaustion first; otherwise admit the reverse-indexed child into pending and enter FunctionEnqueue. |
| FunctionEnqueue | Enqueue the retained pending work at the front before clearing pending and advancing the cursor; return to FunctionAdmission. |
| TupleAdmission | The same field-order behavior with the actual Tuple vector and admission owner. |
| TupleEnqueue | Pending enqueue precedes cursor advancement and return to TupleAdmission. |
| RecordAdmission | The same field-order behavior with Record child coordinates external to this projection. |
| RecordEnqueue | Pending enqueue precedes cursor advancement and return to RecordAdmission. |
| VariantAdmission | The same field-order behavior with Variant payload coordinates external to this projection. |
| VariantEnqueue | Pending enqueue precedes cursor advancement and return to VariantAdmission. |
| Diagnostics | Successful diagnostic body enters Acknowledgements with absent current. |
| Acknowledgements | Complete one pending acknowledgement, or enter ReturnReady when none remain. |
| ReturnReady | Prepare the actual destination/receipt operations, then remove only the top native frame and restore globals outside this projection. |

The native structural functions test `next == children.len()` before pending,
exactly as `structural` does. Both Admission and Enqueue stages invoke that
same function. The computed enqueue uses `pending` and therefore does not
replace the previously admitted relation with a fresh readback. `nextQueue`
places it at the front. The Function producer in Rust retains all four
Value/Effect children; this module represents their opaque task vector and
field control, while exact semantic child production remains a separate owner.

The model intentionally does not derive cursor validity, prepared/completed
acknowledgement consistency, task/port semantics, or child completion merely
from `Shape`. A malformed cursor or arbitrary semantic readback is not an
actual native execution certificate. The note states this overapproximation
and leaves native bounded arithmetic/resource/semantic guards to extraction.

Native `prepare_typed_drain_update` replaces the active frame by a clone with
the same current, stage and continuations while retaining the previous
allocation in undo storage. The top-index guards in normal preparation and
terminal removal justify the top-only frame writes at the represented cuts.
The suspended-frame theorem preserves an exact lower frame under every
successful event, including prepare, settle and return events. Transaction
rollback is not a normal event. `truncateFailure` correctly retains the oldest
saved frames in the reversed list and does not alter the queue; its shape
result requires validity of the particular pre-truncation state.

The apparent additional stage assignments in the legacy synchronous loop do
not supply a competing active candidate path: the enabled-candidate branch
returns to `run_candidate_typed_drain` before that loop. This was checked in
`constrain_live_item_with_inferred_entry`, not inferred from a search result.

## Settlement and event-boundary limitations

The native empty-worklist test is before `settle_candidate_intrusion`; dirty
and clean empty outcomes occur only after the call. `Poll.entry`, `settling`
and `returned` model cuts within that Transport arm rather than new native
stages. `settlement_starts_at_boundary` concerns the before-call state;
`boundary_enters_settlement` explicitly requires `Poll.entry`.

Two limitations matter for downstream use and were sent to the parent:

1. The coarse `EmptyBoundary` also holds at `Poll.settling` or `Poll.returned`
   when the queue remains empty. Stage/current validity alone cannot infer
   `Poll.entry`. A first-boundary history argument must supply that step.
2. `apply (.begin destination)` creates a Transport/current-none frame with
   an empty queue, and its seed enqueue is a separate event. The coarse
   `EmptyBoundary` consequently holds at that intermediate initialization
   cut, even though native `start_typed_drain` has not returned to its polling
   loop. A no-prior-boundary premise from global `initial` would pick that
   intermediate cut, not the later first active polling boundary after NQ's
   tau. A downstream application needs an appropriate active starting cut,
   a proved entry-program-counter frontier, or explicit native-cut alignment.

These are not contradictions of the Stage invariant or its bounded note.
They prohibit treating the event projection as an already extracted native
trace or treating every empty coarse state as an imminent settlement call.
The second target's frozen note explicitly records these distinctions and
does not claim that its global-initialization corollary is the native first
active polling boundary after tau. This is an accepted scope limitation, not
a missing premise silently discharged by the review.

`Bookkeeping` can overapproximate unrelated operations and receipts, but it
cannot mutate the queue, stack, current, stage or birth counter. No theorem
turns an arbitrary bookkeeping replacement into a `NativeDrainOwnership.Run`.
Likewise, immutable admitted-work identity and mutable transported relation
remain separate; their authentic relation to native work items must be proved
by extraction. The note makes those boundaries explicit. No typing-as-safety,
whole-call certificate or semantic cast is used to discharge the Stage result.

## First field-boundary proof

The second module imports the frozen Stage machine unchanged. It adds no
new events, native guards or successful-child assumptions. Its `EntryOnly`
predicate quantifies over every retained frame with the exact birth/index
owner and states `poll = entry`. Initially it is vacuously true; at the final
boundary the existing boundary witness supplies the actual frame.

`structural_entry` checks every branch of all four families. `update_entry`
covers all fourteen stages. `advanced_entry` retains the predicate under
replacement or removal of the top frame. The substantive `apply_entry`
argument covers every event: same-owner settlement is impossible before its
empty field boundary, and same-owner settlement return is impossible while
the derived poll is entry. Settlement of other owners and nested frames
remain possible. Bookkeeping and preparation cannot change the tracked poll.

`BeforeFirst` is the finite snoc closure of the actual existing `apply`
equality plus absence of the boundary in each before-state. It contains no
endpoint boundary, complete execution, child completion or semantic
preservation law. `before_entry` and `before_valid` propagate their initial
predicates along those computed steps.

The review independently inspected this complete first-cut type:

```lean
theorem finite_first_boundary {owner : Owner} {events : List Event}
    {start last : State}
    (computed : execute events start = .ok last)
    (ends : EmptyBoundary owner last.project) :
    ∃ earlier later cut,
      events = earlier ++ later ∧ execute earlier start = .ok cut ∧
      BeforeFirst owner start cut ∧ EmptyBoundary owner cut.project
```

It constructs a prefix of the supplied original event list. The induction
permits an empty prefix when the starting state already is the boundary;
otherwise it uses the actual first `apply` result and recurses on the tail.
An error branch cannot satisfy the supplied successful execution equality.
The assumption that the given endpoint is empty is explicit and conditional;
no claim of finding an empty endpoint in arbitrary inference is made.

The main settlement type is:

```lean
theorem first_empty_enters_settlement {owner : Owner} {last : State}
    (run : BeforeFirst owner initial last)
    (boundary : EmptyBoundary owner last.project) :
    ∃ frame rest,
      last.frames = frame :: rest ∧ frame.owner = owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ last.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle owner) last =
        .ok {last with frames := {frame with poll := .settling} :: rest}
```

The final poll is a conclusion, not a premise. `initialized_first_settlement`
combines it with `finite_first_boundary`, retaining the same event-list
decomposition and computed prefix. The proof derives `Valid` from the
unchanged initialization and propagates entry, then applies Stage's exact
boundary-to-settlement computation. It does not replace the actual final
frame by another frame having the same depth.

The frozen note's initialization section accurately limits the corollary:
the first empty field cut may be the `.begin`-before-seed cut. For a later
active cut, `before_entry` accepts an initial `EntryOnly` premise, but this
module does not produce that premise from active native state. The separately
assigned frontier producer is outside this review. Its absence does not
invalidate these conditional lemmas, and these lemmas do not conceal its
remaining obligation.

## Independent checks

The pinned toolchain is Lean 4.35.0, Lake 5.0.0-src+eb6cafb. All review checks
use no `-o`, one Lean thread, a 120-second timeout, and the already authorized
installed Lake path. The parent is the sole shared cache/build owner.

1. Direct frozen Stage source check, `-j1 -M1024`: **exit 0**, zero diagnostics.
2. Imported Stage all-origin audit, `-j1 -M1024`: **exit 0**, zero diagnostics.
3. Direct frozen First source check, `-j1 -M1024`: **exit 0**, zero diagnostics.
4. Imported First all-origin audit, `-j1 -M1024`: **exit 0**, zero diagnostics.

The actual direct check form was:

```text
timeout 120 /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 YulangClosure/OriginalDrainStages.lean
```

The second direct check substituted `OriginalFirstDrainBoundary.lean`.
The corresponding audit commands used the same executable, timeout and flags
with `/tmp/yulang-drain-stage-boundary-review/audit-stages.lean` and
`audit-first.lean`. No source or imported artifact was emitted by these checks.

The audit selects constants by `Environment.getModuleIdxFor?`, prints complete
types and transitive axioms, rejects every target axiom declaration, and rejects
any dependency beyond `propext`, `Classical.choice`, `Quot.sound`. It separately
prints all 28 Stage and 13 First authored theorem roots, whose imported
constant kinds were independently confirmed to be theorem declarations. No source-prefix proxy or producer audit
receipt was used as independent acceptance.

| Stage census category | Count |
| --- | ---: |
| Definitions | 340 |
| Theorem constants, including generated/private | 292 |
| Constructors | 46 |
| Inductives | 14 |
| Recursors | 14 |
| **All originating declarations** | **706** |

There were exactly 706 distinct begin/end audit pairs. All printed types were
free of ellipsis/elision artifacts, and the axiom counts independently match
the paired note:

| Actual axiom set | All declarations | Theorem constants | Authored roots |
| --- | ---: | ---: | ---: |
| none | 587 | 210 | 1 |
| `propext` | 97 | 60 | 11 |
| `propext`, `Quot.sound` | 18 | 18 | 12 |
| `propext`, `Classical.choice`, `Quot.sound` | 4 | 4 | 4 |

The complete names/types/axioms remain in
`/tmp/yulang-drain-stage-boundary-review/audit-stages.log`; the structured
inventory is `stages-manifest.json` in the same directory. A targeted source
scan of the target and its frozen control dependencies found no `sorry`,
`admit`, project axioms, `native_decide` or kernel-check bypasses.

Stage evidence hashes:

| Evidence | SHA-256 |
| --- | --- |
| `stages-direct.log` (empty successful log) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `audit-stages.log` | `1ef4b8c52c7c4b7f317ca31868995efbd0cc3392f6acbe91b9e94e505de5ab9c` |

The First census independently contains 57 originating declarations:
14 definitions, 35 theorem constants, 4 constructors, 2 inductives and
2 recursors. All 13 authored roots occur as theorem constants. There are
57 matching distinct begin/end records, no diagnostics or elision, and no
unexpected transitive axiom.

| First actual axiom set | All declarations | Theorem constants | Authored roots |
| --- | ---: | ---: | ---: |
| none | 34 | 23 | 2 |
| `propext` | 15 | 4 | 3 |
| `propext`, `Quot.sound` | 6 | 6 | 6 |
| `propext`, `Classical.choice`, `Quot.sound` | 2 | 2 | 2 |

The First authored names by exact axiom group are:

- None: `initial_entry`, `tail_entry`.
- `propext`: `structural_entry`, `replace_entry`, `before_trans`.
- `propext`, `Quot.sound`: `update_entry`, `advanced_entry`, `apply_entry`,
  `before_entry`, `before_valid`, `first_empty_enters_settlement`.
- All three standard axioms: `finite_first_boundary`,
  `initialized_first_settlement`.

These independently match the frozen First note. Its full types and complete
axiom lists are in `audit-first.log`; the separate authored type readouts are
`first-authored-types.log` and `stages-authored-types.log`. The full manifests
are `first-manifest.json` and `stages-manifest.json`, including every private
and generated originating constant. Both source scans found no proof holes,
project axioms or checker bypasses.

| Additional evidence | SHA-256 |
| --- | --- |
| `first-direct.log` (empty successful log) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `audit-first.log` | `60e1cbdb8ee7655955ddee46672ef77398b4f31bc883178e2a219909bac06fe9` |
| `first-manifest.json` | `219d5a2595ddd0f54875c0902c2e9e0c691f47b922baa0f5f7bbfe01609a9860` |
| `stages-manifest.json` | `3d8bc4ac3c3c64a8c77060011e49567b8596fdfbcbc87bdaef0eaf5303f8b5b8` |

## Final verdict and handoff

**PASS, bounded local supplier scope only.** Both exact frozen notes state
what their checked declarations prove and retain the materially open native
and source obligations. The review accepts the Stage shape/owner/saved-frame
invariants and the First finite-prefix/derived-entry lemmas. It does not turn
their supplied successful readbacks into authentic Rust traces, identify the
initialization field cut with a later active polling cut, or claim original
inference termination/NQ/soundness/principality/Effect hygiene closure.

Four of six combined direct/audit invocations were used; two remain unused.
No failed review invocation occurred. All checks are complete and all four
target source/note hashes remained unchanged. Only this review file and the
leased scratch directory were written. No target, compiler, build cache,
`.olean`, root import, Git or shared status was modified. This review is
frozen at the final hash handoff, and writes have stopped.
