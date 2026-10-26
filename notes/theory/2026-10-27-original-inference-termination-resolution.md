# Allocated-prefix Replay ownership for the original termination problem

Date: 2026-10-27. Baseline supplied by primary:
`6148fc868565617d7db6ef193a6ff164700d88f7`, branch `yulang3`.

Status: **25 authored Lean theorems checked; independent review pending.**
The new result proves the allocation-chronology component of the native
first-empty obstruction. It does not prove or refute original inference
termination. No compiler, algorithm, source envelope or error policy changes.

## 1. Original target and the decisive existing obstruction

The target remains `YulangClosure.SourceProblem.InferenceTermination` in
`lean/YulangClosure/Contracts.lean`:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

It includes supported untypable input and concerns inference, not termination
of the program being inferred. The 2026-10-11 top-level inference principles
and the 2026-10-24 birth-level induced-SCC correction remain unchanged.

The earlier `OriginalTerminationClosure` result excludes repeated changed
extrusions of the **same raw pair**. It does not bound new receiving rows.
`FiniteCopyClosure` already derives a fresh-receiver cycle from ten explicit
closure clauses. More decisively, the independently reviewed
[native first-empty obstruction](2026-10-26-native-copy-quiescence-obstruction.md)
proves NQ for the actual
[stale-bound source](fixtures/2026-10-26-stale-bound-annotated.yu), from the
concrete cut immediately before trace event 1229. NQ is an existing manually
reviewed source-code result, not a new theorem of this packet.

Its key chain retains `B48 -> J21 -> C20 -> S47`, the low path
`S47 -> 39 -> 32 -> A45`, `C20.lower T276`, `A45.upper U301`, and copied path
`65 -> 68 -> 69 -> 47` with actual relation fibers. Until a first empty
Transport boundary there is no next settlement. A completed anchored copy
therefore forces an anchored copy with a strictly newer negative-row ordinal
at any proposed finite empty boundary. The finite maximality contradiction
excludes that boundary.

This obstructs a proof route which promises finite **successful** closure of
every unchanged native drain. It does not by itself refute a finite bound on
allocation in all executions: actual errors, including checked identity or
allocation exhaustion, can terminate a drain. Nor does absence of a finite
normal boundary alone prove an infinite chain. Availability, progress, the
original supported-source instance and the concrete `inferStep` simulation
remain separate obligations. Neither a machine-size bound nor a new fuel
parameter is used to rename this gap as original termination.

## 2. What the new module actually constructs

New module: `lean/YulangClosure/OriginalInferenceTerminationResolution.lean`.
Its namespace is `YulangClosure.OriginalInferenceTerminationResolution`.
The filename does not denote closure of the original parent.

One event history owns the following data:

| Data | Construction and exact boundary |
| --- | --- |
| Value and Effect rows | Separate level vectors in one `Rows` state. A successful native append adds one row of the selected kind; the new ordinal is the old length. The native `u32` representability guard is retained. It is not used as a termination argument. |
| Term cells | Raw term identities with immutable readback. The existing `TermView` retains all four Function ports, ordered tuple elements, record labels/optionality, and variant payloads. No two-port replacement of a Function is made. |
| Term publication | A fresh raw ID and independently established producer formation: directly mentioned rows already exist; every referenced term child already exists; a scalar/row leaf cannot disguise a structural endpoint. |
| Relation admission | Calls the existing physical `NativeRelationInterner.Native.call` unchanged. Context bounds, Value/Effect scoped guards, resource checks, reuse and partial effects on error remain its actual code. Successful output records the same returned raw RelationId and complete `NativeValuePorts.Key`. |
| Other scoped allocation | The existing `Native.inventory` event retains interleaved ScopeInventory charges and their actual checked arithmetic/65,536 limit. The chronology argument does not use that limit to prove termination. |
| Replay publication | Retains child/lower/upper RelationIds and complete decoded keys, plus both real bound-key kinds (`NativeValueStructure.ValueBound` and `NativeMergeExpansion.Bound`). It requires previously admitted relation records and allocated bound endpoints. It does not require any child completion. |
| Level-only updates | Preserve both row counts. This allows earlier source-level/merge updates in the chronology projection without claiming that arbitrary updates implement the merge algorithm. No row identity is removed or reused. |
| Failure | Real relation-call failure is recorded, including partial interner state. Explicit row-allocation failure is a terminal projected outcome. `failure_has_no_step` excludes treating that failed attempt as a normal continuation. |

Term interner reuse is an unchanged cell lookup and can erase to zero events.
The projection records successful term publication, not a complete resource
semantics for all term allocation failures. The row-failure event abstracts
possible reservation failure and does not assert that one must happen.

**Producer formation is not an invented runtime guard.**
`term.rs::live_variable(kind, polarity, ordinal)` interns the supplied ordinal
without checking it against the inference row vectors. Function constructors
check term child kinds/polarities, but those checks do not prove the row
allocator's ownership invariant by themselves. Consequently the local
`Cell.Formed` and `PairAvailable` inputs are explicitly the remaining native
producer correspondence obligations. They are neither assumed completion nor
the desired copy-successor law. This packet derives history-wide allocated
prefix validity from those local publication events.

## 3. The checked chronology argument

`TermUses cells id row` is a finite syntactic reference path, crossing the
actual term children of either row kind. `term_uses_before` proves that an
old immutable term cannot acquire a path to a newly allocated row through a
child that was previously absent. Every child was present at publication,
and every later cell readback preserves the old cell. This handles the
structural interner: using the same term ID cannot turn an old Function into
a Function with the newly allocated argument.

`history_valid` derives row/term/relation/Replay formation from the initial
empty history. No final graph size, final set of demands, a successful drain
or an old Replay completion is supplied. `history_native_readback` separately
constructs the existing `NativeHistory` for the physical interner and proves
that every recorded admission still reads back to its **entire** stored key.
It uses the checked old-relation readback and same-ID uniqueness results.

The main theorem, with implicit types omitted here only for readability, is:

```lean
earlier_replay_excludes_later_row
  (history : History before) (run : Run before after)
  (published : replay ∈ before.replays)
  (later : ¬ Available before.rows row) :
  ¬ PairUses after.cells replay.child.key.pair row ∧
  ¬ PairUses after.cells replay.lowerInput.pair row ∧
  ¬ PairUses after.cells replay.upperInput.pair row
```

The actual raw-ID bridge is:

```lean
earlier_replay_id_excludes_later_row
  (history : History before) (run : Run before after)
  (published : replay ∈ before.replays)
  (later : ¬ Available before.rows row)
  (readback : after.native.store.readback replay.child.id = some key) :
  ¬ PairUses after.cells key.pair row
```

`earlier_replay_cannot_read_fresh_request` applies this to the real complete
`NativeValueStructure.Request.key`; its context, source set, transformer and
deferred demand are preserved. It concludes that the older child ID cannot
read back to that fresh-row-bearing request. The two NQ-specific corollaries
exclude an earlier child whose exact pair is `T < N`, and an earlier child
whose lower endpoint is `F_N`, when its stored positive Function argument
reads the fresh row `N`. `positive_function_uses_argument` supplies the latter
reference path directly from the existing four-port `FunctionTerms`.

For NQ §5.3, take `before` at the start of the current typed child drain.
An outer suspended restoration product was published before that cut.
Each distinguished `N` is allocated later. The theorem excludes that outer
product as an owner of the exact fresh child, including through raw
RelationId equality. A matching old dependency must therefore come from a
later owner once the concrete native history extraction is supplied. This
does **not** yet prove that later owner's Replay loop queued every child.

## 4. Minimum missing operational join for the full NQ theorem

The existing Lean projections do not yet compose to NQ. In particular,
`NativeDrainOwnership.dispatch` records an externally supplied dispatch exit;
it does not execute extrusion or install its bounds. `NativeValueDrain`
constructs staged child admission/enqueue, while `NativeReplayCurrent` covers
the Effect operand graph. `FiniteCopyClosure` still assumes its selected copy
and closure laws. Supplying those laws again would restate the missing result.

The minimum faithful join needs these owners:

1. **Native allocator/term/source producer:** extract the local row/term/Key
   formation events above from the actual batch, current source actions and
   `candidate_extrude` callers. Include prior merges without row reuse.
2. **`candidate_extrusion.rs` operation machine:** encode `Visit`, `Function`,
   `Bound`, operation-local signed row/structure memo, saved selected side
   lengths, pending bound stack, low-row reuse and transported actual fibers.
   Derive the copied `B->J->C->S` path, not a supplied `copiedUpper` clause.
3. **`candidate_context.rs` Value Replay:** join exact BoundKey fibers, both
   head-delta products, dependency interning, ordinary `None` provenance and
   suspended restoration ownership to the same queue. The new chronology
   theorem removes the old-suspended-product alternative; the actual later
   queue ownership remains to be proved.
4. **`lib.rs` dispatch and memo:** retain the exact raw pair, generation and
   processing relation; connect real retained-rewrite publication to its
   original extrusion event; include all staged four-port Function children.
5. **Shared drain/settlement control:** distinguish Transport with empty queue
   and no current item from an empty queue during admission/enqueue. Prove
   that a first such boundary has dispatched every previously queued child,
   while all error outcomes remain explicit. This derives the successor at
   the hypothetical boundary and permits finite maximality without fairness.

After NQ is kernel-checked, original `Acc` still requires the independently
selected whole inference transition system, supported initialization and
nonstuttering source/native correspondence. The branch currently supplies no
concrete original `inferInitial`/`inferStep` instance. This packet neither
chooses a new algorithm nor deletes native availability errors.

## 5. Verification and complete authored-theorem axiom audit

Pinned executable used:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Observed versions: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb`. Parent owns all `.lake` builds. No worker build, `.olean`
output, root import change or shared cache write was requested.

Actual checks used `lake env lean -j1 -M1024` on the leased file, and then on
`/tmp/yulang-termination-audit.lean` with `--root=/tmp`. The latter contains
the exact new source plus `#check @...` and `#print axioms ...` for every
authored theorem. Final checker and all 25 audits exited 0. The full default
project and native compiler were not run by this worker.

Material failures retained in the session: direct execution in the default
sandbox returned `failed to locate application` for both version/check
attempts; the authorized fixed Lake executable worked with reviewed
escalation. The first real proof check failed on five elaboration issues
(an Effect-row simplification, an implicit term ID, constructor binder order,
and two unreduced call matches). Those were repaired; no mathematical
counterexample or theorem weakening was used. Subsequent module and audit
checks succeeded.

Every theorem below has the namespace prefix
`YulangClosure.OriginalInferenceTerminationResolution`:

| Complete axiom list | Authored theorem names |
| --- | --- |
| `[]` | `available_mono` |
| `[propext]` | `cell_formed_mono`, `term_uses_available`, `term_uses_before`, `value_available_mono`, `effect_available_mono`, `pair_available_mono`, `publish_extends`, `run_trans`, `failure_has_no_step`, `positive_function_uses_argument` |
| `[propext, Classical.choice]` | `value_uses_prior_allocation`, `pair_uses_prior_allocation` |
| `[propext, Quot.sound]` | `step_extension`, `step_valid`, `run_extension`, `history_valid`, `step_admissions_keep`, `run_admissions_keep` |
| `[propext, Classical.choice, Quot.sound]` | `history_native_readback`, `earlier_replay_excludes_later_row`, `earlier_replay_id_excludes_later_row`, `earlier_replay_cannot_read_fresh_request`, `earlier_replay_cannot_target_fresh_value`, `earlier_replay_cannot_have_fresh_function` |

No `sorry`, `admit`, project axiom, native-evaluation assumption or kernel
bypass occurs in the new source. Complete final type/axiom output is
`/tmp/yulang-termination-audit.log`, SHA-256
`db35955d66a77786b12a8da1a0b47b05d64750c2d5e4f4021201cd67729ba648`.
The copied audit source is the only other worker scratch file.

## 6. Frozen dependencies and scope

| Input | SHA-256 |
| --- | --- |
| `2026-10-26-native-copy-quiescence-obstruction.md` | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `fixtures/2026-10-26-stale-bound-annotated.yu` | `f617815f862683495c3e8d040f4b378f14573cf1ef730a764ff254d748f07a84` |
| `lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `lean/YulangClosure/NativeValueStructure.lean` | `81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc` |
| `lean/YulangClosure/NativeRelationInterner.lean` | `1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

The Lean artifact SHA-256 is
`a89a316ea72e472b0e2c09effc144730dc4c683228008caf42a433d0a969a6dd`.
Only this note and that leased Lean module were written in the repository.
No Git operation, compiler edit, child worker, dependency change, shared
record edit or pending-question write was made. Original source/native
extraction, full NQ, all-context effect-view reference coverage, rollback,
global termination, and independent review remain open.
