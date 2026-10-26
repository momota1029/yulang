# Native Value ports r4 — independent frozen review

Reviewer: `/root/dictionary_denotation_review_r4`, fresh non-author for this
packet, using the inherited generic worker. No unavailable custom role is claimed.
Producer: `/root`. Review date: 2026-10-26.

## Verdict and severity

**ACCEPT**, for the exact frozen mathematical constructor and two-stage dispatch
scope described below. **Blocking: 0; major: 0; required minor: 0.** No material
counterexample or hidden child-completion hypothesis was found in that scope.
This acceptance does not close original inference soundness, native binary
refinement, complete callable semantics, or production promotion.

The producer stopped at `2026-10-26T11:54:23.588939+00:00`. Supplied baseline:
`8472a1ca49da055a1ea298ccfa87745c2a6f5ce4`; supplied integration head: `9778835`.
The reviewer ran no Git command and does not independently attest Git ancestry.
The reviewed bytes are identified by the following hashes, all checked against
the live repository and the frozen manifest.

| Frozen output | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeValuePorts.lean` | `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` |
| `notes/theory/2026-10-26-native-value-ports.md` | `4f39788f4dee30f5f413b0b373965ea583892b7d07e5b95de63ccb93f2819b5b` |
| `tasks/agent-loop/inbox/20261026-native-value-ports-r4.md` | `4bf5ca54883da9be52ff5e65b4d74ce7841997b23bef5430ca3551cf0bd3b27e` |
| Producer `freeze.json` | `5defb8705feb6b5f816b43427c16e4372e4f81a85f291a67dc0bc92684acf357` |
| Final root-check log | `df8c7a9a46170b68f4747ad7787138734d9fd71c5e49834337d53963b3746139` |
| Complete originating census log | `e801f97f2ae5e77505eb87751fc4c09b0d9fd5fd0132d8abb6052f7b9fc3ae22` |
| Complete census audit source | `8fe2c1bcc66b4f88876e1184f319794b42aa0dfc0d348c3d11e69fcbd208721a` |
| Required authored-root manifest | `11457c00d0f05d965d39755b639ea797ddb7d0bb988d0063d0adae44b8e40aff` |

Producer scratch root:
`/workspace/scratch/f98087c7ac1a/value-ports-r4`.
Reviewer scratch root:
`/workspace/scratch/f98087c7ac1a/value-ports-review-r4`.

## Original claim and application

The governing original claim is `SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The same original scope, supported source domain, shared witness, optional records,
method selection, complete Call/effect/generalization meaning, and fixed Value
birth-level qualification remain required. The original operating/proof-closure
instructions, design authority, current task state, Lean skill and source map
were read. The immediate parent is the Value child construction after the Context
stage described in `2026-10-26-native-context-expansion-construction.md`, sections
1, 5 and 7. That prior packet passes the entire `ValueRequest`; it does not supply
the Function/Tuple/Record/Variant children constructed here.

This packet supplies actual finite child vectors, complete decoded child keys,
their newly allocated Context/transformer readbacks, their port dependencies,
and the admission/enqueue history. Its output can replace an assumed structured
child list in the shared native history bridge. It does not provide the history's
authentic input projection or the source interpretation. The original parent
therefore remains **OPEN**.

## Source correspondence checked

The entire 1,063-line Lean module, the construction note, relevant complete
theorem types, and the actual Rust owners were inspected. The following source
hashes agree with both the frozen source copy and current repository bytes:

| Native source | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |

| Concrete owner | Reviewed correspondence and consequence |
| --- | --- |
| `lib.rs` endpoint definitions; `candidate_context.rs` scoped demand/key definitions | Every Value endpoint constructor and polarity, Tuple arity, all seven Effect endpoints, Context, optional source-set, transformer and all five demand fields survive in the decoded representation. Canonicalization renames row IDs only. Physical `ScopedFlowId` encoding is explicitly residual. |
| `candidate_context.rs` Context interning/assertion, local source weight, and post-check Context | Context ID 0 is identity; allocated IDs are one-based. Every node input is an earlier existing ID under `ContextsFormed`. The actual supplied post-check ID is used. An Effect upper Allowance alone supplies the local prefix. A missing readback is not silently treated as an existing view with no weight. |
| `candidate_context.rs` Function admission | Local prefix allocation precedes inherited Context construction. Argument and ArgumentEffect swap the inherited Context, except identity; the local Prefix remains outside that swap. The four fields determine Swap/Preserve and retain exact port dependencies, with optional Derived additional. |
| `candidate_context.rs` Function flow; `candidate_scope.rs` stamp/protect constructors and evaluation | Incoming Function transformer must be identity. A deferred demand must match the parent's actual negative Function root. It is consumed in the child flow; the parent receipt retains Call/use/root/scope/input. ArgumentEffect stamps the input; ResultEffect protects the output scope iff the original input is absent. Value ports receive identity flow. Existing protections/inputs and all other scopes are preserved exactly as the relevant pointwise theorems state. |
| `candidate_context.rs` relation guards and structural admissions | Value/nonidentity-transformer, Effect/deferred-demand, and nonidentity Effect self-relation guards match. Tuple/Record/Variant preserve the entire parent flow and source set; their ports retain original indices. |
| `lib.rs` Function child builder | Exactly four children in native order: Argument, ArgumentEffect, ResultEffect, Result. Both argument ports are contravariant and both result ports covariant. Raw term endpoint readbacks are supplied as data; they are not predicates assuming safety. |
| `lib.rs` Tuple child builder | Both advertised arities and both actual vector lengths are checked. Successful output covers every matching position, with no truncated zip masquerading as complete coverage. |
| `lib.rs` Record child builder; `NativeRecordPlan` | Lower name lookup uses its first occurrence. Missing optional upper slots retain their original target positions; missing required fields and optional-to-required mismatches keep their distinct outcomes. No partial children escape a failure. The `(0,1)` witness verifies the missing-optional position rather than renumbering it. |
| `lib.rs` Variant child builder | Every upper entry with matching tag and payload length remains a separate requirement; duplicate keys are not deduplicated. Payload order and all three indices agree. The first unmatched lower alternative yields its diagnostic and discards any earlier built prefix. `Except.error` is that diagnostic, not a Rust availability-failure assertion. |
| `lib.rs` four child steppers and `enqueue_item` | Each step selects `children[len - 1 - next]`. Admission stores a pending receipt; a later step enqueues that same receipt, clears pending and increments. `enqueue_item` with a supplied relation preserves the original raw task and uses front insertion. Reversing traversal plus front insertion restores original source order. Child jobs carry `replayAck = none`. |

The enqueue owner was inspected beyond the four steppers to resolve the concrete
risk that enqueue might recanonicalize, deduplicate, or replace a supplied child
task. In this path the relation is already supplied and raw-task retention agrees
with `Work.native`. Allocation/resource failure remains outside the mathematical
success domain.

## Premises, output strength and attempted counterexamples

`YulangClosure.NativeValuePorts.admit_constructs` quantifies over arbitrary
arenas, fixed raw readback/canonicalization functions, the same complete parent,
the supplied post-check ID, Derived flag, child and receipt. Its sole premise is
the actual equation `admit ... = some (after, receipt)`. Its conclusion constructs
`arena.Extends after` and every field of `AdmissionResult` in that same `after`:
canonical pair, sources, parent, port, Derived, Context order/readbacks, complete
Flow meaning, guards and registered complete child key. There is no semantic
child-typing premise or completed-owner premise.

`YulangClosure.NativeValuePorts.drive_success_readback` quantifies over the same
raw functions, parent/post/Derived, original children/queue/arena, fuel and final
cursor. Its sole premise is successful computed `drive` from `initialCursor`.
It derives `pending = none`, a single list whose source projection is exactly
the original children, exact final queue equality with the old tail, every full
`AdmissionResult` in the same final arena, and no Replay ACK on any job. Successful
finite computation is a local constructor condition; it is not semantic acceptance
of the children. The theorem does not assert unconditional termination or impose
a new native/source time bound.

`dispatch_step_valid` starts from the actual inductive admission/enqueue step and
one common cursor invariant. The invariant's initial case is constructed; it is
preserved through arena extension, including already completed receipts. Pending
receipts are tied to the current reverse-traversal child. End-of-vector pending
absence and final source order are conclusions. No second favorable job list or
unrelated per-stage parent is substituted.

The malformed Context risk is real for an arbitrary mathematical arena/post ID:
such an argument need not satisfy the Rust `assert_context`. The packet makes
that boundary explicit. `build_context_formed` assumes a formed arena and
`post ≤ contexts.length`, then proves formation and the resulting ID bound.
The generic `drive` theorem does not claim these premises for arbitrary inputs.
The corrected witness starts with actual Context ID 1, an existing parent and a
formed arena; its old unallocated ID 55 is not final evidence. The prefix/swap
example constructs `[without 0, prefix 7 0, swap 1, prefix 7 3]` and result ID 4.
This is consistent with native chronological allocation and earlier-ID formation.

Other concrete attacks inspected were truncated Tuple payloads, missing optional
Record positions, duplicate upper Variant requirements, the first missing Variant
after a successful prefix, nonidentity incoming Function flow, mismatched demand
root, local Prefix placed inside Swap, premature queue insertion, lost raw tasks,
and fabricated Replay acknowledgements. The definitions/theorems and native
branches agree on these cases within the stated success/readback domain. No new
counterexample to the original source theorem is claimed.

## Independent evidence reconciliation

The independent parser verifies **406 SHA-256 comparisons**: all 3 frozen outputs;
15 live read inputs and their 15 frozen copies; 150 live project sources and their
150 isolated copies; all 40 frozen receipt files; the root manifest; audit program
and audit snapshot; 3 final module copies; the census log; and all 13 per-call logs
plus all 13 per-call source snapshots. It also checks exact manifest agreement,
balanced unique census blocks, exact module inventory/trailer, all authored roots,
complete type blocks and exact transitive axiom markers. The reconstructed records
equal the producer's complete `census-records.json`.

| Inventory | None | Only `propext` | `propext` + `Quot.sound` | Total |
| --- | ---: | ---: | ---: | ---: |
| All originating declarations | 705 | 161 | 25 | 891 |
| All originating theorem constants | 235 | 88 | 25 | 348 |
| Authored roots, a subset of those theorems | 4 | 28 | 24 | 56 |

No `Classical.choice`, project axiom, `sorryAx`, unchecked native-evaluation axiom
or kernel bypass occurs in these transitive results. The source hole scan is
supplemental: `admit` is the named mathematical admission function/constructor,
not a proof-hole tactic. The originating audit covers private and generated
declarations, not only the 56 convenient authored names. No UTF-8 replacement,
omitted-type ellipsis, error or warning occurs in the complete final census.

Pinned toolchain evidence is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake 5.0.0-src+eb6cafb.
The producer used 13/20 allowed calls; successes were 07, 10, 12 and 13. Failed
01–06, 08–09 and 11 and all their snapshots remain intact. Only the final-source
12 and 13 are final proof evidence; both exit 0 without warnings. Their exact
commands/resource receipts are frozen in `logs/12-final-port-roots.json` and
`logs/13-originating-census.json` and copied into the review integrity receipt.

Final complete census command, cwd `value-ports-r4/project`:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 AuditNativeValuePorts.lean
```

Final root check invokes the frozen `check_lean.py` using that exact Lake,
`--project /workspace/scratch/f98087c7ac1a/value-ports-r4/project`, `--timeout 115`,
`--module YulangClosure.NativeValuePorts`, and the exact 56 repeated `--theorem`
arguments listed in the checked JSON receipt. Every Lean process used one thread
and 1024 MiB; the wrapper aggregate ceiling was 1280 MiB, outer timeout 119 s.
Final call 12 took 13.005619 s; call 13 took 2.610077 s. Producer total recorded
checker time was 89.861396 s; peak aggregate RSS was 1,179,955,200 bytes.

The reviewer used **0/2 Lean calls**. Existing complete frozen receipts resolved
the checker risks; no redundant smoke build or budget increase was needed.
The independent substantive verification command was:

```sh
PYTHONDONTWRITEBYTECODE=1 TMPDIR=/workspace/scratch/f98087c7ac1a/value-ports-review-r4/tmp python3 /workspace/scratch/f98087c7ac1a/value-ports-review-r4/review_integrity.py
```

Its final exit is 0. The first reviewer parser execution exited 1 because Lean
renders two generated hygienic matcher names with a dagger in `#check` output.
The correction permits that exact rendering only for internal `._@.` names;
BEGIN/END and axiom reports still require exact environment names, and authored
roots still require exact printed names. The two-name incident and repair are
retained in `integrity-parser-repair.json`. It changed no proof, checker or
producer output and consumed no Lean call. The producer's separate interrupted
greedy-parser incident is also retained in its frozen evidence.

## Exact residual obligations and next bridge

1. Authenticate the input parent relation, fixed raw term/table views,
   canonicalization functions, actual post-check Context, formed Context arena
   and raw interner inventories from one native execution. The mathematical
   functions quantify over these inputs and do not establish their authenticity.
2. Refine decoded complete keys to physical `ScopedFlowId` interning, its enabled
   flag, interner invariants, finite capacity/inventory checks, allocation, integer
   bounds and failure-path partial mutations. The present arena is deliberately
   a mathematical allocation-success representation.
3. Cover the other actual Value dispatch branches: current-memo reuse,
   canonical/retained extrusion rewrites, incompatible-shape diagnostics,
   bottom/top shortcuts, fallback row propagation and their event owners.
4. Connect these constructed admissions and pending enqueue stages to actual
   issued occurrences, committed completed bodies, diagnostic acceptance,
   merge/cancellation/restoration/versioned table history and terminal Replay
   receipts. Admission and no-ACK enqueue are not an accepted drain or completed
   child proof. `record_typed_pair_admission` is not promoted to a completed body.
5. Construct the entire original shared `nu,K,D,eta0` interpretation, full
   descriptors, complete Call/method/annotation meaning, source queries and
   independent challenges. Four scalar Function ports do not establish a complete
   callable contract. Full `OriginalValueMem`/`PhiW`/`P_F`/`SourceT` and the original
   same-scoped witness remain with their semantic owners; no narrowing of the
   original language or replacement source checker is authorized.

The first applicable bridge is the authentic native input/event projection that
installs these exact constructed child jobs in the shared Context/drain history.
This review accepts the reusable constructor result, with those named obligations
remaining open. Root remains the sole integration, shared-status and Git owner.

## Review artifacts and cessation

Repository write lease used only for this review file. Scratch writes are confined
to `value-ports-review-r4`: `review_integrity.py`, `integrity-result.json`,
`integrity-parser-repair.json`, `review-inputs.json`,
`key-theorem-types-and-axioms.txt`, the final output
hash manifest and STOPPED marker. No producer/source/config/import/Rust/dependency
or shared-status file was changed. No child, Git command, fresh Lean process or
background checker was launched. The exact stop time and review-file hash are
recorded in the final scratch manifest; the cessation footer follows below.

## Appendix: exact principal theorem types and axioms

These six complete blocks are reproduced from the reconciled final census. The
full 891-declaration type/axiom receipt and all 348 theorem blocks remain in the
frozen producer handoff and census.

```text
@YulangClosure.NativeValuePorts.build_context_formed : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {weight : Option Nat} {post : Nat} {swap : Bool},
  YulangClosure.NativeValuePorts.ContextsFormed arena.contexts →
    post ≤ arena.contexts.length →
      YulangClosure.NativeValuePorts.ContextsFormed
          (YulangClosure.NativeValuePorts.buildContext arena weight post swap).fst.contexts ∧
        (YulangClosure.NativeValuePorts.buildContext arena weight post swap).snd ≤
          (YulangClosure.NativeValuePorts.buildContext arena weight post swap).fst.contexts.length
'YulangClosure.NativeValuePorts.build_context_formed' depends on axioms: [propext, Quot.sound]

@YulangClosure.NativeValuePorts.admit_constructs : ∀ {arena after : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.admit arena views qv qe parent post derived child = Option.some (after, receipt) →
    arena.Extends after ∧
      YulangClosure.NativeValuePorts.AdmissionResult after views qv qe parent post derived child receipt
'YulangClosure.NativeValuePorts.admit_constructs' depends on axioms: [propext, Quot.sound]

@YulangClosure.NativeValuePorts.variant_first_missing : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {upper before after : List YulangClosure.NativeValuePorts.Alternative} {start : Nat}
  {actual : YulangClosure.NativeValuePorts.Alternative},
  (∀ (candidate : YulangClosure.NativeValuePorts.Alternative),
      candidate ∈ before → upper.any (YulangClosure.NativeValuePorts.matching candidate) = Bool.true) →
    upper.any (YulangClosure.NativeValuePorts.matching actual) = Bool.false →
      YulangClosure.NativeValuePorts.variantChildren terms upper start (before ++ actual :: after) =
        Except.error (start + before.length)
'YulangClosure.NativeValuePorts.variant_first_missing' depends on axioms: [propext]

@YulangClosure.NativeValuePorts.dispatch_step_valid : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {before after : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.DispatchStep views qv qe parent post derived before after →
    YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue before →
      YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue after
'YulangClosure.NativeValuePorts.dispatch_step_valid' depends on axioms: [propext, Quot.sound]

@YulangClosure.NativeValuePorts.drive_success_readback : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {arena : YulangClosure.NativeValuePorts.Arena} {fuel : Nat} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived fuel
        (YulangClosure.NativeValuePorts.initialCursor arena children queue) =
      Option.some cursor →
    cursor.pending = Option.none ∧
      ∃ jobs,
        List.map YulangClosure.NativeValuePorts.Work.source jobs = children ∧
          cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native jobs ++ queue ∧
            (∀ (work : YulangClosure.NativeValuePorts.Work),
                work ∈ jobs →
                  YulangClosure.NativeValuePorts.AdmissionResult cursor.arena views qv qe parent post derived
                    work.source work.receipt) ∧
              ∀ (work : YulangClosure.NativeValuePorts.Work), work ∈ jobs → work.native.replayAck = Option.none
'YulangClosure.NativeValuePorts.drive_success_readback' depends on axioms: [propext, Quot.sound]

YulangClosure.NativeValuePorts.Witness.function_drive_whole : ∃ cursor,
  YulangClosure.NativeValuePorts.Witness.completed = Option.some cursor ∧
    cursor.pending = Option.none ∧
      ∃ jobs,
        List.map YulangClosure.NativeValuePorts.Work.source jobs = YulangClosure.NativeValuePorts.Witness.children ∧
          cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native jobs ∧
            (∀ (work : YulangClosure.NativeValuePorts.Work),
                work ∈ jobs →
                  YulangClosure.NativeValuePorts.AdmissionResult cursor.arena
                    YulangClosure.NativeValuePorts.Witness.views id id YulangClosure.NativeValuePorts.Witness.parent 1
                    Bool.true work.source work.receipt) ∧
              ∀ (work : YulangClosure.NativeValuePorts.Work), work ∈ jobs → work.native.replayAck = Option.none
'YulangClosure.NativeValuePorts.Witness.function_drive_whole' depends on axioms: [propext, Quot.sound]
```

## WRITES STOPPED

`2026-10-26T12:06:48.402229+00:00`. Verdict **ACCEPT**. Review wall time 544.402 seconds within 900 seconds; focused Lean calls **0/2**; children **0**; live checker processes launched by reviewer **0**. All authorized review writes are complete.
