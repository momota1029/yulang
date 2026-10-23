# R345 — K0 initial-drain source census

Status: frozen primary source census, revision 1. Source files are read-only.
This is source correspondence evidence, not a proof of `H(S)` preservation or
an independent review. The constructive lane has a separate exact lease.

## Parent and inputs

Parent: the unchanged full Yulang2/Simple-sub source/native A/B theorem and
catalog. Immediate gate: audit N/D2, continuing R339's ordinary replay-child
retirement proof with initial/current, designated, processing and FunctionPort
obligations. R339's narrow child result remains accepted only at its stated
scope.

- R345 contract SHA-256:
  `c4322952c7c484003ee7c85efeb63e3b6daf34a1efbb17b2d32ae532e5074fa8`.
- Baseline branch/head/upstream:
  `research/simple-sub-intrusion` /
  `addd4ea9ff2b868fd01dca28c34e6c2b0d6e42d8` / same.
- User audit SHA-256:
  `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- Whole-language semantics TeX SHA-256:
  `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`.
- Aligned audit revision SHA-256:
  `bea755595302d5b98fb1880fb89b505ad783a6e428c639aae6734b167df86d65`.
- R339 contract rev2 / proof / outcome-receipt hashes:
  `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00`,
  `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87`,
  `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701`.
- Direct source files below match the R345 contract's SHA-256 manifest.

The aligned audit is a navigation/crosswalk artifact only. R345's algebraic
`H(S)` remains the existing independent K0 interpretation; this census does
not identify it with the whole-language `Vⁿ/Cⁿ` interpretation or boundary
evidence. The original audit and TeX inputs are untracked user files and were
not edited.

## Source-to-state path

### 1. Source occurrence to initial Value/Effect task

`candidate_source::Action::Fact(index)` calls `admit_collected_fact` at
`candidate_source.rs:2427`. The owner at `lib.rs:11481–11530` admits the exact
`ConstraintOccurrence` into the store transaction, records provenance, reads
the admitted term kind, and forms:

- Value: positive lower endpoint and negative upper endpoint;
- Effect: positive lower endpoint and negative upper endpoint.

Both are sent to `constrain_live_*` with that occurrence's identity and cause.
`constrain_live_item_with_inferred_entry` enters `run_candidate_typed_drain`
when the candidate graph is active (`lib.rs:13950–14035`). This identifies the
native ingress task. The `H(S)` proof must still interpret the authentic source
inequality independently; successful store admission is not its own semantic
witness.

`LiveConstraintTask` has exactly two cases, Value with a canonical endpoint
pair or Effect with lower/upper endpoints (`lib.rs:4225–4238`).
`term::Polarity` has Positive and Negative constructors
(`term.rs:150–153`). The separate bound owner maps positive side to `b ≤ o`
and negative side to `o ≤ b` (`candidate_effect.rs:476–489`); keep this
orientation when relating row bounds to `φ(q)`.

### 2. Initial frame and pending-to-current handoff

`start_typed_drain` starts with an empty typed worklist, saves current native
processing and context relation through `begin_typed_drain`, clears the live
processing slots, obtains any source-context seed, and enqueues the incoming
item (`lib.rs:14186–14222`). The frame constructor retains `initial`, source
occurrence/cause, prior processing pair/relation, `current=None`, and its
initial `Transport` stage (`candidate_context.rs:2249–2262`).

If an inferred-entry seed is created, a passive `SourceDrainReceipt` is
published only after enqueue succeeds. It records task/origin/relations but
does not itself assert that the item is entailed or semantically discharged.

At `Transport` with no current item, the driver may settle intrusion against
the retained initial task when the worklist is empty; it then prepares any
front replay ack, pops a work item, and stores the exact item as `frame.current`
(`lib.rs:14320–14354`). With a current item, it sets native processing to the
task and relation. `Transport` rewrites its relation, `Context` records the
context-execution result, and `Dispatch` passes the task to the ordinary
consumer (`lib.rs:14355–14392`). Thus a queue pop moves the task into frame
state; it does not by itself remove the formula from the intended `P(S)`.

### 3. Cache-current suppression and task dispatch

`pair_is_current` requires both a `TypedPairKey` memo entry and a processing
relation whose completion generation is current (`lib.rs:13507–13518`). For
Effect, `dispatch_live_item` records canonical enqueue evidence before checking
the raw pair. A current hit skips re-application; a miss marks admission then
applies the task. For Value, a current hit returns immediately; otherwise the
dispatcher handles canonical rewrite, retained extrusion rewrite, terminal
shapes, structural decomposition or the direct transition
(`lib.rs:14432–`; primary inspection continued through the Function/tuple/record/
variant dispatch cases at `14780–14848`).

The memo/generation conjunction is an operational shortcut only. It is not a
logical entailment `H_after ⊨ φ(q)`. A proof of retirement must identify an
existing bound, retained child, or remaining formula that supplies the removed
task. The dispatch memo's diagnostic `children` and `completion` fields also
cannot be assumed to coincide with `H(S)` without a separate projection lemma.

### 4. Function-port child creation and enqueue

For a positive lower / negative upper Function pair, `dispatch_live_item`
constructs the four ordered children:

| Field | child endpoints | polarity action |
|---|---|---|
| Argument Value | upper argument positive → lower argument negative | contravariant |
| Argument Effect | upper argument effect positive → lower argument effect negative | contravariant |
| Result Effect | lower result effect positive → upper result effect negative | covariant |
| Result Value | lower result positive → upper result negative | covariant |

The array is stored in `FunctionDispatch` on the parent frame
(`candidate_context.rs:61–64`; `lib.rs:14780–14848`). Each step first asks
`candidate_function_port_admit` for a child relation, stores a pending
`TypedWorkItem`, and a later step enqueues it. Only after successful enqueue
does the dispatcher clear `pending` and increment `next`
(`lib.rs:14955–14990`). The parent frame remains live while the child is handed
off.

`candidate_function_port_admit` reads the actual processing parent, derives
the child pair and source metadata, computes the operation (`Swap` for
Argument/ArgumentEffect; `Preserve` for ResultEffect/Result), composes the
parent post-check context with authentic local scope/demand evidence, creates
the child relation and records `Derived`/`FunctionPort` dependencies when
applicable (`candidate_context.rs:3505–3567`). It does not add a direct concrete
bound to `B(S)` by itself. The required `φ(q)` must be established from the
independent structural/typed K0 interpretation and transported through the
pending child, relation lifecycle, and subsequent drain. R339's direct
replay-bound witness does not cover this path.

### 5. Acknowledgements, return and frame restoration

Before a `Transport` dequeue of a replay child, the driver prepares its exact
ack and stores it in the drain frame. `Dispatch` clears the copied current
item's `replay_ack`, while the frame retains the acknowledgement for terminal
completion (`lib.rs:14327–14348, 14375–14391`). Terminal processing validates
the frame index/stage/cursors, completes one exact child acknowledgement at a
time, and only after `ReturnReady` records passive source-drain completion,
pops the frame and restores the saved processing pair/relation
(`lib.rs:14881–14953`; `candidate_effect.rs:490–518`).

The `initial` task is still present in the frame throughout dispatch and
terminal processing. The terminal pop removes that representation. A proof
must show the same formula remains in `B/Q/P/R/D` or is entailed by the
post-pop theory. Likewise, restoring a prior processing task is not proof that
the just-retired initial task was discharged. A completion receipt is
attribution only.

## Census boundary and implementation disposition

The inspected concrete owners establish where work is stored, moved, checked,
and retired. They do not yet establish the mathematical `H(S)` projection for
every initial, designated, processing or FunctionPort item, nor that every
removed formula is entailed after terminal pop. I found no source-qualified
K0 defect that would justify a code change. The implementation disposition is
`NO_SAFE_CODE_SLICE` for this census; this is a missing proof supplier, not a
claim that the complete compiler path is sound.

Exact hashes at census freeze:

| Owner | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

Checks were direct source inspection and SHA-256 comparison. No tests, builds,
compiler/runtime probes, code changes, external contact, descendants or Git
operations were used.
