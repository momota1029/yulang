# Ordinary Function Argument Effect: source and live-consumer audit

Date: 2026-10-10
Status: independently reviewed bounded static source characterization; no theorem, hygiene,
source acceptance, implementation-gate, or production-conformance promotion
Assigned baseline: `3fab829c0683e4b3b06dfe61f4b60a12884560a5`
Worker: `/root/argument_effect_source_bridge`; complementary source audit
Exclusive lease: this note only; no compiler edits, execution, or delegation

## Objective and governing premises

Trace an ordinary Argument Effect through real source formation, annotation
construction, typed Function comparison, context derivation, the live consumer,
capture/freshening and rollback. Authority is the selected contextual-attachment
design §§3–6, including §3.1 set-wide attachment identity, and the annotation
effect policy §1. This audit retains composed polarity, local subtraction rather
than family-wide erasure, symbolic-variable connectivity, the distinct inferred
entry flow, and the disabled general concrete-negative admission gate. The
callback example's retracted output supplies no expected result.

The previously reviewed Function-port proof is a conditional operation-order
derivation. This audit independently extracts its frozen Oracle source blobs;
it does not repeat that algebraic proof or treat endpoint reversal as evidence
of executable subtraction. All current-source locators below refer to the
assigned baseline. Direct dependencies were compared byte-for-byte with that
revision; all matched at inspection and final freeze.

## One actual source construction path

Use the existing source fixture at
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs:59`:

```yulang
act io:
    our tick: int -> ()
my bridge (consume:([io] int) -> ()) = consume
```

The fixture contains an ordinary Function Argument Effect. The formal parameter
starts at composed Negative; its Function argument flips to composed Positive.
Thus this `[io]` is a concrete allowance under the selected policy. Its textual
argument position does not make it a negative subtraction interface. The
fixture's existing assertion is source evidence, not a test result from this
audit; no parser or solver was executed here.

Direct source facts, with conditional execution steps explicitly identified:

1. `yu-hir/src/module/local_source.rs:290` retains the parameter's source key,
   lexical scope and parsed annotation. `source_annotation.rs:399` puts the
   bracket row on the Function argument; `:505` separates sigil variables from
   concrete atoms and requires a unique effect-namespace declaration for each
   supported identifier operand. The concrete entry is the resolved declaration,
   not its spelling. Parameterized effect operands are outside this parser's
   inspected identifier-only branch.
2. `shadow_apply.rs:80` invokes `candidate_source::preflight` before candidate
   collection/session creation. `candidate_source.rs:92` starts formal checking
   at Negative and flips argument polarity recursively. This fixture's argument
   row passes the composed-positive clause. At `:257`, collection schedules an
   exact `FormalAnnotation` action; `:553` executes that action.
3. `candidate_effect.rs:899` constructs paired positive/negative Function terms,
   with the argument variance reversed. At `:919`, explicit composed-positive
   effects use one source view, keyed by the exact row `SourceNodeKey`, on both
   polarities. `:1304` gives it resolved concrete members and no symbolic tail.
   Its positive port row has a Support lower; its negative port row has an
   Allowance upper. `:605` creates the source payload and closed filter handle.
   `candidate_context.rs:1360` retains owner, position, scope, polarity and all
   ordinals under one payload identity. The stored left/right words are empty.
4. `candidate_formal_annotation` at `candidate_effect.rs:938` introduces
   `F_positive <: parameter` (slot 43) and `parameter <: F_negative` (slot 44).
   Conditional on successful preceding allocations and ordinary bound
   propagation, `candidate_extrusion.rs:645` replays opposite bounds as the
   actual ordered positive-Function/negative-Function comparison. This is the
   inspected mechanism that supplies the comparison, rather than an invented
   standalone comparison rule. A complete source worklist trace is unverified.
5. The live typed Function case at `lib.rs:12030` emits Argument Effect endpoints
   `F_upper.argument_effect <: F_lower.argument_effect`; at `:12074` it calls
   `candidate_function_port_admit` and stores that relation on the queued item.
   The result ports preserve endpoints; the argument ports reverse them.
   There is no syntactic Oracle `Neg::Bot` passthrough branch in this ordinary
   four-child block. This audit does not assess the separate inferred-entry
   replacement's complete correspondence.
6. At `candidate_context.rs:1680`, the constructor uses the parent's retained
   post-check context `P`, computes `Swap(P)` for Argument Effect when `P` is
   nonidentity, and then prefixes the child-local closed Allowance payload:
   `PrefixLeft(w, Swap(P))`. If `P=Identity`, the constructor omits structural
   `Swap(Identity)`. If the local context is Identity, it adds no prefix. A local
   nonidentity context must be exactly `PrefixLeft(w,Identity)` or construction
   fails. In this fixture, annotated ports are live rows; the port comparison
   can have Identity local context, with the closed filter encountered later
   through Support/Allowance bound replay. This does not authenticate a
   source-reachable nonidentity Function parent.
7. `lib.rs:11862` invokes `candidate_context_execute` before endpoint memoization.
   Identity passes without contextual work. The supported nonidentity path
   validates every zero-word filter before publishing its checks and registers
   the corresponding Allowance on the real receiver. The atom consumer at
   `candidate_effect.rs:753` unfolds Support members, checks concrete operands
   against the retained allowed set, sends unmatched members into a symbolic
   tail if one exists, and records a mismatch for a closed disallowed member.
   `candidate_extrusion.rs:726` keeps level-selected bound insertion and
   opposite replay. These are executable allowance mechanisms; they do not
   perform annotation-local subtraction.

## Discriminating fragment and exact missing premise

The constructor and consumer support different envelopes. Directly inspecting
`candidate_zero_word_filters` at `candidate_context.rs:1731` yields its complete
node grammar: Identity, `PrefixLeft(w,Identity)`, and ordered Replay nodes whose
children precede their parent. Payload ownership, boundary identity and empty
words must validate. Every other node returns `IdentityExhausted` via
`exhausted()` at `:545`.

A smallest nonidentity inherited context in the supported grammar is
`P=PrefixLeft(w,Identity)`. Conditional on an ordinary Argument Effect port
being constructed with that retained post-check parent and no child prefix,
its exact image is `Swap(P)`. The live consumer rejects that Swap root. If a
child prefix exists, `PrefixLeft(v,Swap(P))` is rejected because its input is
not Identity. Even a Preserve result with a nonidentity parent and new child
prefix leaves the consumer's grammar. This is a two-node static discriminant
between carrier construction and live execution, not a source-reachable failing
program or a theorem about reachable tasks. A nonidentity Value parent is itself
rejected by `candidate_context_execute`, so this audit cannot infer that the
port is actually reached with this supplied `P`.

The precise remaining premise is therefore source-derived transport and live
discharge of nonzero inverse-position context obligations, including attachment
identity, actual PUSH/POP data, active-family checks and receiver registration.
Correct endpoints and an operation-labelled dependency do not supply it.

## Contract correspondence and lifecycle boundary

| Selected contract | Baseline evidence and classification |
| --- | --- |
| §3 exact operation tree and relation identity | Executable structural interning and `RelationKey { pair, context }` at `candidate_context.rs:1417`; component kind is in the typed pair. Exact construction is not full operation execution. |
| §3/§3.1 annotation-owned set and member ordinals | Retained per-view payload, owner/position/scope/polarity and ordinals; source payload survives symbolic tails. `unit_push` is dormant and the words remain empty. Negative empty bundles are explicitly inert provenance at `candidate_effect.rs:1137`, not an executable grant. |
| §4 Function ordering | Executable constructor matches swap-before-child-prefix for its restricted local-prefix input. At `candidate_context.rs:114`, the comment that child admission reconstructs its own context is stale for nonidentity parents; its narrower claim that no structural `Swap(Identity)` is constructed remains accurate because the implementation elides that node. The function body at `:1680` is direct evidence. `retained_input` still marks FunctionPort dependencies inert (`:494`). |
| §4 admission before equality | Context execution occurs before endpoint memo/equality handling. Closed zero-word filters are validated/registered and discharged; `post_check_context` becomes Identity only for a discharged relation (`:1560`). Nonidentity Value, Swap, suffix POP, Both and nested prefixes are rejected. |
| §4 negative wrapper/filter obligations | Closed Allowance checks and future-bound replay are executable. Source concrete composed-negative rows are rejected before solving; corresponding constructor guards also reject them. Actual right POP and active-family obligations have no live execution in this consumer. |
| §4 concrete residual, lineage gamma and feedback | Absent from the inspected route. No `ResidualRecipe`/gamma constructor occurs in the searched context/effect/scheme/extrusion/intrusion owners. This is a bounded owner audit, not a whole-repository absence theorem. |
| §4 inferred entry Both | Inferred-entry provenance is explicitly inert (`candidate_context.rs:59`). The context syntax has a certificate token, but live filters reject Both and capture payload discovery rejects it at `:939`. No authorization is established by retaining a token. |
| §4 capture/freshening | `candidate_scheme.rs:596` follows reachable bound contexts and payload views, then retains bundle incidence. At `:910` it remaps payload views through one per-use map and renames context DAGs; `:1020` restores contextual bounds and fresh bundle incidence. Swap is structurally traversable and renameable; that does not make it executable. Full Both capture is rejected. |
| §4 extrusion/intrusion | Existing level orientation, actual row maps, bound origins and transport witnesses are retained. Their presence does not authenticate all transport: retained-input analysis reports transport-authentication gaps and always reports unavailable filter obligations, producer readiness and dependent observations (`candidate_context.rs:531`). |
| §§4–5 rollback and circuit certificates | Context checkpoints/rollback cover present payloads, nodes, relations, dependencies, origins, bounds, replay cursors, uses, bundle incidence and discharges (`:1061`). Effect checkpoints include views, contributions, conflicts, annotation maps and capture incidence; intrusion delegates to them. `lib.rs:9155` rolls back failed routes and `:9313` invokes intrusion rollback. No selected two-circuit acceleration/certificate-observation withdrawal implementation was found in these inspected owners. Existing intrusion generations/completions are not evidence of that circuit contract. |
| §6 concrete-formal gate | Intentionally disabled: `preflight_annotation` disallows concrete rows at composed Negative; formal preflight additionally requires exactly one variable there. `candidate_formal_pair` and `candidate_signature_effect` repeat guards. This is recorded candidate rejection, not a newly selected public source boundary or a hygiene proof. |

No rollback/retry execution ran. The present journal supports the retained
state; it cannot establish rollback of unconstructed residuals, circuit
certificates or observations. No candidate result was published in this audit.

## Independently extracted Oracle comparison

Oracle revision: `6a18bd24bd0fa8b07e3eca5e099bfa8646320e3a`, the frozen parent
named in the reviewed proof note. Read-only extraction confirmed both blobs:

| Oracle file | Git blob |
| --- | --- |
| `crates/infer/src/constraints/machine/propagate.rs` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |
| `crates/infer/src/constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |

`propagate.rs:226,247–255` reverses ordinary argument endpoints and passes the
actual `constraint.weights.swapped()`. Positive Stack/NonSubtract consumers at
`:19,:31` then apply `with_left_prefix` using the actual wrapper weight.
Negative Stack at `:37` checks the filter and active-stack families before
retaining its right suffix. The separately guarded syntactic `Neg::Bot` path
uses `both_from_right`, rather than ordinary Swap. The bodies at
`constraints/mod.rs:3566,:3577` confirm the directed conversions and prefix
composition recorded in the proof note.

Independence here means fresh extraction of immutable source and comparison
against the actual successor constructor/consumer. Both this audit and the
proof share the selected policy and the interpretation of those named weight
operations. Neither establishes their full semantics, source reachability,
all worklist activation or runtime handler behavior. No second checker, toy
transition model, seeds/ranges, mutations or Oracle execution was used.

## Freeze, checks, resource use, and next action

The SHA-256 dependency table below freezes the assigned revision. Read-only
`rg`, bounded `sed`, `git show`, `git rev-parse` and a serial Python/hashlib
snapshot check were used. All listed workspace dependencies matched baseline;
the final recheck confirmed no changed dependency. Note integrity checks cover
the single leased path, final newline, balanced fences, trailing whitespace
and required packet/claim markers. They do not validate mathematics or source
execution. No test/build, Git mutation, compiler change, shared-record edit,
child, benchmark or executable experiment occurred.

Read-only batches peaked at three tool invocations. No heavyweight process ran.
Exact CPU/RAM and wall time were not measured; budget consumption is unknown
numerically. Unverified scope includes the complete fixture trace, actual
nonidentity Function reachability, arbitrary mixed recursion, attachment-local
negative subtraction, handler selection, full Call, soundness/principality and
public/default/F5 cutover. The independent compiler-referee review found no
blocking or major issue and one minor source-comment paraphrase, corrected
above. This remains a bounded characterization, with no source-reachability or
gate certification.

Recommended next action: assign the owning live inverse-context consumer cut,
with source-produced PUSH/POP and receiver obligations as retained premises,
while retaining concrete-negative admission behind its existing gate. Another
endpoint-polarity probe cannot resolve this consumer gap.

### Dependency SHA-256 snapshot

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/progress/2026-10-10-function-argument-effect-contravariance-proof.md` | `7377dc89973b5b380c1466161f0c20e94d0cf39fb860aa1477e9a3b3aec1730c` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/src/term.rs` | `75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615` |
| `crates/yu-solver/tests/candidate_formal_effect_polarity.rs` | `dc89def4c2653960e29474135d4e2f91c076bd8a27eb54b048088820a915d636` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-argument-effect-source-bridge-audit.md`.
- Baseline SHA: `3fab829c0683e4b3b06dfe61f4b60a12884560a5`.
- Changed dependency hashes: none observed; frozen table and Oracle blobs above.
- Claim/review status: independently reviewed bounded static source
  characterization; writes stopped after the minor wording repair; no theorem,
  gate or production promotion.
- Checks already run: read-only source/Oracle extraction, baseline/hash equality,
  narrow note integrity check; no builds/tests/execution.
- Proposed checkpoint message: `research: audit ordinary Function argument effect source and consumer seam`.
- Shared-record deltas left to primary/curator: link this audit in
  `tasks/current.md`/theory records if accepted; distinguish executable allowance
  and port construction from inert PUSH/Both metadata, rejected inverse contexts,
  disabled concrete-negative admission and unconstructed residual/circuit
  lifecycle. No shared file was edited.
