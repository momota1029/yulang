# Oracle returned callback: SCC order and the first missing fresh-use identity

Date: 2026-10-11
Status: frozen unreviewed source audit; original universal H remains OPEN
Claim class: source-derived ordering/constructor facts and a localized artifact gap
Y3 baseline: `6984b89e55a55d03f95d963b38dbc180c746b285`
Oracle source baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only; leaf, no delegation or compiler changes

## Objective, authority and frozen evidence

Trace the exact source and dump in
[qualified returned callback probe](2026-10-11-oracle-qualified-returned-callback-probe.md),
from SCC scheduling to the original annotation identity and its actual use at
`e11/r2`. Locate the application and retained-check owners, stopping at the
first unsupported source-ID/consumer correspondence. This packet executes no
Oracle: the earlier two-call budget is exhausted.

Authority: [selected annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and withdrawn callback result §6;
[original H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md) §1 and
generalized-observation premise §5;
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Original H still quantifies over every original successfully lowered
program, annotation, instance and actual route; this single program does not
replace that domain. No source meaning or subtraction rule is reselected.

The exact source remains:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
my provider() = \() -> tick::ping()
my observed() = f provider
```

The frozen dump observes a clean, nonmissing provider with
`() -> () -> [tick] ()`, `r1:"tick::ping"->d1:"tick.ping"`, and
`observed: () -> [tick] ()` containing `e11:r2:f->d2:f` and
`e12:r3:provider->d3:provider`. Its `f` display contains `'b#0[tick]`.
The earlier binary/source correspondence premise remains primary supplied:
checking binary bytes did not independently prove its build provenance.

## SCC/DAG order: expansion follows quantification

Oracle paths below are relative to `/tmp/yulang2-oracle-read`.

`crates/infer/src/lowering/body/mod.rs:632–641` explicitly lowers **all
binding bodies before draining analysis**. Lines 2071–2082 traverse the source
block; 2263–2364 enqueue RegisterDef and complete the named binding. Thus
`observed`'s reference and application construction can precede quantification
of `f`. Textual declaration order does not establish prior publication.

The visible global-reference DAG for this source is `observed -> f` and
`observed -> provider -> tick.ping`. The reference to `cb` inside `f` is local:
`lowering/name_ref.rs::lower_local_name` resolves it directly rather than
enqueueing the global ApplyRefResolution/UseResolved path. The five-line
source has no reverse global reference or method selection. This describes
the source-generated reference DAG, not a captured SCC event transcript.

The required relative order is enforced at the source owners:

1. `analysis/session/lifecycle.rs:1092–1101` resolves a global reference and
   sends its stored parent, target and use coordinate to UseResolved.
2. `scc.rs:266–325` either emits InstantiateUse for an already quantified
   target or retains the dependency until the target is ready. A same-SCC
   reference instead uses OpenUse; the displayed acyclic global-reference
   source has no such reverse reference.
3. `scc/graph.rs:496–518` requires completed roots and no outgoing edges,
   method dependencies or conformance blockers. `scc.rs:329–359` emits
   QuantifyComponent **before** incoming InstantiateUse events.
4. `analysis/session/selection.rs:1040–1120` consumes events in order; it
   batches only consecutive InstantiateUse events. QuantifyComponent calls
   `quantify_component` before a later instantiation batch.
   `analysis/session/instantiate.rs:14–83` generalizes/finalizes and installs
   each actual scheme; `358–367` requires `Def::Let { scheme: Some(..) }`
   before preparing an instantiation.

Therefore the ordinary completed source route expands `f`'s stored scheme
for the `observed -> f` use **after quantification**, even if that reference
was constructed or resolved earlier. The code establishes this partial
order; the dump supplies neither timestamps nor a full SCC event sequence.
No claim of “f was quantified before lowering observed” follows.

## Authentic annotation constructor and first unsupported identity

Let `a` denote the concrete `[tick]` occurrence in the returned Function
inside `cb`'s annotation, and let `s_a` denote the actual SubtractId allocated
when the owning paired annotation constructor executes for that occurrence.
This is a source-defined symbolic identity, not the numeric guess zero.

`lowering/expr/lambda.rs:1244–1283` connects the real parameter annotation
through AnnConstraintLowerer. `annotation/constraints.rs:251–280` selects
the parameter boundary path; `124–138` emits both positive and negative
value connections. Its recursive Function case at 363–389 descends into
the returned Function and constructs all four ports. The concrete result
row owner at 424–470 calls `effect_row_stack`; lines 657–690 allocate a fresh
ID for the resolved concrete atom set, and 593–599 register its declared
stack fact. The row has a PUSH view and a filtered negative view. These are
actual constructor owners, not supplied transition axioms.

The Function case returns only **its immediate** `ret_eff.subtracts`.
Consequently the nested `[tick]` allocation is not automatically the outer
`cb` binder's immediate call predicate. Equating every descendant occurrence
with that predicate would skip an actual source boundary.

The first unsupported bridge is **the original `s_a` to the raw identity and
quantified status in the stored `f` scheme**. `generalize/mod.rs:177–238`
computes stack quantifiers from compact liveness and prunes stray IDs.
`generalize/core/stack_ids.rs:23–49,76–109,176–179` requires live PUSH entries
in covariant positions at selected quantified coordinates. This is not the
rule “all annotation IDs are quantified.” Neither the frozen dump nor this
packet has the executed compact graph, raw `f.stack_quantifiers`, or an
allocation/projection certificate for `s_a` through these transformations.

The display cannot repair that gap. `poly/src/dump/type_format.rs:21–23`
creates a new TypeVarNamer for each scheme; lines 552–588 assign encountered
raw SubtractIds consecutive display numbers from zero. The formatter at
`type_format/formatter.rs:1351–1362` prints that assigned number.
Thus `#0` identifies a formatter encounter within `f`'s display, not raw
SubtractId(0), its annotation origin, or its fresh use in another arena.

## Freshening owner: exact rule, unavailable executed map

For a local source target, `analysis/session/instantiate.rs:449–457` uses
`instantiate_scheme_with_roles_and_provenance`; `instantiate.rs:91–103`
creates one new SchemeInstantiator. Lines 621–647 preallocate fresh mappings
for `scheme.stack_quantifiers` before cloning the predicate. Lines 741–768
implement its private map: each quantified source ID receives one target
fresh ID, repeated occurrences reuse it, and an unmapped ID is reused by
ordinary cloning. Lines 770–787 then add root POPs of `u32::MAX` for the
selected quantified IDs. These operations are more than a pure renaming.

Symbolically, for each actual `q` in the stored quantifier set `Q_f`, the
`r2` instantiator constructs one `M_r2(q)` and consistently reuses it. The
source proves that conditional map rule. The artifact contains neither
`Q_f` nor entries of `M_r2`; it cannot establish `s_a in Q_f`, a numeric
`s_a -> M_r2(s_a)` pair, or even the required original-to-scheme identity
relation before that map. No executed map is invented here.

`analysis/session/instantiate.rs:462–486` records generalized source/use
provenance and projected witness routes. Its `505–522` and `318–337` connect
the cloned predicate to this stored use coordinate by actual direct-lower
or subtype insertion. The poly dump retains `r2`'s target DefId, but omits
that use coordinate, the private subtract map and these derivation records.

## Application, contribution and check owners within the stopping boundary

The static operation audit already connects provider's operation DefId to
the declaring effect TypeDeclId. The frozen dump observes its body and the
two applications inside `f`: `e2 = cb ()`, then `e4 = (cb ()) ()`.
It does not observe those callbacks running or their constraint provenance.

`lowering/expr/tail.rs:535–625` is the actual application constraint owner:
it constructs a negative Function demand from the argument and fresh return
ports, constrains the callee, and joins callee/call effects into the result.
`constraints/machine/propagate.rs:210–267` sends argument ports in the
reversed direction and result ports in the preserved direction; its pure
argument-effect passthrough is a separate branch. This locates the consumers
for both `cb` applications and `f provider`. It does not reconstruct the
executed weighted edges from provider's concrete contribution to output.

Actual check/replay owners are localized:

- `machine/propagate.rs:38–56` checks a negative Stack filter before erasing
  its wrapper and enqueueing the normalized derived constraint.
- `machine/bounds.rs:3213–3255` retains a variable's non-All filter and visits
  current lowers. New semantic lower insertion at 630–730 checks its own
  incoming filter and calls the registered-filter owner at 3285–3301.
- `bounds.rs:3303–3360` checks weighted concrete lowers, recursively retaining
  obligations on encountered variables. It does not descend into Value
  Function ports; a latent callback requires its own structural route.
- `bounds.rs:3363 onward::lower_bound_replay_actions` prepares actual weighted
  replay, with explicit proof-terminal failure. These are production owners,
  not evidence that this probe's particular annotation receiver was visited.

No actual raw receiver/filter/constraint records are available for `r2`, and
no retained-check discharge certificate is printed. Generic owner coverage
therefore cannot certify this route's check activation, replay completion,
safe discharge, or contribution lineage after generalization. Inspection
stops at the original-to-stored-scheme identity gap; it does not attempt the
downstream whole-route proof by assuming that missing premise.

Classification: **only a bounded positive observation**. The printed result
retains `[tick]`, but lawful preservation of the original attached
contribution is not established. No independent same-family contribution
was constructed, no forbidden removal or missed check is witnessed, and this
is not a source-qualified hygiene falsifier. Original H remains OPEN.

## Baseline delta, checks, omissions and next owner

The observation's Y3 baseline was `161886f1b63b93a3f1d08130170c509bae2feb7d`;
this packet uses `6984b89e55a55d03f95d963b38dbc180c746b285`. The inherited
authority and static-audit hashes remain unchanged; the frozen observation
is now an additional dependency. No Oracle semantic baseline changed.
No commit-range comparison or compiler integration was performed.

Checks: named source reads and hashes; note whitespace/newline/fence check.
Startup used read-only revision lookups; no Git mutation occurred. No Oracle,
Cargo/build/test, executable experiment, temporary output, mutation or seed
search ran. CPU/RSS/wall time are unmeasured; only short file/hash processes
ran, without parallel heavyweight computation. Some guessed owner paths were
absent; actual owning paths above were located. No whole-source census,
runtime event reconstruction or allocation-schedule proof was completed.
This artifact is produced by the same worker as the two earlier notes and
has no independent-review status.

Recommended next owner: a primary-assigned **prover** should derive the
original `s_a` to stored `f` compact/scheme identity and quantifier-selection
relation from the actual constructors, with these source positions as inputs.
If an executed numeric certificate is necessary, the primary must separately
authorize bounded event/map capture; this packet grants no such code or call
scope. Another unchanged poly dump does not supply the missing premise.

## Dependency snapshot and commit packet

| Governing/evidence dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-qualified-returned-callback-probe.md` | `7ccf8ef6d31d640585cbfb3e5813d518be57fd8cb1b3139601ea42d394d61bd2` |
| `notes/progress/2026-10-11-oracle-operation-path-source-audit.md` | `a39b7ff03f7358e31ce811c5e1d933bdfcb06b6de8c477590aecb87a37178819` |

Key Oracle constructor/map dependencies, relative to its pinned checkout:

| Source | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/body/mod.rs` | `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| `crates/infer/src/analysis/session/selection.rs` | `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `crates/poly/src/dump/type_format.rs` | `49800841ea8059b007076b8018076baa91ae275c76f3f07eb24a57341fe35bd7` |

- Exact leased/change path: `notes/progress/2026-10-11-oracle-returned-callback-fresh-use-bridge.md`; writes stop at handoff.
- Baseline: Y3 `6984b89e55a55d03f95d963b38dbc180c746b285`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`. No dependency hashes changed by this worker.
- Claim/review status: frozen unreviewed source facts and first unsupported identity bridge; original H OPEN; exact route remains a bounded positive dump observation.
- Checks already run: narrow source inspection and hashes, note integrity. No execution/build/test or Git mutation.
- Proposed research-checkpoint commit: `research: locate Oracle returned callback fresh-use identity gap`.
- Shared-record deltas left for primary/curator: distinguish reference construction from postquantification expansion; record formatter-local #0 and missing original-to-scheme identity/quantifier map; retain H OPEN and the exhausted call budget. No task/index/authority/theory-status file edited.
