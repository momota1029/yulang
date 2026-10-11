# Oracle direct return: fresh use and the provider row-match boundary

Date: 2026-10-12
Status: frozen producer derivation; independent review pending; original H OPEN
Claim class: bounded source correspondence and conditional path derivation
Y3 baseline: `74fff171ce7ee69ffc7c5df02569b7ed9eba5d32`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive output lease: this file only; leaf, no delegation

## Frozen statement, hypotheses and exclusions

The objective is the direct-return later-use seam of original
[H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1. Its quantifiers remain:
every successfully lowered Oracle source program P in the original domain,
every composed-negative concrete annotation occurrence a, its original lexical
scope sigma and binders, every actual copy/instantiation u, and every actual
call/output route k involving that occurrence. Authorized subtraction must
remove only the contribution attached to that exact instance on that route;
independent same-family contributions survive. Symbolic tails remain connected;
current and future concrete lowers meet retained checks. Occurrence, attachment,
scope, provider/call binder and correlated residual lineage survive copying and
generalization under the actual consistent renaming. Incorrect lowers require
authentic checking/errors and safe nonpublication. Successful lowering does not
imply successful inference/publication. Complete Call, soundness and required
principality remain separate obligations. No quantifier is discharged by this
bounded packet and none is removed from H.

For the jointly designated discriminator, fix a to the concrete `[tick]` in
`my direct(cb: (() -> [tick] ())) = cb`, sigma to direct's original body, b to
its resolved cb binder, s to that row constructor's original SubtractId, u to
the actual direct reference in `observed_direct`, and k to the outer application
in `(direct provider) ()`. Write x for the same annotation Effect coordinate
and alpha=s. Fresh images x_u and alpha_u denote the actual instantiator's maps,
not equal numeric IDs across arenas. Provider means the resolved `provider`
argument of this application, not a separately selected witness.

Authority is
[annotation-effect-hygiene-integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and
[top-level-inference-principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The primary's accepted dependencies are P/S/K at the exact hashes below.
The source and display observations are the frozen
[use chain](../progress/2026-10-12-oracle-direct-return-use-chain.md) and
[larger-source probe](../progress/2026-10-11-oracle-callback-reuse-projection-probe.md).
The four-definition extraction has not been executed in isolation.

Shared operational assumptions are the pinned source bytes, normal completed
construction/query/drain operations, successful ordinary annotation/name
resolution and fresh allocation without exhaustion, with the accepted P/S/K
premises retained. They do not supply provider compatibility, complete replay,
projection completeness, independent attachment or complete output meaning.

The bounded conclusions are:

1. An incoming acyclic reference to this direct declaration cannot acquire an
   open-use connection to its original coordinates before first export. Its
   ordinary scheme consumer consistently freshens K's retained x/alpha and
   installs a root POP(alpha_u, MAX). This is source correspondence conditional
   on the accepted P/S/K constructor slice and normal completion.
2. Along the returned-callback path, **if the actual bound/replay owners activate
   the stated Function comparisons**, native weight composition consumes the
   one retained PUSH(alpha_u, tick) with that same root POP. This is a
   conditional path derivation, not a claim that every bound is replayed or
   projected into the observed scheme.
3. For every invocation of the actual concrete row-match owner with lower
   `Con(resolved_tick, [])` and an upper row containing the same nullary family,
   the owner emits no comparison to that row's tail, for any incoming weights.
   This is a local source-derived consumer fact. Its application to the actual
   provider requires the actual provider-to-argument replay route.

No Oracle invocation, instrumented transition model, compiler edit, semantic
choice, source restriction or withdrawn callback scheme is introduced.

## 1. Transfer from fresh declaration to the acyclic source use

Oracle citations are relative to `crates/infer/src/`.
The frozen larger source defines direct with a bare cb body; the other
definitions refer to direct, through, route and provider but direct refers to
none of those definitions. The local cb reference is already resolved to b
and is monomorphic (`lowering/name_ref.rs:146–173`,
`lowering/expr/tail.rs:855–858`). There is no reverse value-reference path
from direct to a consumer, and no self application or method/impl requirement
in direct. A resolved effect type in its annotation is not such a value use.

The definition constructor enters a child level and creates fresh public R
(`lowering/body/mod.rs:2282–2301`). Its actual named-header constructor starts
empty annotation-variable and closed-row maps
(`lowering/expr/method_body.rs:55–84`). Another declaration's `[tick]` therefore
does not reuse direct's x through this map. Accepted S accounts for the local
incidence and local annotation checks; accepted K accounts for its first
normal export before incoming use constraints. These facts concern this
ordinary declaration, not arbitrary nested contexts or mutated module graphs.

For a module reference, `lowering/name_ref.rs:83–115` creates a fresh use value
and queues `ApplyRefResolution` with its resolved target. The work consumer
(`analysis/session/lifecycle.rs:1088–1100`) passes that exact parent, target and
use value into `SccInput::UseResolved`. The SCC owner (`scc.rs:266–315`) has
three genuine alternatives: already quantified target gives InstantiateUse;
same open component gives OpenUse; different components retain an edge,
merging only when the target reaches the parent. Because direct has no outgoing
value-reference route to these consumers, their incoming edge cannot close
such a cycle. Registering direct's root opens only *internal pending* uses
(`scc/graph.rs:78–82,183–215`), not incoming intercomponent edges.

When direct finishes, its component can be removed once ordinary readiness
holds. `scc.rs:329–357` emits QuantifyComponent before incoming InstantiateUse
events. `analysis/session/selection.rs:1040–1119` consumes that ordering:
quantification calls `quantify_component`, which installs the finalized scheme
at `analysis/session/instantiate.rs:55–82`; a subsequent instantiation batch
reads that installed `Def::Let.scheme`. If direct was already quantified when
the reference resolves, the first alternative uses the same installed scheme.
The open-use consumer (`instantiate.rs:4–11` in the session directory) is not
selected merely because an incoming reference exists.

Thus acyclic consumer references do not themselves invalidate K's “before
incoming external uses” snapshot. Applying accepted P/S/K to this source
declaration still requires their ordinary completed-operation hypotheses;
the earlier successful dump is not a replacement for those hypotheses.
The resulting relevant literal ports are K's returned callback
`Stack(PosVar(x), PUSH(alpha, tick))` and its argument companion
`Neg::Row([Con(tick,[])], NegVar(x))`, with x and alpha quantified.
No claim about all containing programs or compiled-cache interfaces follows.

## 2. The actual scheme constructor emits correlated fresh evidence

`analysis/session/instantiate.rs:363–455` selects the actual stored target
scheme, distinguishes imported/finalized templates and ordinarily calls
`instantiate_scheme_with_roles_and_provenance`. The captured no-prelude,
no-cache source declaration is an ordinary source definition; this derivation
uses the ordinary branch, not an unrelated imported provider.

`instantiate.rs:620–647` freshens every listed quantified variable and stack ID
before cloning the root. `fresh_var:732–738` and `fresh_subtract:741–748` reuse
one map per source key. `clone_pos:788–846` visits the same Function result
ports and stack nodes; `clone_stack_weight:983–999` uses that same subtract map.
Consequently K's positive returned occurrence and the selected root POP refer
to the *same* alpha_u. The quantifier consumer at `770–786` adds POP count
`u32::MAX` for every selected stack quantifier, including alpha_u. There is no
test of sigma, b, a later-call scope or a visible handler in that constructor.

The result is passed to the use value by the actual admission batch
(`analysis/session/instantiate.rs:311–335,488–520`). This emits the native
constraint/admission request. It does not make witness completeness, recorded
derivations or a stored lower into a proof of every later activation/projection.
In particular, cloning exports no separate source-attachment certificate that
would classify the provider operation as independent or authorize a later call.

## 3. Conditional returned-call path and its exact cancellation

Let d be u's fresh direct-reference Value, p the actual provider-reference
Value, r the first application's result Value, e1 its Effect, c1 its call
Effect, and c2/e2 the later application's call/result Effects. These are the
actual application constructor's slots, not independent witnesses.
`lowering/expr/tail.rs:543–563` emits each four-port Function demand. The first
is direct applied to p, returning r. The second demands that r accept the actual
Unit argument and return through c2. At `615–624`, each application forwards
its callee evaluation Effect and call return Effect to its own result Effect.

The second callee is `Expr::App`, not a Var of b: `tail.rs:626,844–850`.
`local_callee_call_projection:690–705` supplies no local predicate there, and
`unannotated_local_callee_return_effect:740–749` supplies a bare c2 demand.
Direct's body never invokes b. Hence no new local callback call predicate or
authentic source handler at k supplies the cancellation discussed below.

Put Q=POP(alpha_u, MAX). On the branch that activates the cloned direct Function
against the first demand, the real Function owner
(`constraints/machine/propagate.rs:212–269`) carries Q unchanged into the
returned Value. If that returned callback lower then meets the second demand,
the same owner carries Q into its result Effect. Positive Stack normalization
at `11–23` prefixes the callback's P=PUSH(alpha_u, tick), giving left weight
P composed with Q (`constraints/mod.rs:3577–3582`).

`constraints/directed_weight.rs:145–170,399–405` gives
`(leading_pops=0,pushes=1)` composed with `(MAX,0)` as `(MAX-1,0)` for alpha_u.
The active tick PUSH is gone on this branch. A different ID is not cancelled
by family equality. The remaining leading POP entry is not the empty weight;
this derivation does not erase it or assert its final compact image. It also
does not say a nominal provider `Con(tick,[])` was deleted by this arithmetic.

This identifies the genuine subtraction constructor and the conditional path
on which its matching PUSH is consumed outside direct's local call frame.
It does not establish that this branch is the complete actual output, that a
provider lower reached x_u, that all replay branches survive, or that the
displayed purity is caused solely by this cancellation.

## 4. The concrete provider is not automatically a lower of x_u

The operation emission has a genuine source owner:
`lowering/body/act.rs:147–195` resolves the Act and builds its operation type;
`lowering/body/signature_helpers.rs:217–256` inserts that resolved effect into
the result row. This is the actual tick source, not a family picked to match a.
The frozen record additionally prints `provider: () -> [tick] ()` and its
direct-call control retains tick. Neither supplies the complete raw scheme
or every replay/projection record of the provider use in observed_direct.

The returned x_u is the tail of K's *negative argument* row. A proof shortcut
“provider has tick, therefore x_u has a tick lower” is invalid at the actual
consumer. For an actual concrete effect comparison,
`constraints/machine/propagate.rs:179–191` calls
`enqueue_row_item_to_upper_row`. At `1007–1042` that owner searches the upper
prefix for the same resolved family. On a match it emits only invariant
argument comparisons. For nullary tick there are zero such comparisons and
**no comparison to upper_tail**. The tail route at `1019–1029` exists only
when there is no matching prefix item. This conclusion holds for any weights,
including a propagated right POP; it follows from the real emission code.
Matching an effect row is not an authentic runtime handler discharge.

There are also real variable-row alternatives, not permission to replace this
matched path by a chosen tail witness. `propagate.rs:104–148` calls
`add_effect_row_upper_bound` for a source variable and row upper.
`constraints/row_effect.rs:88–234` can create weighted residual gamma and
enqueue both source-to-prefix/gamma and gamma-to-the-same-tail comparisons.
Its unweighted reduction at `236–347` records matched lowers and emits their
original upper replay rather than sending every matched concrete item to the
tail. `constraints/machine/bounds.rs:630–733` extrudes/checks and admits lowers,
then obtains incremental row routes and replay actions. These consumers cannot
be replaced by a raw lower-table scan or by independent existential gamma and
output witnesses.

## 5. First remaining premise and economy audit

The direct first-export and consistent fresh-use identity seam is now bounded
by the source scheduler and accepted P/S/K. The first unfinished joined
operational premise is the **actual provider compatibility/replay branch at u**:

> Starting with the resolved provider declaration's actual installed predicate,
> derive its concrete tick lower's native admission and replay into direct's
> instantiated negative callback result-Effect row. Identify the exact row
> prefix match, residual/tail route and any additional lower on x_u from that
> same use. Then derive which returned-callback lower is activated against k's
> demand and whether its complete Effect/projection preserves any independently
> attached tick contribution.

The concrete match consumer has no tail edge; its invocation for the actual
provider and absence/presence of other correlated branches have not been
derived here. The conditional cancellation cannot fill that premise. The
packet therefore proves neither tick preservation on observed_direct nor a
source-qualified contradiction to H. It also does not classify the same
provider's later operation as an independent attachment just by naming it.

The earlier universal/generalized-observation route and concrete liveness
route left an export/use seam untouched. Accepted P/S/K and this scheduler
derivation advance that seam; repeating them would not resolve the new
provider-row branch. Apply the existing economy audit before another equivalent
attempt: scoped subtraction and natural higher-order inference are A/B; recovery
of attachment or projection lineage from display `#0` is D. The actual scheme
instantiator, row matcher/residual constructor, admission/replay owners and
projection query know the joined facts. Derive them there, or have the primary
authorize minimal evidence at those owners. No extra semantic relation,
mandatory annotation, source restriction or reclassification of H is selected.

One next action: primary assigns the exact provider-export-to-row-match/replay
bridge above using this bounded direct-use image, followed by fresh independent
review; Oracle execution remains outside this packet's exhausted budget.

## Snapshot, checks, resources and runtime

Static reads used Python/`cat`/`rg` and read-only `git show`; no executable
Oracle sample, build, test, instrumentation, Git mutation or child dispatch ran.
Initial aggregate captures were truncated, including oversized shared task
records; decisive statement and consumers were reread narrowly. Some guessed
owner paths were absent; located owners are cited above. Six of seven Y3
dependency byte checks matched assigned HEAD. K differs from HEAD's older
file but matches the primary's explicit accepted frozen SHA below, which
governs this packet. All sixteen decisive Oracle byte checks matched the pin.
No dependency was edited. One lightweight read shell ran at a time, zero
heavyweight processes; samples/seeds/ranges: zero. The four-process resource
limit was interpreted as concurrent capacity under the canonical laboratory
rule and disclosed to the primary. CPU/RSS and total wall time were not
instrumented; work remained within the assigned 45-minute attempt.

Requested routing: normal `gpt-6.1-sol` / `high` proof leaf. The callable schema
supports prover; `.codex/config.toml:9–15` registers it and Sol/high defaults;
`.codex/agents/prover.toml` omits role model/effort pins. Observed effective
runtime model/effort: unknown, since no per-agent runtime metadata was supplied.
No Astra, effective override, hot reload, independent review or closure claim.

Frozen Y3 dependencies (SHA-256):

| Input | Hash |
| --- | --- |
| H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| P | `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7` |
| S | `affb7a0fe174c755877fe09bc2633c488b53bc0281ba6cd2082bb7a85aac0535` |
| K, explicit primary pin | `f87f09b54ee64e1be6a22fffd059f0cae4aeb2e340d7dbcca1809280947a8cd5` |
| Direct use-chain | `bafbfe7e08c0a6ce80529b6d78f8be698496b824dec0cc2d5a96b4150c34a3a8` |
| Captured larger-source probe | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| Annotation authority | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Decisive Oracle hashes (paths relative to `crates/infer/src/`):

| Owner | SHA-256 |
| --- | --- |
| `scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| `scc/graph.rs` | `db16401e8bfcdc04a421fdabdc93d333abb56013032f345a065684f2a1cf15a5` |
| `analysis/session/selection.rs` | `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33` |
| `analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `lowering/body/mod.rs` | `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1` |
| `lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `lowering/body/act.rs` | `dfb8bbe305fe369e2fc4f0f413be2009d44343aaa43c3dc1f73dcacf9479fe4d` |
| `lowering/body/signature_helpers.rs` | `8302de665ec38ef4a1cf2e00b762b74c7f5fb85e866526224ec527d487cea4cd` |

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-12-oracle-direct-use-discharge-proof.md`; frozen at handoff, writes stopped.
- Baselines: Y3 `74fff171ce7ee69ffc7c5df02569b7ed9eba5d32`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`; explicit K hash overrides older HEAD bytes only for that dependency.
- Changed dependency hashes: none changed by this leaf; K's already supplied frozen difference is recorded above. Primary revalidates these dependencies at integration.
- Review status: unreviewed bounded source correspondence, conditional returned-path derivation and exact local row consumer fact; no H, complete Call, soundness, principality or production promotion.
- Checks already run: narrow source reads; seven Y3 and sixteen Oracle pinned-byte comparisons; supplied P/S/K hashes checked. No tests/builds/Oracle execution.
- Proposed checkpoint message: `research: trace direct scheme fresh use and provider row-match boundary`.
- Shared-record deltas left for primary/curator: consume K at the acyclic scheme-use boundary; record same-map root POP/PUSH and the matching nullary row consumer's absent tail edge; retain H OPEN with actual provider compatibility/replay and complete output projection as the remaining joined bridge. No shared task/index/theory-status file changed.
