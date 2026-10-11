# Oracle direct callback: later-use source owners

Date: 2026-10-12
Status: frozen unreviewed research audit; H and actual-use bridge OPEN
Claim class: source-derived bounded constructor/consumer characterization, with an explicit conditional fresh-use lemma
Assigned Y3 baseline: `74fff171ce7ee69ffc7c5df02569b7ed9eba5d32`
Branch: `research/simple-sub-intrusion`
Oracle baseline/read root: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; source inspection, no delegation

## Objective and exact premise

Audit the real later-use owners for:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

This fragment is extracted from the larger source in the frozen
[display probe](2026-10-11-oracle-callback-reuse-projection-probe.md), §2.
That larger invocation reported `observed_direct: () -> ()`; the separate
direct-call control reported `[tick]`. The extracted source has not run alone.
Neither a display `#0` nor two equal displayed families establishes raw identity.

Authority is [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The original [H statement](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1 retains its full successfully lowered source domain, original occurrence,
scope/binders, every actual use/call/output route, independent same-family
preservation, symbolic connection and present/future checks. This audit does
not select new language meaning or produce an H counterexample.

The [use chain](2026-10-12-oracle-direct-return-use-chain.md) and
[liveness audit](../theory/2026-10-11-oracle-direct-liveness-proof.md) supply
earlier owner locations and their stated gaps. Accepted
[K](../theory/2026-10-12-oracle-direct-return-stack-cleanup-proof.md), hash
`f87f09b54ee64e1be6a22fffd059f0cae4aeb2e340d7dbcca1809280947a8cd5`,
establishes the installed scheme only for its isolated declaration slice before
external uses. Its transfer to the actual larger program is not a premise
silently supplied here.

Shared operational assumptions: inspected source bytes, normally completed
methods, successful resolution of the designated declaration/operation and
fresh allocation without exhaustion. Candidate premises needing further
evidence are the **actual installed scheme read by this use having K's image**,
the actual provider records/replay, and a complete semantic final observation.

## Scheme selection and the conditional fresh-use lemma

Oracle citations below are relative to `crates/infer/src/` unless qualified.

`lowering/name_ref.rs:83–115` makes a fresh use Value and exact-pure reference
evaluation Effect for each top-level name, records its parent/target, and queues
`ApplyRefResolution`. `analysis/session/lifecycle.rs:1092–1100` resolves that
reference and supplies `SccInput::UseResolved` with those same objects.

`scc.rs:266–320` distinguishes already quantified targets, internal SCC uses,
and cross-component edges. `scc/graph.rs:496–515` admits a finished component
only after its outgoing dependencies clear. `scc.rs:335–355` emits its
`QuantifyComponent` before incoming `InstantiateUse` events.
`analysis/session/selection.rs:1040–1119` consumes these in order and routes
`OpenUse` separately to the target-root connection.

In the designated acyclic fragment, `observed_direct` refers to `direct` and
`provider`, and `provider` refers to the operation; `direct` returns its local
`cb`. The local reference owner resolves `cb` immediately
(`name_ref.rs:146–169`), without queuing the top-level use event. Thus the ordinary
incoming use route supplies a fresh scheme use after quantification, rather
than an early target-root constraint through `OpenUse`. This source ordering
does not alone prove that all larger-program construction/prepass state is
identical to K's isolated input.

The actual scheme read is `Def::Let.scheme` at
`analysis/session/instantiate.rs:363–369`, not the compact `self.schemes` store
or its printed text. Fresh declarations take the ordinary unimported branch at
448–455; imported/finalized-template validation is a distinct branch. The batch
owner at 311–335 installs the cloned predicate into the same use Value via
direct lower insertion or subtype routing (505–520).

**Conditional fresh-use lemma.** If that actual stored scheme quantifies K's
original coordinate x and ID α and contains K's paired occurrences, then this
ordinary completed use allocates x′ and α′ before cloning, shares those mappings
across both occurrences, and wraps the root with POP(α′, `u32::MAX`).
This follows directly from `instantiate.rs:91–101,516–529,625–636,732–786`:
the one instantiator has memoized variable/ID maps; all quantifiers are mapped
before the root is cloned. Recursive Function ports use that same object
(798–807,861–870); Stack and NonSubtract clone their weights (835–841,891–894),
and `clone_stack_weight:983–999` renames each entry with `clone_subtract`.
The negative Row tail uses `clone_neg`, hence the same x′ (887–889).
This establishes consistent renaming for the supplied scheme image; it neither
establishes that image in this context nor proves cancellation on a later call.

## Provider incidence and its concrete contribution

The effect family is source-supplied at
`lowering/body/act.rs:166–195`: resolve the operation's act TypeDecl and build
its type application. `lowering/body/signature_helpers.rs:217–256` inserts that
concrete atom into the operation return Effect, even when `ping`'s written
signature has no effect row. `SignatureLowerer::lower_effect_row_pos`
(`lowering/signature_effect.rs:78–107`) emits its positive Row. These inspected
owners introduce a nominal family atom, not an annotation SubtractId.

There are two real suppliers: the operation declaration constrains its public
root (`lowering/body/act.rs:106–127`), and the qualified reference additionally
constrains the operation use Value directly
(`lowering/expr/block_local.rs:990–1048,1066–1091`). The qualified reference's
evaluation Effect is exact pure (996–997); tick belongs to its callable's latent
return Effect. Ordinary application of `ping` uses the same four-port consumer
as the later applications. Defined-lambda output connects the provider body
Effect to its returned Effect (`expr/lambda.rs:797–808,954–975`;
`expr/tail.rs:1084–1109`). This identifies the concrete source contribution's
supplier; the exact generalized provider scheme and active replay records for
the captured invocation are not reconstructed here.

At `(direct provider)`, `make_app_with_origins`
(`lowering/expr/tail.rs:543–563`) puts the **same provider reference's Value and
evaluation Effect** in the demand's argument ports. It does not independently
select another provider. Its return Value is a fresh result coordinate r₁;
its fresh call Effect is c₁. The argument's pure evaluation Effect is distinct
from the provider's latent tick. No direct argument-latent-effect-to-result
edge is emitted by this application constructor.

`constraints/machine/propagate.rs:212–270` is the owning Function consumer:
arguments and their weights reverse; result Value and Effect preserve direction.
Comparing the provider callable with the negative callback annotation therefore
has its own result-Effect comparison. **The prefix/tail distinction matters.**
If this comparison reaches `Pos::Con(tick, [])` against
`Neg::Row([Con(tick, [])], Var(x′))`, the matching-family branch at
`propagate.rs:1007–1042` performs invariant argument checks; it does not emit
that tick as a lower of x′. An unmatched family goes to the tail. If the lower
is instead a Var, `row_effect.rs:88–234,236–320` selects actual weighted or
unweighted residual/reduction paths. Their weights and bound records must be
supplied before choosing a branch. Thus “provider has tick” alone does not
establish “tick reaches x′ or the later call Effect.” This is a source-rule
discriminator, not an executed branch claim.

## Returned callable, second call and observation

The first call's output is r₁. Function return decomposition targets that exact
coordinate; it does not attach the original cb LocalBinding metadata to the
`Expr::App` constructed at `tail.rs:626`. At the second application, the callee
is this App and its evaluation Effect is the first application's Effect e₁.
`local_callee_def` accepts only Var (`tail.rs:844–850`); therefore the second
call obtains neither cb's local call predicate (690–705) nor the unannotated
Arg wrapper (740–758). Its demand uses bare fresh c₂ and fresh result r₂.
This rules out that particular local-predicate owner as the explanation for
the displayed purity; it leaves type-weight propagation active.

For each application, `tail.rs:615–624` connects the callee evaluation Effect
and the returned call Effect to that application's Effect. Hence the second
construction emits e₁ ≤ e₂ and c₂ ≤ e₂. Its direct callee constraints consume
r₁, not an unrelated returned callable. These are generated constraints, not
proof of their terminal bound state or complete Call meaning.

The exact future-check owners are `bounds.rs:3213–3255` (register and scan current
lowers), 3285–3360 (new lower and recursive concrete/variable filtering), and
`add_lower_bound:630–732` (extrude, check/erase left filter, subsumption/insertion,
then filter invocation and replay scheduling). They check a retained actual
filter once supplied on its receiver. This audit has not supplied the actual
filter/receiver or terminal provider-derived lower of c₂/e₂. It cannot conclude
that tick was checked there, bypassed, or removed by the quantified root POP.

The observed definition's lambda output uses its actual body Effect as the
Function return Effect (`lambda.rs:954–975`; `tail.rs:1092–1109`). Component
generalization/finalization and `set_def_scheme` are the output owners
(`analysis/session/instantiate.rs:14–83`), distinct from raw bound insertion.
The dump reads the installed Let scheme
(`crates/poly/src/dump/surface.rs:139–172`), and the formatter renders its
predicate and Function return row
(`crates/poly/src/dump/type_format/formatter.rs:64–93,480–491`). This is a
stored-scheme display observation. Complete projection, row-rendering fidelity,
CLI dispatch for the captured run, and runtime operation behavior are not
proved by locating these readers.

## First remaining premise and bounded result

The first unestablished use-specific premise is the **actual installed direct
scheme selected at `prepare_instantiated_use` having K's x/α image in the larger
program**. SCC ordering explains why this acyclic incoming use is delayed; the
complete contextual equivalence of its constructor/prepass/export input to K
is still required. After that, the next seam is the joined provider comparison,
residual/replay records and their projection into the same r₁/c₂/e₂ route.
The explicit matched-row branch prevents replacing that seam with a family
membership assertion. The source return reference identifies cb, but does not
by itself establish complete later runtime provider behavior or independent
H contribution attachment.

This method advances ownership and discriminates actual row routing; it does
not repeat the root-weight algebra, prove universal H, or reinterpret scope.
No counterexample is established. Complete H, complete Call, soundness,
principality, Oracle source adequacy and Y3 implementation/cutover remain OPEN.
Recommended next action: the primary's actual-use proof/source lane supplies
one joined contextual scheme/use/provider/replay derivation at these owners,
then applies the conditional renaming lemma to those same objects.

## Frozen dependency snapshot and checks

SHA-256 values below describe inspected bytes; no dependency was written.
Two Y3 inputs (use chain and liveness) were also matched to loose objects from
the assigned pin. A bounded read of loose object files could not recheck packed
objects; K is absent from that Y3 tree and is instead the explicitly supplied
frozen-hash dependency. Oracle's detached HEAD file matches the Oracle pin.
Full baseline byte equality is left for the primary's integration checks;
hash equality is not inferred from HEAD alone. Unrelated Y3 HEAD movement does
not replace the assigned baseline.

| Y3 direct input | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-12-oracle-direct-return-use-chain.md` | `bafbfe7e08c0a6ce80529b6d78f8be698496b824dec0cc2d5a96b4150c34a3a8` |
| `notes/theory/2026-10-11-oracle-direct-liveness-proof.md` | `eeb4a6bc838fdbc1007cc2565e6654cf382f1c77d65583e318d74e2d8a4bcb8f` |
| `notes/theory/2026-10-12-oracle-direct-return-stack-cleanup-proof.md` | `f87f09b54ee64e1be6a22fffd059f0cae4aeb2e340d7dbcca1809280947a8cd5` |
| `notes/progress/2026-10-11-oracle-callback-reuse-projection-probe.md` | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

| Oracle path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `crates/infer/src/analysis/session/selection.rs` | `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/infer/src/scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| `crates/infer/src/scc/graph.rs` | `db16401e8bfcdc04a421fdabdc93d333abb56013032f345a065684f2a1cf15a5` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/lowering/body/act.rs` | `dfb8bbe305fe369e2fc4f0f413be2009d44343aaa43c3dc1f73dcacf9479fe4d` |
| `crates/infer/src/lowering/body/signature_helpers.rs` | `8302de665ec38ef4a1cf2e00b762b74c7f5fb85e866526224ec527d487cea4cd` |
| `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `crates/infer/src/lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/poly/src/dump/surface.rs` | `4d0d8f4b0c8c1cee3ab44cbb58486cccfe7fa4a88ff09a23b3401990e89f76e4` |
| `crates/poly/src/dump/type_format/formatter.rs` | `10ef65e06243dff901d83e37bde22b99065c05dc92a31872fb8179397c3c2265` |

Checks: bounded `cat`, `rg -n`, `rg --files`, Python line/hash reads, loose-object
byte comparisons and leased-note integrity. Initial broad context captures were
truncated; decisive owners were reread in smaller slices. Guessed formatter,
row and register paths were absent and were replaced with located owners.
No Oracle invocation, compiler experiment, tests/build, instrumentation, network,
Git command/mutation, production/test edit or question-board access ran.
There is no independent executable oracle: the evidence is the production source
plus the separately frozen earlier display probe. No seeds/ranges, mutations or
new samples; no exhaustive search. A selected branch's inputs, terminal replay,
failure/error consumer and semantic output adequacy remain explicit omissions.
Four top-level lightweight shell/Python invocations were used; later reads reused
one Python process and sequential short rg children (at most two local processes
active together). Heavyweight process count is zero. CPU/RSS were not measured;
the bounded attempt ended within 30 minutes. Runtime model/effort metadata is
unknown; no model change or child spawn occurred. Writes stop before review.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-oracle-direct-use-owner-audit.md`.
- Baseline SHA: Y3 `74fff171ce7ee69ffc7c5df02569b7ed9eba5d32`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency hashes changed by this worker: none; snapshot above, K explicitly supplied outside the Y3 pin.
- Review status: frozen producer audit, independent review pending; conditional/source characterization only.
- Checks already run: narrow source/hash and two pinned-object comparisons; note integrity; zero execution/build/test.
- Proposed checkpoint message: `research: audit direct callback fresh use and provider effect owners`.
- Shared-record deltas left to primary/curator: attach the conditional fresh-use lemma, SCC-order boundary and matched-prefix discriminator to the actual-use gate; retain H and joined contextual scheme/provider/replay/output obligations OPEN. No shared task/index/theory-map or question bundle changed.
