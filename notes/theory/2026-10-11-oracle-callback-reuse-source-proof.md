# Oracle callback reuse: source constructors and the exact unfinished use bridge

Date: 2026-10-11
Status: frozen research source characterization, awaiting independent review; H remains OPEN
Claim class: source-derived constructor/consumer characterization and minimized obstruction; no established counterexample or universal theorem
Yulang3 baseline: `b4c294ae69586805f92e966cbde8fae3ebe2b621`
Oracle source baseline supplied by the primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle inspected checkout: `/tmp/yulang2-oracle-read`
Exclusive output lease: this file only; leaf, no delegation

## 1. Objective, frozen statement and evidence

Trace the exact accepted callback-reuse source from the frozen
[probe](../progress/2026-10-11-oracle-callback-reuse-projection-probe.md)
through real Oracle constructors and consumers. The required outcome is an
actual violation of the original H, or its first undischarged premise. Authority:
[annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The primary subsequently selected the `direct` control in that same
frozen source as the sharper discriminator; the original `route` remains covered
below. This selection does not change H or its source domain.

H is frozen exactly as stated in
[Oracle global effect hygiene](2026-10-11-oracle-global-effect-hygiene-proof.md)
§1:

> For every Oracle source program P in the original successfully lowered source
> domain, every successfully lowered composed-negative concrete annotation
> occurrence a, its original lexical scope sigma and binders, every actual
> copy/instantiation u of that occurrence, and every actual function call/output
> route k involving that occurrence, subtraction authorized by a removes only
> the contribution attached to that exact instance on that route. An independent
> contribution at the same resolved family survives that subtraction. Symbolic
> annotation tails remain connected; every current and future concrete lower
> reaching the relevant receiver encounters the actual retained check. The
> occurrence, attachment, scope, provider/call binder and correlated residual
> lineage remain appropriately identified through actual copying and
> generalization, up to the actual consistent renaming of a fresh use.

The original qualifications also remain: nested arguments reverse polarity;
nested results preserve it; incorrect concrete lowers require authentic errors
and safe nonpublication; successful lowering does not itself certify successful
inference/publication. Complete Call, soundness and required principality remain
separate obligations. No restriction to monomorphic programs, particular IDs,
nullary effects, or direct local calls is added to H.

The candidate instance is the exact source in the probe. Its relevant parts are:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my route(cb: (() -> [tick] ())) =
    ((\() -> {
        cb ()
        \x -> x
    }) ()) cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
my observed_route() = (route provider) ()
```

The frozen evidence records `provider: () -> [tick] ()`,
`direct: (() -> [tick; 'a] ()) -> () -> ['a#0[tick]] ()`,
`route: (() -> [tick] ()) -> () -> ()`, and pure `observed_direct` and
`observed_route`, with completed dump, exit 0, empty stderr. The independent
direct-call control retains `tick`. The binary hash is the probe's
`0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58`;
it was not re-executed or revalidated here.

Fix a to the concrete row in the particular formal's annotation, sigma to that
receiving function's original lexical body, and cb to its actual resolved formal
binder. The call in `observed_direct` occurs outside `direct`'s body; the final
call in `observed_route` occurs outside `route`'s body. The selected policy
authorizes function-local subtraction. Neither temporal separation alone nor
equal family names establishes independent attachment. The provider, output
and residual witness must all be those of this actual source use.

Shared operational assumptions are the inspected source bytes, the frozen
probe's report of completion, ordinary completed method calls, and fresh arena
allocation without ID exhaustion. They do not assume complete replay, exact
projection, exported-ID lineage, an independent contribution, or scope-safe
generalization.

## 2. Source-owned annotation and callback binder

Oracle citations below are paths relative to the inspected checkout's `crates`
directory (`/tmp/yulang2-oracle-read/crates`).

`infer/src/lowering/expr/lambda.rs:1244–1341` builds the formal annotation and
invokes `connect_parameter_computation_detailed`. The latter sets
`parameter_function_boundary=true` during this connection
(`infer/src/annotation/constraints.rs:250–293`).
`connect_value_detailed` at 132–144 emits both actual comparisons: the paired
positive annotation into the formal value and the formal value into its paired
negative annotation. This is an emitted graph, not a supplied transition model.

For `() -> [tick] ()`, `lower_value_bounds:362–389` constructs all four Function
ports, retains Function result polarity, and uses reversed argument ports. The
formal is a negative position of the receiving Function, so the callback result
effect row is composed-negative. `lower_ret_effect_bounds:424–470` allocates its
boundary coordinate e and a fresh stack ID i; `effect_row_stack:657–690`
resolves the concrete atom and constructs `PUSH(i, Set(tick))`. The positive
callback latent effect is the PUSH view of e. The negative companion is a
filtered view of the same e. `predicate_weights:921–925` constructs
`POP(i)` with that concrete filter. The callback's positive result **Value**
is wrapped with `NonSubtract` carrying this predicate
(`lower_value_bounds:370`, `wrap_non_subtracts:848–851`). Thus the raw paired
constructor already places correlated stack evidence on latent output and
returned Value, before any callback call.

i denotes the allocation belonging to this constructor execution; it is not
the numeric name `#0` in the display. Public and erased callable-upper
construction may allocate additional IDs. Those auxiliary allocations cannot
be conflated with i merely because they use `tick` or a shared coordinate.

`lambda.rs:1282–1283,1571–1579` retains the call predicate but clears the
immediate parameter output predicate when the annotation itself is Function.
`mark_lambda_param_call_predicate:919–936` installs the call predicate on the
new local binder. This distinction matters for `direct`: it never calls cb,
so there is no local call-induced predicate in its frame. An explanation in
which `direct` subtracts a first local invocation is false for this source.

`infer/src/lowering/name_ref.rs:145–176` resolves each local reference to the
same DefId and obtains its value through `instantiate_local_value`.
The formal binder constructor at `lowering/pattern.rs:238–281` sets `Def::Arg`
and `scheme: None`; defined parameter construction at `lambda.rs:707–736`
uses that pattern and installs the annotation's call predicate on its locals.
`expr/tail.rs:855–858` returns `local.value` unchanged when there is no local
scheme. The formal references are therefore uses of the monomorphic formal,
not independently chosen fresh providers. No application-side SubtractId is
allocated by `make_app_with_origins:535–624`.

These constructors discharge annotation polarity, original formal binding,
paired coordinate, and source placement of the original PUSH/POP evidence.
They do not establish which of those graph paths survives scheme projection.

## 3. The real first-call and returned-identity path in route

For `route`'s `cb ()`, `local_callee_def:844–850` recognizes the actual Var and
resolved DefId. `local_callee_call_projection:690–705` reads that binder's
stored call predicate. `make_app_with_origins:550–551` calls
`extend_current_latent_predicate`; its owner at 719–726 appends the predicate
to the **current innermost frame**, the anonymous unit lambda. It does not
append it to a guessed outer route or another callback binder.

The block owner (`expr/block_local.rs:94–141,1284–1308`) emits the cb application
as a statement, combines statement/tail evaluation effects, and forwards the
tail Value, the actual identity lambda. `lambda_predicate_subtracts`
(`tail.rs:1058–1077`) retains latent predicates even for anonymous lambdas.
`lambda_output_predicate_vars:1092–1112` wraps both result Effect and result
Value with the same predicate. Consequently there is a source-emitted route
for cb's POP to reach the returned identity Value, which is then applied to the
same cb. This is more precise than describing subtraction only on the first
call's immediate Effect.

The identity's returned callback and later application still require real
Function propagation and bound replay; a syntactic identity is not an
independent-selection license. `constraints/machine/propagate.rs:210–265`
swaps argument ports and preserves result ports. Stack and NonSubtract
normalization at 11–38 emit weighted derived comparisons. Bound insertion at
`machine/bounds.rs:630–731` extrudes, checks, records and generates replay;
its subsumption/projection exits are real. These source rules establish that
the comparisons are generated. They do not prove that every required
route survives all subsumption, row reduction and projection decisions for
this exact source run.

In particular, the later invocation being temporally separate does not itself
show a fresh stack attachment. That is not a rejection of the policy's lexical
limit: preserving the original scope is part of the required H conclusion.

## 4. Provider, scheme export and the suspect later-use consumer

The provider's `tick` has an actual source owner.
`infer/src/lowering/body/act.rs:151–195` builds the operation's signature from
the resolved Act declaration; `body/signature_helpers.rs:217–258` inserts the
Act into the operation result row. `lowering/signature_effect.rs:78–107`
emits positive concrete row items. The ordinary application constructor passes
callee result Effect and callee evaluation Effect into its result Effect
(`expr/tail.rs:535–624`). These facts, together with the frozen provider and
direct-call control, establish a concrete `tick` provider. They do not assign
an arbitrary independent witness to the returned callback.

The actual export seam is:

1. `compact/collect/mod.rs:848–877` requests
   `scheme_projectable_lowers_in_scope`; the source query at
   `constraints/structural_kernel/access.rs:862–898` excludes records whose
   real projection decision is `Excluded`. Stored lowers alone do not establish
   inclusion in the exported callback.
2. `compact/collect/type_nodes.rs:1–115` carries outer weights into positive
   Function **result** ports, including a returned Function's latent Effect.
   Its negative Function branch reverses the carried side at 117–135.
   Negative effect-stack compaction at 545–562 may expose allowed families as
   concrete row prefix items. This can explain the argument-side `tick` row
   without proving the identity of the returned PUSH.
3. `generalize/mod.rs:177–238` selects stack quantifiers through two paths:
   live covariant PUSH occurrences at quantified coordinates, and declared
   facts whose `fact_by_id(id)` result has `Subtractability::All`
   (`199–204,867–889`). It then prunes stray IDs. This is not a census of all
   original annotation IDs. The candidate's concrete `Set(tick)` fact does not
   establish the All branch. `compact/finalize.rs:586–603,837–839` resets
   compact filters to All when exporting principal Stack nodes.
4. `analysis/session/instantiate.rs:14–90` finalizes each generalized component
   into the poly arena and installs its actual scheme. Merely capturing a
   provenance witness does not establish projection completeness.
5. `infer/src/instantiate.rs:621–647` clones the actual scheme with one map.
   `fresh_subtract/clone_subtract:741–768` preserve retained identity under its
   consistent renaming. Then `wrap_predicate_with_stack_pops:770–787` adds
   **POP count `u32::MAX` for every selected stack quantifier** to the cloned
   root predicate. This consumer performs no lexical-scope check against
   `direct`, `route`, or `observed_direct`.

The last operation is the localized suspect. The direct source has no local
cb call to justify an immediate call-frame POP, yet its actual scheme use runs
this quantified-root POP constructor. Function propagation carries root
weights into returned Function outputs. The local algebra composes by exact
ID (`constraints/directed_weight.rs:145–170`); another ID is not cancelled
because its family is also `tick`.

This source characterization is not a conditional theorem supplied as the
packet outcome. It identifies the concrete source/data premise that must be
resolved before that suspect can be called the actual loss cause.

## 5. What the dump consumer does and does not establish

`yulang/src/main.rs:2988–3005` builds poly and calls the ordinary surface
dumper; `support.rs:1308–1313` prints the text and each reported error.
`poly/src/dump/surface.rs:172` formats the installed scheme.
`type_format/formatter.rs:90–108` renders `scheme.predicate`, with role
predicates; it does not render a live lower/filter table or a raw quantifier map.

The ordinary formatter emits each positive concrete effect item: Function
formatting at 480–491 calls `pos_row_inline`, whose traversal at 900–976
recurses through Row/Union, suppresses Bot, names a Var, and renders other
items. `type_format.rs:591–597` omits the effect brackets for an empty part
list. Stack rendering at `formatter.rs:256–270` may hide the special
quantifier POP(MAX) wrapper but recursively renders its inner type. Therefore
the frozen pure `observed_direct` is not explained by this formatter simply
hiding a concrete `tick` row item in its output Effect. Conversely, a surface
`#0` is assigned by a display-local name map (`type_format.rs:580–589`), not
a raw ID or a proof of annotation-to-export lineage.

The text proves neither the original ID's membership in `stack_quantifiers`
nor the actual per-use clone mapping. It also does not establish a runtime
operation or a sound complete typing. No such claims are imported from exit 0.

## 6. First residual gap and economy audit

No source-domain exclusion for this ordinary accepted source was established.
No genuine counterexample to H was established either. The first residual
source/operational premise is now the following joined export-to-use fact,
with `direct` preferred because it removes the anonymous first-call path. This
is the smallest currently identified operational package for evaluating this
candidate, not a proof that every clause below is logically necessary to
refute H:

> For the actual generalized `direct` scheme used by `observed_direct`, identify
> the raw stack entry descended from a's i, its selected stack-quantifier
> membership and actual clone map, the provider-to-argument/returned-callback
> projection and replay records, and the later callback call's Effect route.
> Establish whether the root POP(MAX) on that exact clone cancels a's surviving
> latent PUSH outside sigma. Separately determine whether the actual provider's
> concrete `tick` lower has an independently surviving output route or was
> excluded/consumed at an earlier row/projection owner; this addresses H's
> independent-contribution clause, rather than being necessary to establish
> every possible scope-escape counterexample.

This is a joined fact for one actual use. Separate existential witnesses for
the provider, row tail, returned Value and visible stack cannot establish the
proposed operational explanation.
The constructor trace does not assume it; the frozen display lacks those raw
records. An exact static derivation of those projection/replay decisions, or
a separately authorized minimal observation at these owners, is needed.
Until then, the root POP is an identified mechanism, not a demonstrated cause
of the displayed loss. The candidate is not silently classified as outside H,
and same-provider reuse is not promoted to independent attachment by naming it.

The preceding universal source lane and this concrete source lane meet the
same export-to-observation seam by different methods. Before another equivalent
attempt, apply `rules/compiler-engineering.md`'s economy audit: scoped
subtraction and ordinary higher-order inference are A/B; recovering raw
annotation-to-scheme incidence from `#0` would be D. The owning annotation,
projection, finalization and instantiation constructors already possess the
necessary identities. Observe or derive that joined lineage there; do not
invent a reconstruction relation, restrict source programs, add mandatory
annotations, or relabel H as optional C research. No implementation change or
semantic adoption is authorized by this note.

One next action: primary obtain the exact `direct` export/use lineage above,
using the smallest authorized evidence at its existing owners, and then assign
fresh independent review of the resulting source-qualified conclusion.

## 7. Checks, resource use and runtime

Only the leased note was written. Commands were lightweight `cat`, `sed`, `rg`,
`rg --files`, `sha256sum`, and read-only `pwd`/`git rev-parse HEAD`; the mistaken
full baseline in the initial packet was corrected by the primary to the actual
HEAD stated above. Some broad initial captures were truncated; decisive owners
were reread narrowly. A few guessed source paths were absent; actual owner paths
were found and read. No Oracle execution, Cargo/build/test, instrumentation,
network request, Git mutation, compiler/test/shared-record edit or delegation
occurred. There were zero executable samples and zero heavy processes, with at
most four independent lightweight commands concurrently. CPU/RSS/wall time
were not instrumented; no numerical quota was supplied beyond that concurrency
and no-execution boundary. Work stops at this precise evidence gap.

Requested runtime: `gpt-6.1-sol` / `high`, normal proof leaf. Config declares the
prover role without role-level model/effort pins and Sol/high defaults. Observed
effective model/effort: unknown; no tool runtime metadata was supplied. No Astra,
reload, override, independent-review or theorem-promotion claim.

## 8. Dependency snapshot and commit packet

SHA-256 of decisive dependencies inspected in this packet:

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-callback-reuse-projection-probe.md` | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Oracle `infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle `infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle `infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle `infer/src/lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| Oracle `infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| Oracle `infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| Oracle `infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| Oracle `infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| Oracle `infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| Oracle `poly/src/dump/type_format/formatter.rs` | `10ef65e06243dff901d83e37bde22b99065c05dc92a31872fb8179397c3c2265` |

Commit packet:

- Exact leased/change path: `notes/theory/2026-10-11-oracle-callback-reuse-source-proof.md`; writes stop at handoff.
- Baseline: `b4c294ae69586805f92e966cbde8fae3ebe2b621`; Oracle source supplied as `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency changes: none made by this leaf; primary revalidates the frozen dependency cone before integration. Runtime source/binary correspondence is inherited from the probe, not re-executed.
- Claim/review: unreviewed source characterization and exact obstruction; no counterexample, H closure, source-generalization equivalence, complete Call, soundness, principality or production certification.
- Checks: source-owner reads/searches, decisive dependency hashes and leased-note whitespace review; no executable check/build/test authorized or run.
- Proposed checkpoint: `research: localize Oracle callback escape hygiene bridge`.
- Shared-record deltas left for primary/curator: retain the frozen probe as candidate evidence; record `direct` as the sharper scope discriminator, the actual quantified-root POP(MAX) owner, and the missing joined raw export/use/provider replay evidence. Keep H and all dependent production/F5 gates OPEN. No shared task/index/theory-status edits.
