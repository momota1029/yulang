# R93 logical occurrence proof handoff

Status: **CONSTRUCTED / UNCHECKED / WRITES STOPPED**. Independent review,
primary adjudication and kernel acceptance are pending. No theorem below is
reported as proved by Lean before the authorized primary check succeeds.

## Fixed input and authority

- Packet: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R93`, contract r1,
  SHA-256 `e762c73cfd33c60428bb632ef4441bac8f4df2f579a6e0a9c394c5e6ac9b0c77`.
- Manifest r1 SHA-256
  `f78e8b13001b4c7dacd21f0e664d345fcd5d4e1639635d846d9f5df1b5a3762f`.
- Primary-supplied admitted baseline: `853b52673`; contract's original input
  baseline: `21777269598c0629d31e1b6684c87b0c1eebe724`. No Git operation was run
  by this leaf to infer another revision.
- Direct module dependency: `OriginalSourceGeneration.lean`, SHA-256
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`;
  its sole project import `OriginalSourceSyntax.lean`, SHA-256
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- R92 source handoff SHA-256
  `20dba2bbbc87ea93f0f4d131561aa6cca8a1ed013b756dcdd3ad45c1981973bc`.
  These three hashes were read with `sha256sum` and match the fixed packet.
- Output module: `notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR93.lean`,
  SHA-256 `3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192`.
- Only this handoff and that module were written. No scratch, generated,
  cache, audit-project, root-import, compiler, policy or shared-record writes.

## Original sources and correction boundary

The unchanged parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5,7: every supported original source, lawful finite construction history
and retained qualified extrusion; one joint lawful strategy at the original
source scopes, preserving complete external conclusions and correlated
evidence. The birth-level qualification correction remains in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Nothing here changes
qualification, witnesses or that source domain.

Source construction authority is
`notes/design/2026-10-08-source-generalize-definition.md` §2, selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
The decisive binder distinction is construction §3.3: ViewLogic precedes
challenges; Shared is retained once; EventProof remains under its original
event telescope. The opening correction notice and source inventory in
`docs/yulang-source-type-safety-ja.tex` were consulted as source mapping,
not blanket semantic authority. The exact implemented definitions read were
`OriginalSource.Source`, `RuleTree`, `RuleForest`, `sourceRules`, and its
statement/bindings continuations. The App and Lambda equations are at
`OriginalSourceGeneration.lean:111` and `:132`.

## Construction and theorem surface

All names below have prefix
`YulangClosure.OriginalSource.LogicalOccurrencesR93.`.

`Index` is a finite binary positional index with optional occurrence payloads.
`encodeTree`/`encodeForest` traverse every original generated constructor.
`inventory` enumerates `(Route × Occurrence)` entries. Separately, `advance`
and `follow` walk the original `RuleTree`/`RuleForest`, and `observe` reads
only logical `.existsE` nodes (`viewLogic`, `eventProof`, `publishedInstance`).
An `Occurrence` keeps the complete Binder, ordered enclosing `ScopeFrame`s,
and unchanged generated body `RuleTree`.

| Declaration | Exact quantified statement shape |
| --- | --- |
| `inventory_iff_lookup` | For every index, route and occurrence, pair membership in `inventory index` iff `lookup index route = some occurrence`. |
| `encode_lookup` | For every scope, original tree/forest cursor and route, `lookup (encode scope cursor) route = observe scope cursor route`. |
| `observe_eq_follow` | For every scope/cursor/route, `observe` equals `follow` followed by `payload` at the resulting exact position. |
| `source_membership_iff` | For every category, original Source, Context, scope, route and occurrence, membership in its generated `sourceInventory` iff observation at the same route is `some occurrence`. No typing or successful-check premise. |
| `full_route_unique` | Two members for the same complete route in the same generated source inventory are equal as whole Occurrences. No distinct-site premise. |
| `source_provenance` | A member yields an original-tree `follow` result at exactly `.existsE binder body`, with the occurrence's exact enclosing telescope, `logicalKind binder.kind = true`, and equality of its binder/body to that original node's binder/body. |
| `app_exact` | Every Context, Mark, callee, argument and incoming scope: observation at `annotationRoute mark` is the App ViewLogic Binder with the unchanged `appRule`, full premises and original callee/argument `sourceRules` subtrees. |
| `lambda_body_exact` | Every Context, Mark, Formal, pattern, body and incoming scope: observation at `bodyRoute mark formal` is the body EventProof Binder with exact `bodyScope` and `bodyRule`. |
| `app_inventory` | The exact `app_exact` occurrence belongs to the source inventory at that route. |
| `lambda_body_inventory` | The exact `lambda_body_exact` occurrence belongs to the source inventory at that route. |

No theorem adds assumptions to the original parent. The only membership
hypotheses above are in uniqueness/provenance conclusions about that inventory.
All ten declarations have embedded fully qualified `#check @...` and
`#print axioms ...` commands in the leased module. Their **actual printed types
and transitive axiom lists are NOT RUN**, not empty lists.

Routes use `List Bool`. Every unary tree wrapper and a rule's forest edge use
`false`; forest cons head/tail use `false`/`true`; choice left/right use
`false`/`true`. The original cursor fixes what a step means. There is no
site-based lookup or equality assumption. An annotation wrapper adds two
`false` steps. Lambda's body route has eight fixed `false` steps, an extra
`false` at Value entry, then `[false,false,true,false]`. Lengths without/with
annotation are 13/15 (Value) and 12/14 (Computation). `bodyScope` retains, in
order, Description, ViewLogic, Invocation, Receipt, optional actual
Return/rebind execution, and Shared; the body EventProof itself is introduced
at that position rather than inserted into its own enclosing telescope.

## Represented cases and limits

Every original Source constructor is accepted through unchanged `sourceRules`:
all 13 expressions, all 11 patterns, all 3 statements and every container,
default, guard, operation arm, binding, module and block continuation. The
generic traversal covers all 10 RuleTree constructors and both RuleForest
constructors. Neither pattern alternatives nor optional source elements are
discarded. `lambda_body_exact` splits both annotation alternatives and both
formal entry alternatives; formal annotation and raw pattern/body data remain
arbitrary and retained. `appRule` also retains `singletonFormalCall` and its
conditional Role/initial-origin premise without assuming that condition.

The stored subtree is the **original generated RuleTree body**, not a new
semantic source judgment or a separately reconstructed raw Source AST node.
The App/Lambda equations explicitly retain the original raw operands under
`sourceRules`. No general raw-Source-subterm inversion theorem is supplied.
The syntactic telescope retains binder/anchor declarations, not values or
admitted strategies for those declarations. No conversion from this binary
route encoding to `OriginalSourceEvents.ActualKey.route` is supplied.

## Verification evidence and exact handoff

The fixed packet explicitly forbids worker Lean/Lake/checker execution and
reserves at most two bounded direct checks to the primary after independent
review and pushed authorization. Consequently:

- Lean/Lake/checker/build/test calls by this leaf: **0**.
- Pinned configuration actually read: `leanprover/lean4:v4.35.0`, Lake library
  `YulangClosure`, `-j1 -M1024`, empty external package list.
- Actual executable version commands and exits: **NOT RUN**.
- Kernel acceptance and axiom results: **NOT RUN** for all ten theorems.
- Skill checker: **NOT RUN**; it builds dependencies, outside this packet.
- Static `rg`, `sed`, `cat`, `sha256sum`, two module-edit calls and the
  handoff-edit call completed with exit 0 / successful tool returns. A static
  forbidden-token search found only the comment describing the axiom list;
  no `sorry`, `admit`, project `axiom` or checker bypass is present.
- Pinned installed API sources read, without execution:
  `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/Option/Basic.lean`
  (`Option.bind_some`, `Option.bind_none`) and `Init/Data/Prod.lean`
  (`Prod.exists`). This is API lookup, not an executable version receipt.

Primary next action: independently review this frozen module, then perform its
authorized direct file check with the pinned installed Lean and existing
two-module artifacts. The embedded commands produce every required theorem
type/axiom audit without creating another audit file. Preserve the first
actual diagnostic if elaboration fails. In particular, the constructor
equation proofs use `simp only [sourceRules]` followed by reduction; their
interaction with the private generator helpers has not been executed.
No material failed checker log exists: there was no checker attempt.

## Parent application and first remaining premise

If kernel accepted and independently approved, this supplies R92's syntactic
occurrence/provenance segment: the generated App ViewLogic and Lambda-body
EventProof are in an actual finite inventory at unique complete routes, with
their original enclosing binders and generated body retained. It does not
construct their admitted payloads or transport selected formal contracts.

The first semantic premise remains with the original checker/source admission
owner: actual App ViewLogic / body EventProof introductions must admit a
joint payload at their full telescope that preserves the same selected
descriptor/interface/Name/Shared tuple through App readout. Route transport
to ActualKey and raw-source-subterm ownership are additional explicit bridge
work for the source owner. Arbitrary `base.logical`, a proposition definition,
or assumed `LocalLaws` cannot supply this premise. R92's `NO_SAFE_CODE_SLICE`
therefore remains applicable. No source-qualified semantic counterexample
was constructed. Original A/B, joint lift, native correspondence, effect
hygiene, principality, termination and production authority remain OPEN.

One leaf, no children, no heavy process, no CPU/RSS measurement and no
background work. Work stayed inside the finite 1,000-second assignment;
elapsed wall time was not separately instrumented. Writes stopped after this
handoff; only a new explicit primary repair packet may resume them.
