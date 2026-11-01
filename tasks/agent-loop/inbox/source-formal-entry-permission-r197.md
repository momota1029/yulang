# R197 — frozen source-definition obstruction r1

Session: `SOURCE-FORMALENTRY-PERMISSION/R197`. Author:
`/root/r196_canonical_model`, registered `lean_prover` leaf; no descendants.
Requested Sol/high; observed model/effort UNKNOWN. Baseline supplied by primary:
`yulang3` / `90d757d2f`. Exact leases: this handoff and
`notes/theory/lean/YulangClosure/SourceFormalEntryPermissionR197.lean` only.
R196 outputs remain frozen. Outcome: **BLOCKED_SOURCE_DEFINITION**.
Independent review and integration remain primary-owned; no self-certification.

Contract r1 SHA `59dd1b847bf7b90af55e98ad139b2792c471da2749218dd14e1e4c066f8ef0ab`.
Activation supplied SHA `6494907a2b2e31662491959cdcf3ffcf7e75fefd23b2761a7d9f8660110d4da5`;
current activation SHA after the primary appended this session's runtime
acknowledgement: `d9252f1ebe980ecbdc126693e5f03681f99f11426a7b3f96757266747f053526`.
This receipt update was explicitly reported to the primary. Contract and
semantic input hashes match the issued pins.

## Fixed policy and exact missing original equation

Read the selected source policy, not a native model as semantics:
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2.
It authoritatively fixes composed Function polarity: negative `[E]` permits
local subtraction; positive `[E]` allows the resolved concrete member at that
position. Effect identity includes resolved arguments. A symbolic variable is
not collected as a concrete grant, but keeps its constraints and connections.
Permission creates no inflow, closes no open row, and performs no subtraction.
The actual handler handles; handling signal from signal|write leaves write.
No new semantic vote is required for this policy.

The first unavailable source-definition equation in the pinned surface is:

> At `formal.annotation = some a`, the original resolved declaration **a**,
> in the actual Lambda/formal occurrence and original lexical/type scope,
> denotes its complete typed annotation positions and their composed Function
> polarities, exact concrete effect instances/type arguments, source row/path
> identities, and symbolic variables with their original dependency links.

This names the missing original declaration interpretation; it is **not** a
proposed registry grammar, a new abstract field, an assumed source readout,
or a successful-permission predicate. The input must come from the actual
original annotation declaration, not an inferred type or numeric ID spelling.
The policy determines the permission action once those positions/members are
known; it does not define how resolved ID `a` denotes them.

Exact source locators: `OriginalSourceSyntax.lean:23,31–39` defines
`YulangClosure.OriginalSource.Annotation := Nat`, and
`Formal.annotation : Option Annotation`, with site/name/outerComputation.
The header says IDs refer to original resolved syntax/declaration tables.
`OriginalSourceGeneration.lean:132–172`,
`YulangClosure.OriginalSource.sourceRules`, copies that same ID into
`sourceFormalRole` at the original formal context. Both receiptFormation and
Value `entryForceReturnRebind` / Computation `retainedEntry` remain in their
actual entry scopes. The generated atom records no concrete effect row or
typed-position interpretation. All annotation references in these two pinned
files were inspected; no declaration lookup/meaning equation is defined there.

The absence of that equation from these inputs does not prove that no original
interpretation exists elsewhere, or that a new language decision is needed.
The primary explicitly confirmed this bounded stopping outcome.

Owner candidate: **primary's original source-annotation declaration/meaning
lane**, owning the resolved annotation table and its typed-position denotation.
`OriginalSourceGeneration.sourceRules` is the receiving FormalEntry rule owner.
Next evidence is the exact existing original declaration equation and version,
or an authorized source-grounded construction of it, retaining every coordinate
above. Native collector/consumer owners remain downstream and WAITING.

## Why existing finite results do not supply it

- `ComputationPermissionEntryR39.Annotation Id` already contains owner,
  position and an optional `Row Id`; that row already contains position,
  concrete vector and symbolic variables. Its `Action` is supplied expanded
  data, not an `OriginalSource.Annotation` declaration interpretation.
  `prepare`/`permissionFor` validate/copy that data under their own premises.
- `FormalEntryPrestateBridgeR169.Parameter.annotation` likewise contains the
  expanded R39 `Annotation Id`. `successful_nonempty` assumes its successful
  finite `Trace`; it proves copied payload/publication and unchanged inflow,
  not the original ID-to-typed-position equation.
- `FormalEntryOriginR171.successful_annotation_origin` retains an already
  supplied annotation through its event construction/scan and still assumes
  the R169 trace. Its `roleFor` reads that model's optional row; it is not an
  interpretation of original `Formal.outerComputation` or declaration ID.
- `OriginalEffectHygiene` proves original publication/replay/lifetime facts;
  its opening scope explicitly leaves source annotation/profile/path and
  complete permission interpretation open. Reuse remains valid through its
  real premises. R116/R45 are downstream retained-record/consumer models.

The bounded R172 source-judgment note was read for context only; its earlier
collector/preparation defects and historical Rust excerpts were not treated
as current source semantics. No Rust source path, including either quarantined
runtime path, was accessed. No internal-ID trace was started.

## Parent application and scope retained

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This source definition blocks the concrete interpretation of Lambda's
`sourceFormalRole` and its source-owned annotation permission. Consequently
the same generated constraints/assignment cannot yet be connected to that
original local atom in `Satisfies K E (Build C S)`. Reconstruction cannot
consume an uninterpreted atom as a proof of the original policy. Constructing
one parent witness `e` and proving `sameScoped s x e a` also remain open.
No successful Trace, expected permission, `prepare`, `permissionFor`, source
admission, sourceJudgment or readout premise was added to a new theorem.

Value and Computation entry both remain supported; the outer written
annotation boundary, nested Function polarity, Lambda/formal/parameter
identities, original source row/binder/scope/path, resolved effects and type
arguments, symbolic links and actual inflow remain required. No constructor,
Call/effect port or shared witness was removed. Semantic permission construction
and its application are omitted openly. This is neither a source-qualified
counterexample nor a proof of semantic underdetermination.

Before/after: **5/5 prerequisite packages open; 0/4 roots closed**.
Distinct effect-hygiene delta: **zero**; the source FormalEntry permission
premise remains open at the declaration interpretation above.

## Actual pinned check and declaration audit

Artifact SHA-256:
`9c3f46d7e5b4b8aec1f542fc15fbd68726d08039d979ba1ecacc1a19dd252794`.
The Lean file is a documented stopping surface with printed existing
definitions, **zero new theorem declarations** and no permission/model instance.
Delivered theorem types / theorem axiom audits: **not applicable (zero)**.
No theorem of permission or soundness is claimed from module acceptance.

From `notes/theory/lean`, read-only `elan which lake` returned
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, exit 0,
with warning that latest-release query failed and the existing pinned version
was used. The resolved executable returned:

```text
lake --version: Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
lake env lean --version: Lean (version 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Both version commands exited 0. Exactly **one** targeted check ran:

```sh
timeout 120s /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.SourceFormalEntryPermissionR197
```

Exit **0**; reported module compilation **3.8 seconds**, five jobs. Actual
printed definitions/types:

```text
@[reducible] def YulangClosure.OriginalSource.Annotation : Type := Nat
structure YulangClosure.OriginalSource.Formal : Type
fields:
  Formal.site : OriginalSource.Site
  Formal.name : OriginalSource.Name
  Formal.annotation : Option OriginalSource.Annotation
  Formal.outerComputation : Bool
def YulangClosure.OriginalSource.Formal.entry : OriginalSource.Formal → OriginalSource.Entry :=
fun formal => if formal.outerComputation = true then OriginalSource.Entry.computation else OriginalSource.Entry.value
OriginalSource.sourceRules : OriginalSource.Context →
  {category : OriginalSource.Category} → OriginalSource.Source category → OriginalSource.RuleTree
def YulangClosure.SourceProblem.InferenceSoundness :
  {S C X E D A N : Type} → SourceProblem S C X E D A N → Prop :=
fun {S C X E D A N} p =>
  ∀ (s : S) (x : X) (d : D) (a : A),
    p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
Build completed successfully (5 jobs).
```

No failed Lean check or timeout occurred. The skill checker was not used:
there are no new theorems, and its temporary audit tree is forbidden by the
packet. Existing source definitions were printed directly from the leased
module. No second check, broad/default build, test, dependency update, global
default change, installation, new environment/cache/target/scratch or Rust/Cargo
execution was attempted.

## Input and generated-output pins; cessation

All contract-pinned inputs match:

```text
Contracts 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
OriginalSourceSyntax 3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration 126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
annotation-effect-hygiene-integration a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
OriginalEffectHygiene 926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f
ComputationPermissionEntryR39 748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e
SuppressionPermissionR116 2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a
InternalPermissionIncidenceR45 9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f
FormalEntryPrestateBridgeR169 bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4
FormalEntryOriginR171 03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6
```

Pinned project unchanged: Lean 4.35.0, `YulangClosure`, no external packages,
`-j1 -M1024`. Sole existing-cache ownership explicitly granted. Generated
outputs under `notes/theory/lean/.lake/build/`:

```text
lib/lean/YulangClosure/SourceFormalEntryPermissionR197.olean
  fdf8cdefdd286c39b3eed9498c480d29f73119630fb22a3871a0cb461292ab99
lib/lean/YulangClosure/SourceFormalEntryPermissionR197.ilean
  54d8b710ead15f0ccf8d6eb845ba472016bf3b581fcf5db517ecc1df459eea53
lib/lean/YulangClosure/SourceFormalEntryPermissionR197.trace
  9dbc1cc00f3cf1f84d4830ec1a7d645e7e3f860b8eb6e2151763b3fcc6184c57
ir/YulangClosure/SourceFormalEntryPermissionR197.c
  b231dcd35eb9f3d974c6a7b2b3fe71c2e3b8041709b3fd8abee1574fafd8adda
ir/YulangClosure/SourceFormalEntryPermissionR197.setup.json
  575a26c8b974c069e37f72b2c7d8d59e1f91000e9b394edd57361592d0c52dcd
```

Lake also wrote the adjacent `.olean.hash`, `.ilean.hash`, `.c.hash` files.
No scratch/audit/log path. Only the two leased outputs were authored, plus
these authorized generated cache outputs. No root imports, shared records,
other workers' files, compiler sources, rules/configuration, questions or Git
state were written.

Resource bound: 2400 active seconds, at most two 120-second focused checks;
one check used, no timeout. UTC observation: initial bounded read completed
14:13:17, successful check/hash receipt 14:15:53 on 2026-11-01. Aggregate active
seconds/peak RSS are not instrumented; do not treat this interval as CPU time.

**STOPPED; writes stopped after this r1 handoff.** No running checker or
descendant. Cache ownership returns to primary on intake. Next bounded request:
`R197-ANNOTATION-DECLARATION-MEANING-1`, parent and source owner above; supply
the exact declaration-to-typed-position equation without assuming successful
permission construction. Frozen bytes await independent review.
