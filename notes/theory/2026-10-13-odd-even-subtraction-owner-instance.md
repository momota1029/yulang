# Odd/even subtraction: original scoped owner instance

Status: frozen unreviewed research checkpoint; requested child judgment unconstructed
Claim class: bounded source/owner characterization and precise missing input
Baseline: `8f0c9cbb5ac207b18ad374d2e26610c02922604d`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; leaf, no delegation or Git mutation
Method: inspect adopted source rules and actual import/operator/literal suppliers;
stop at unavailable original environment data, without another Call reconstruction

## 1. Frozen claim, original binders and hypotheses

The source is exactly:

```yulang
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

Keep distinct parameters `n_O` and `n_E`, source definition Values `O` and `E`,
and the original occurrence of **`n_E - 1` in even's call to odd**. The parent
claim and binders are those of
[odd/even intrusion preservation §§1–2](2026-10-13-odd-even-intrusion-preservation.md).
The approved inner extrusion origin/receiver is E/O. Its actual argument parent
`T` is the subtraction result, not an asserted identification with `n_E`'s type.

For every actual lawful original instance to which this child is applied, use
that instance's original `Γ_E`, dependent `W_E`, registered `n_E`, operator
association/resolution, imported contracts, providers and literal introduction.
The required conclusion is:

```text
Γ_E; W_E ⊢ n_E - 1 : Comp(E_arg,T)
```

It must retain the original whole computation and its delayed-argument formation
for the enclosing `odd(...)`, together with every complete operator Call
interface if the actual selected source rule constructs Calls. `E_arg,T` are
jointly determined by that original construction; no separate marginal witnesses
may be chosen. This is neither a universal judgment in arbitrary invalid
environments nor permission to replace the original quantifiers by one integer
instance. The parent preservation/principality scope remains unchanged.

Existing hypotheses are the exact source/binder choice, accepted E/O ownership,
and adopted general source schemas. The packet supplies **no concrete ambient
import table, selected subtraction declaration/provider, original literal-1
certificate or independent complete operator law**. Their existence cannot be
added to the hypotheses and then reported as discharge of the requested child.

Excluded choices: Int for the formal/result; purity; arity/currying/tuple encoding;
primitive rather than Call; a chosen Sub implementation; source rejection;
independent attachment/provider/witness/residual selections; and shrinking the
world, future-context, alternative, guard or history domains.

## 2. Governing semantic owners

The following adopted sources, rather than their navigation summaries, govern
the inspected semantic bridge:

| Source and exact section | What is selected and what remains independent |
| --- | --- |
| [Source Generalize definition](../design/2026-10-08-source-generalize-definition.md) §§2–3 | Selects construction §§3–5; expressly retains genuine primitive, initial-world and local constructor premises L1–L5. Supersedes no independently fixed primitive meaning or production resolver. |
| [Source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md) §2 L1–L5; §3 and §3.1 | Literal/authentic primitive needs actual declaration and whole local typed relation. Name restricts the same binding/provider certificate. Parameter introduces its ordinary flexible source endpoint. Call consumes original callee, inert whole argument, receiver/receipt, entry, designated consumer and invocation return. |
| [Complete Call definition](../design/2026-10-07-complete-call-contribution-definition.md) §§1–3 | Actual complete operation is retained, with independent complete C0. Operator typing/witness actions, provider dispatch, contextual world binding and primitive admission remain independent. |
| [Literal Call checking](../design/2026-10-09-native-literal-call-checking-definition.md) Scope; §§1–3 | Selects literal 0 at native id's actual registered Int frame. Does not establish literal 1 at a subtraction provider's inlet. |
| [HIR operator association](../design/2026-09-18-hir-operator-association-first-slice-draft.md) Scope, Authority/current state, D3–D4 | Association uses the exact environment and retains applications; explicitly excludes name resolution, type/effect representation and solving. No builtin/prelude operator seeding is selected for this slice. |
| [Operator-chain reference](../../syntax-reference/en/src/expressions/operator-chain.md) §§1–2,4,7 | Exact environment admits spelling/fixity; later association supplies operand structure. Syntax does not supply operator values, typing or execution meaning. |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5, Authority/integration | Preserve native generation/accumulation/propagation and complete Call/effect hygiene; no proof-driven ordinary-source restriction. |

The original Call-introduction candidate is not used as adopted arithmetic
authority. The prior [owner audit](../progress/2026-10-13-odd-even-operator-owner-audit.md)
and [constructor boundary](2026-10-13-odd-even-source-subtraction-construction.md)
locate that proposal's resolution/semantic-generation seam. This packet instead
uses the adopted Source Generalize and complete-Call owners directly.

The exact source embedding is into §3's original resolved graph, binder tree,
declarations, captures, actual provider and initialization/current-world anchor.
Writing the child as `Γ_E;W_E` abbreviates those original dependent inputs; it
does not construct them. An arrow signature or candidate type coordinate does
not instantiate the original `rho;T |- S @ a_b : R ! C [d]` judgment.

## 3. Actual environment and literal routes

The first unavailable input is **which original ambient syntax and semantic
imports/declarations resolve this particular infix occurrence at `Γ_E`**.
The fragment does not list its ambient imports. That omission is missing packet
data, not evidence of a source error, an empty original environment or absent
language subtraction.

Current Y3's nearby import owner does not fill this input:

- `crates/yu-hir/src/module.rs:109–116` defines `SemanticImports(())`, describes
  imports as intentionally unavailable, and exposes only `empty()`.
- `lower_module_with_counters`, `:923–930`, accepts `_imports` without a payload
  usable for the original operator/provider registration. Its root planning and
  namespace construction at `:943–950` do not turn that opaque input into imports.
- `lower_leaf`, `:2112–2136`, retains an IntegerLiteral's spelling and occurrence.
  `local_source.rs:636–664` resolves Names through the actual lexical/module
  namespace and stores Integer spelling/scope. Neither is an original complete
  subtraction/literal semantic certificate.
- `candidate_source.rs:335–349` generates Int bounds and empty-effect bounds
  for formed Integer nodes. This is a real candidate literal constructor, but
  its stored facts alone do not establish their activation, replay or the
  original literal-1 provider/world/declaration interpretation. No candidate
  execution or source-law equivalence was inferred from those emissions.

Consequently, an actual original association/resolution instance is not supplied
by the current `SemanticImports` route. Previously inspected LocalSource/ordinary
Apply limitations remain local implementation boundaries; this note makes no
new rejection claim and does not repeat their analysis. No parser or solver was
run on the fragment.

## 4. Historical supplier evidence: available, not selected here

The read-only checkout root in this section is
`/home/momota1029/rust/yulang2-oracle-capture`. These bytes are implementation
evidence only, independently hashed below; they are not Y3 semantic adoption.

| Historical owner | Actual available construction |
| --- | --- |
| `lib/std/core/ops.yu:1–3,30` | Imports numeric roles; infix `-` body is `\x -> \y -> x.sub y`. This operator body has a method-resolution step. |
| `lib/std/num.yu:8–9,27–28,46–47,59–60` | Defines Sub and separate int, float and frac implementations. The int implementation calls `std::int::sub`. The existence of other providers prevents treating the catalogue as occurrence selection. |
| `lib/std/prelude.yu:1,6` | Reexports core operators and numeric roles. Availability through this module does not show that this source imported it. |
| `lib/std/int.yu:11` | `sub: int -> int -> int = builtin_op::int_sub`. |
| `crates/infer/src/builtin_ops.rs:140–145` | Structured `IntSub` registry entry has `Binary { param: "int", ret: "int" }`. |
| `crates/infer/src/lowering/builtin_op.rs:15–39,170–207,219–269` | Given an already resolved builtin, constructs its reference, signature bounds and curried function ports. Its own entry comment explicitly places symbol resolution before this owner. |
| `crates/infer/src/lowering/expr_syntax.rs:335–355`; `expr/chain.rs:551,584` | Historical number parser maps `1` to `Lit::Int(1)` and dispatches numeric syntax to `lower_number`. This is historical literal evidence, not the original Y3 literal's whole semantic judgment. The body of `lower_number` was not inspected. |
| `web/docs/reference/operators.md`, opening and Importing operators | Describes downstream import of operator syntax, including explicit core-ops imports. No ambient import instance for the exact fragment is supplied. |

The available chain is therefore a **potential** imported operator, method,
implementation and builtin chain, not an established chain for `n_E - 1`.
Even selecting the int registry entry would supply only an implementation
signature at that boundary. It would not independently establish the adopted
L1 whole operand telescope, effects, original guards, admission, provider/future
laws, joint dependent substitution and any complete Calls in that chain.

This distinction fixes the stop precisely:

| Kind of fact | State in this packet |
| --- | --- |
| Adopted general source rule | Available: Source Generalize literal/Name/Parameter/Call schemas and complete-operation retention. |
| Concrete original source environment/resolution data | Unavailable: the exact `Γ_E` import/association/declaration/provider instance. This is the first stop. |
| Selected specialized semantic law | Not established by the inspected governing chain: no original subtraction/literal-1 L1/L2 instance at `W_E` follows from the general selection or historical signatures. This is a later independent premise, not asserted globally nonexistent. |

No generic operator-Call reconstruction was attempted after this stop.
Both continuations remain open: the eventual resolved declaration may already
have an independently adopted semantic law whose concrete instance is missing,
or it may expose a genuinely unselected local law. The absent original
`Γ_E,W_E` import/declaration/provider instance prevents deciding between them.
This packet therefore does not claim that adopting a new law is necessary.

## 5. Minimized obstruction and retained consumers

The source owner handoff is the following original **input**, rather than a
new proof-only relation:

```text
the actual import/declaration environment and associated occurrence at Γ_E
  -> actual resolved operator reference/provider and operand incidence
  -> its independently established whole local semantic law at W_E,
     including actual n_E use, literal-1 introduction and dependent actions
```

The first arrow cannot be instantiated from the packet or inspected current
import payload. Subsequent arrows remain required and unproved. This is an
obstruction to the present construction, not a refutation of the original child
judgment or the accepted source.

When that input is supplied, the selected source constructor must consume it at
the original occurrence. If it uses Calls, each actual operation must retain
its callee computation, whole argument carrier, actual returned provider/current
world, entry/role, receiver/receipt, designated consumer, invocation return,
returned-provider/future interface, complete independent alternatives and
evidence, and distinct callee-pending/receiver-pending ordered suffixes. Receipt
is not replayed; independent abstract arms keep their own laws. Complete C0 is
still an independent typing premise. This is a retained obligation inventory,
not a conditional derivation that closes it.

The enclosing `odd(...)` consumes the authentic subtraction computation as its
whole delayed argument. It cannot consume a substituted Int descriptor, a
separately chosen effect, or projected provider evidence in its place. Delay's
original license and universal designated execution obligations remain intact.
The E/O qualification determines which authentic extrusion pairs qualify; it
does not manufacture this source judgment or those pairs.

## 6. Economy audit, falsifier and next action

The earlier elaboration and native intrusion routes left original arithmetic
formation untouched. The prior bounded owner packets localized it; this new
input scope inspected actual imported-role/provider and literal suppliers.
It found available historical alternatives and the concrete current import
boundary, but did not discharge the parent gate.

The genuine source typing/effect/complete-Call premise is A/B: accepted-output
safety and natural arithmetic inference. Missing packet data is not itself a
metatheorem. No inspected owner is shown to have constructed and discarded a
complete original subtraction certificate; class D is therefore unestablished.
Retaining actual import/declaration/provider evidence could remove later
reconstruction, but cannot create an unprovided semantic law. No new evidence
layer, annotation or restriction is selected.

Falsifier for this bounded obstruction: provide the actual original ambient
import/association/resolution certificate for this occurrence, followed by its
independent complete local law and literal-1 instance at the same `Γ_E,W_E`.
A registry entry, prelude reexport, scalar signature or selected integer
reference term alone does not falsify it.

One next action: the primary supplies the original source environment and
resolved declaration/provider instance from its owning import/resolution route;
then dispatches that concrete instance's remaining local semantic law, if
unprovided, through the existing authority/review path. Another quotient or
generic complete-Call proof at the unchanged premise is not the next action.

## 7. Checks, dependency snapshot and resource bounds

Checks: static `cat`/`sed`/`rg` reads; read-only HEAD/branch/status inspection;
SHA-256 and `git show` byte comparisons against the pinned baseline; leased-path
post-write inspection. All twenty direct Y3 dependencies in the snapshot matched
the baseline when checked. Some initial combined captures truncated; affected
governing rules/sections were reread narrowly. Discovery searches named several
nonexistent guessed paths; their errors support no absence conclusion. No
compiler test, build, runtime probe, search-model checker or Git mutation ran.

Resources: zero children, tests/builds/probes or measurements; only lightweight
read/hash processes, with bounded independent read batches. CPU/peak RAM and
exact reasoning wall time were not instrumented. Assigned ceiling: 30 minutes.
Primary remains the sole shared verification/integration owner.

Requested model/effort: normal registered prover, GPT-6.1 Sol/high per the
governing routing; the received assignment itself did not expose its launch
arguments. Observed effective model/effort: unknown, no runtime metadata exposed.
The callable schema includes prover; inspected role pins omit model/effort and
configuration defaults are Sol/high for agents. Configuration is not evidence
of this worker's effective settings. No Astra request/override or reload claimed.

Direct semantic/source dependency SHA-256 (baseline byte comparisons MATCH):

```text
c47cf65821b1364ded2a1a9e29d89304ed03d629f696c2929bc80e9af6e8d285 notes/theory/2026-10-13-odd-even-intrusion-preservation.md
bb34dd39856a0e12fee1e169c8bd2b6ad28f78e978d6bc4d6799d46b0809e7ac notes/theory/2026-10-13-odd-even-source-subtraction-construction.md
822c57a981d328995b7d2ba872cbf3d944dacfe6168d808929e23a9a991b5f7c notes/progress/2026-10-13-odd-even-operator-owner-audit.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
e65be7638ed616f5a88ce7d7bc5fffa06a07ee634df3649bd83cf0a60410d39b notes/design/2026-10-09-native-literal-call-checking-definition.md
ff113c3641f791788bea97e22b4f5dfcb91037be523e8198d3add8e6e89e17ed notes/design/2026-09-18-hir-operator-association-first-slice-draft.md
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5 crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842 syntax-reference/en/src/expressions/operator-chain.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

Routing/process dependency SHA-256 (also baseline MATCH):

```text
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1 .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98 .codex/agents/prover.toml
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1 rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69 rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6 rules/git-concurrency.md
```

Historical checkout SHA-256; no comparison to a Y3 baseline or adoption claimed:

```text
cb2c15eca2803a6b5a65e33541dd1213bd5f985c470a7767c17a4d59f77ca8c0 lib/std/core/ops.yu
631417ef1a85e38564fcc10d17b6eac6f64dfb735bf46d823ef1c7dd015f5e69 lib/std/num.yu
2d0d9b3bba4a4726dbb7f985e46524eea6b7e794759719a78d31984792b79822 lib/std/int.yu
a9d65efddb7d5bb3a8962a2cd64e9bd55a377ec6ff5b3bc29c25db8d1a67b3e0 lib/std/prelude.yu
c79a7dfb031bc58598ea6551472be568362f3b34c1b7a1b4c53721e0581c053d crates/infer/src/builtin_ops.rs
a3eb2bcdfc9216015d8b7759028dd2c77a2f0a2465128de5b198300498c6cb95 crates/infer/src/lowering/builtin_op.rs
3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085 crates/infer/src/lowering/expr_syntax.rs
e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6 crates/infer/src/lowering/expr/chain.rs
5785e906036cc19f45c17a7f87ac3096190ae75d538ee6be81fedc7c2c6c3945 web/docs/reference/operators.md
```

Task/lab/index records were locator/context reads only. The concurrently modified
`2026-10-13-check-closure-compatibility-proof.md` bytes were not read or consumed.
Omitted: original ambient import data, whole specialized primitive law, actual
source acceptance, method selection execution, complete C0, Branch/guards,
recursive-world closure, intrusion transport, soundness, required principality,
termination and F5/cutover. No theorem or aggregate gate is promoted.

## 8. Commit packet

- Exact leased/changed path: `notes/theory/2026-10-13-odd-even-subtraction-owner-instance.md`.
- Baseline SHA: `8f0c9cbb5ac207b18ad374d2e26610c02922604d`.
- Changed direct dependency hashes versus baseline: none in the twenty checked
  Y3 dependencies. Historical snapshot is foreign evidence, not a baseline delta.
- Claim/review status: bounded characterization and missing input; frozen,
  unreviewed research only. Original child and parent gates remain OPEN.
- Checks already run: static owner/authority reads, baseline/hash comparisons
  (29 hashes match, twenty Y3 files match the pinned baseline), read-only
  repository state and leased artifact inspection; no tests/builds.
- Proposed checkpoint message: `research: pin odd-even subtraction import and provider boundary`.
- Shared-record deltas left for primary/curator: link this note; distinguish the
  absent original environment instance from the available historical Sub/IntSub
  chain and independently required semantic law; retain complete Call, effect,
  preservation and principality obligations. `tasks/current.md`, theory status,
  design index and authority records are intentionally untouched by this leaf.
