# Raw block / legacy core / production term crosswalk

Date: 2026-10-06
Status: frozen bounded source characterization; unreviewed research checkpoint; no implementation authority
Baseline: `503ae9d21fc7b0e4a1062cd101804fb13183273c`
Legacy revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: `notes/progress/2026-10-06-source-registration-block-core-crosswalk.md`
Method: owning-source inspection and explicit node/identity transport crosswalk; no behavior execution

## Objective and governing premises

Trace `my apply f = { my step x = f x; step }` from raw braced canonical
Statement through retained legacy source lowering and current production
HIR/solver. The two reviewed encoding/block-value notes are dependencies;
this artifact adds the concrete raw-node/legacy-output/current-term seam.
It does not repeat their general search for an equivalent source encoding.

The pinned `tasks/current.md:1031–1047` selects this candidate and keeps
source acceptance, legacy evidence, current translation, and registration
separate. The call-view authority §§1.1, 2–3, 5 fixes annotation absence,
comparison-independent source formation, the protected provisional formal
view and its scoped ordinary-value resolution. Actual callable roles remain
fixed. No grammar or role decision is proposed here.

Exact syntax premises are binding-use §§Placement, Direct Rowan CST,
Boundaries, Non-goals (`15–18`, `23–32`, `90–94`, `122–127`, `190–195`),
braced-statement-block §§1–4 (`5–10`, `15–25`, `29–44`), architecture's
Authoritative canonical Statement binding/use addendum (`11090–11135`),
and Authoritative F5 §§19–21, 41 (`417–524`, `1420–1440`). Later F5 Pattern
ML application admission governs both headers; it is not the older generic
architecture's future Pattern placeholder. The architecture's brace meaning
boundary (`6415–6432`) leaves block/record interpretation to HIR/inference.
F5 §21 specifies one-formal production lowering; it does not supply arbitrary
nested local binding. Typed computation core §§2–3, 6 (`70–135`, `396–428`)
is Draft and derivation-indexed, not raw-CST authority.

## Raw candidate identity and CST derivation

Use byte ranges in this exact ASCII string, with half-open intervals:

| Occurrence | Range | Required identity |
|---|---|---|
| outer declaration `apply` | `3..8` | outer definition |
| outer formal `f` | `9..10` | `df` |
| brace expression | `13..38` | block B |
| local declaration `step` | `18..22` | local definition ds |
| inner formal `x` | `23..24` | `dx` |
| inner callee `f` | `27..28` | use uf referring to df |
| inner argument `x` | `29..30` | use ux referring to dx |
| application `f x` | `27..30` | call c, distinct from uf and ux |
| final `step` | `32..36` | use us referring to ds |

The production-composition CST skeleton below omits trivia and literal tokens
except the block separator. It is a static derivation, not a dump from a new
parser run for these bytes:

```text
Root
  BindingStatement
    BindingHeader
      Pattern
        IdentifierPattern(apply)
        PatternMlApplicationTail
          Pattern / IdentifierPattern(f)
    BindingBody
      OperatorChain
        BracedStatementBlockExpression
          Statement
            BindingStatement
              BindingHeader
                Pattern
                  IdentifierPattern(step)
                  PatternMlApplicationTail
                    Pattern / IdentifierPattern(x)
              BindingBody
                OperatorChain
                  IdentifierExpression(f)
                  MlArgument
                    OperatorChain / IdentifierExpression(x)
          BlockStatementSeparator(Semicolon)
          Statement
            OperatorChain / IdentifierExpression(step)
```

Current parser construction locators: binding `185–253` creates the header
and body; `259–313` combines owner stops with comma/semicolon/equals; Pattern
`1099–1125` admits the single formal application tail. Statement `562–604`
creates the brace primary; `917–962` dispatches canonical nested binding.
Expression operator-chain `782–819` creates `MlArgument`, parsing its one
argument with `MlMode::None` and resuming the enclosing chain with `All`.
Headers' Pattern application and body's expression application are different
node families, despite both spelling two space-separated names.

The exact parser baseline is the pinned parser file inventory below.
Layout baseline is also explicit: Statement `590` calls
`delimited_baseline(incoming, first-item-leading)`; lexical observation
`92–99` changes that baseline only for a deeper newline. This candidate is
all on one line, so it retains incoming layout baseline. Pattern continuation
requires same-line/deeper Gml (`pattern/mod.rs:1102`, F5 §20 `445–449`);
expression continuation checks no newline or deeper indentation
(`operator_chain.rs:758–771`). The semicolon belongs to the brace owner,
and the right brace stops the binding body. No new delimiter or continuation
choice is needed. This derivation does not assert typed source acceptance.

## Explicit legacy node and output correspondence

The legacy CST vocabulary is different. Its `Binding` / `BindingHeader` /
`Pattern` / `ApplyML` formal arguments correspond structurally to current
`BindingStatement` / `BindingHeader` / `Pattern` /
`PatternMlApplicationTail`; `BraceGroup` corresponds here to the current
brace sequence, and `Expr(Ident f, ApplyML(Expr(Ident x)))` to the inner
OperatorChain and MlArgument. This is a correspondence of production shapes,
not an identity of Rowan trees or proof that their parsers accept exactly the
same complete input language.

The legacy extraction `expr_syntax.rs:379–410,421–436` selects the binding
body and collects Pattern arguments. The outer owning helper is
`expr/mod.rs:276–341` (binding body with arguments / named self), feeding the
Defined lambda route. The nested binding uses
`block_local.rs:866–896`, likewise `LambdaScope::Defined`. Crucially,
`lambda.rs:256–268` dispatches Defined parameters to
`lower_defined_lambda_params`; the generic recursive branch at `271–368`
is not the selected branch for these declarations. The Defined route
`644–743` installs formal locals and frames before body lowering,
`779–784` lowers the body while those locals exist, `852–865` wraps
parameters in reverse order and restores locals, and `946–975` emits
`Expr::Lambda(param.pat, body.expr)` as a Value computation with Function
constraints. It is therefore a concrete lambda-generation route rather than
just a nearby generic-lambda existence witness.

| Current raw role | Exact legacy source seam | Legacy output / identity |
|---|---|---|
| brace B with local binding and final name | `chain.rs:593–596`; `expr_syntax.rs:115–140,171–179`; `block_local.rs:69–86,122–140` | Binding child prevents record classification; block items are lowered in order; final Expr is returned directly. |
| ds (`step`) | `block_local.rs:554–585,1225–1263` | Fresh DefId, local `Pat::Var(ds)`, stored body and generalized local scheme before tail lowering. |
| dx and inner function | `block_local.rs:866–896`; `lambda.rs:644–743,852–865,946–975` | Formal local installed before `f x`; emitted `Lambda(pat_dx, body_c)`. Enclosing df is not removed when inner formal scope is restored. |
| uf, ux, us | `chain.rs:544–546`; `name_ref.rs:73–75,146–174,215–220` | Reverse lexical local lookup; fresh reference resolves to local DefId; `RefUse` carries source span, parent, value; output `Expr::Var(ref)`. Local value may be instantiated, so reference identity is not equality of every use's TypeVar. |
| c (`f x`) | `tail.rs:14–16,89–124,626–627,630–686` | ApplyML argument is lowered, then `make_source_app` supplies call/callee/argument source ranges to the application path; emitted `Expr::App(callee.expr,arg.expr)`. |
| B's returned function reference | `block_local.rs:1284–1306` | `Block([Let(My,pat_ds,lambda_dx)], Some(Var(ref_ds)))`; tail.value flows to a fresh block value, and head/tail effects flow to its effect. |

The schematic legacy arena output is consequently:

```text
Lambda(pat_df,
  Block([Let(My, pat_ds,
    Lambda(pat_dx, App(Var(ref_df), Var(ref_dx)))))],
    Some(Var(ref_ds))))
```

This shape retains the local binding and its named use; it is not already
`Lambda(df,Lambda(dx,App(...)))`. The emitted references continue to identify
definitions after the lowering-local vector is truncated. That is static arena
transport, not an operational captured-environment lifetime theorem. Legacy
inference/scheme/effect constraints remain part of the old implementation's
assumptions; copying these constructors does not establish new call-view
formation. No legacy parser or lowerer was executed for the exact candidate.

## Current production transport and omission ownership

| Stage | Positive correspondence | Exact omission / owner |
|---|---|---|
| syntax grammar and lossless CST | Distinct formal, name and call ranges can be named from the composed structure. | No demonstrated grammar omission for this candidate. Exact-byte parse was not run. |
| operator association (`yu-hir/lib.rs`) | `136–144` retains associated structure; `298–303,458–501` retain MlArgument continuation with callee/argument children in `HirExpr::Value`. `HirExpr::Apply` at `63–68` represents dynamic operators. | This structural Value is not resolved ordinary-call HIR or typed Function application. A dynamic operator Apply variant does not fill that gap. |
| outer resolved module binding | `module.rs:1155–1205,1471–1516` admits one plain formal; creates df as `HirParameterId(DefinitionRootId(apply),0)`, pushes it, lowers body, restores scope, wraps Lambda. | `direct_atom` (`lib.rs:176–185`) excludes a brace child; `module.rs:1419–1423` rejects no-atom/composite chains; `1374–1385` creates Error. Conditional on the shown recovery-free CST, output is outer Lambda(df, Error(B)), retaining its root and df. |
| local binding / capture | Parameter lookup stack exists (`module.rs:876–903,1443–1455`). | Module planning visits only root children (`804–806`); no nested local declaration owner or Block/Bind/Apply resolved variant exists (`426–449`). ds, dx, uf, ux, us, c are not visited/resolved in the rejected body. This is HIR lowering/representation, before typed elaboration. |
| solver collection | Existing Lambda recipe can retain outer occurrence/root/formal (`lib.rs:1038–1051`). | Body Lambda or Error yields CollectedBodyStatus::Error (`939–964`); the actual candidate's Error body is incomplete. Even hypothetically erasing the local bind to nested Lambdas would still hit the nested-Lambda collector restriction. Collector repair alone cannot create the absent HIR. |
| typed core and registration | Draft core has lambda/name/call/bind constructors (`§2`) and derivation-indexed translation (`§3`); §6 `403–410` binds the RHS result value. | No inspected current production seam constructs that typed derivation from this raw brace/local/call. Missing typed ports/receipt, retained capture evidence, and correlated original nu,K,D are typed-elaboration/source-registration obligations, separately from HIR and collector support. |

Thus the first production stop for the candidate is composite-body HIR
lowering. A later collector restriction is independently visible. Source
registration remains open even if both implementation restrictions are lifted.
These limits characterize implementation, not newly chosen rejection semantics.

## Conditional core bridge and discriminating boundary

Explicit candidate assumptions are **P** (the exact bytes realize the shown
recovery-free CST), **L** (translate these two canonical statements to one
lexical local-function bind, with uf→df, ux→dx, us→ds), and **T** (supply the
selected roles, result interfaces, typed incidences, and preserved lexical
references/evidence required by the Draft derivation). Under P/L/T the
candidate derivation is:

```text
lambda(df,
  bind(ds, result(lambda(dx, call(n_uf,n_ux))), result(name ds)))
```

The definition/lambda entry/body interfaces and normalizations are implicit
in this proof notation, not inferred from CST tags. The Draft core's
Return/bind law then removes the administrative local bind only if lookup
returns the retained same closure under the allowed observation relation.
That is the prior note's separate closure-preservation premise; no new proof
of it is claimed. This crosswalk instead derives why local definition/use
identity and two distinct scopes must survive before that law can apply.

A distinguishing static seam is the same one-formal header with composite
body: adding the brace creates no new outer formal, yet prevents any inner
resolved occurrence construction. Simply extracting all descendant identifiers
would fail to distinguish the definition ds from use us, df from uf, or dx
from ux. Flattening the bind or allocating independent f identities would
assume away the transport premise. This is a derivation of necessary source
correspondences, not a minimized accepted-program counterexample.

## Independence, coverage, resources, and freeze

Established within the pinned source inspection: the named parser construction
and HIR/collector branches exist with the specified payload and refusal
conditions. Bounded characterization: the grammar composition and static legacy
output schema. Conditional derivation: P/L/T and closure observation law are
required for raw-source-to-core/equivalence conclusions. No established theorem,
current typed acceptance, registration certificate, or independent review of
this artifact is claimed.

Legacy source and existing notes share the legacy implementation lineage;
current parser/association/HIR/solver share production assumptions. They are
cross-layer corroboration, not independent operational oracles. Source spans
and static DefIds prove neither runtime reference lifetime nor the inferred
protected Function relation. No oracle, tests, builds, probes, mutations,
seeds/ranges, enumeration, or performance measurements ran. No network ran.
Omitted: exact-byte parsing, runtime closure construction/capture lifetime,
legacy parser compatibility, solver solving, recursive local groups, records,
empty blocks, mutation, State, handlers, and broader source adequacy.

Exactly 12 sequential lightweight exec_command invocations were used, including
pwd, rules/notes reads, rg, pinned Git reads, hashes, and final lease write.
Read-only Git commands retrieve immutable dependencies; no Git mutation ran.
One short Python process at a time; sequential Git subprocesses; no heavy
process or children. Reported command wall times were at most 0.2 s; aggregate
session wall time, CPU and peak RSS were not instrumented and remain unknown.
Some broad captures were truncated; later targeted reads recovered decisive
locators, but the search is not exhaustive. Output is this lease only.

Final dependency bytes matched the pinned current revision. Failure conditions:
changed direct dependencies, a contrary exact parser result, a selected current
raw-block rule or a legacy dispatch/typing condition invalidating the schema.
Stop condition reached: the raw identity-to-lexical-typed derivation seam is
specified as missing; another checker assuming L/T would leave it untouched.
Writes stop with this frozen artifact before independent review.

Recommended next action: the primary should fix the narrow realization contract
for this CST sequence with two formal owners, one local definition/use and one
ordinary call, using the existing compatibility evidence; then require separate
HIR, typed-registration and collector conformance gates against that contract.
No grammar redesign or toy semantic probe is needed to expose the current seam.

## Frozen direct dependencies

Navigation tasks/index were read at the pinned revision, not consumed as live
semantic authority. Current dependency bytes were rechecked against baseline;
legacy bytes were read only at their named frozen revision. No hash changed.

| Revision | Path | SHA-256 |
|---|---|---|
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` | `bef24bf81b5d561538974db75c950a2df9cc2ed0b49248f2440fb0781941e436` |
| `503ae9d2` | `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `503ae9d2` | `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `503ae9d2` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `503ae9d2` | `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `503ae9d2` | `syntax-reference/en/src/expressions/braced-statement-block.md` | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| `503ae9d2` | `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `503ae9d2` | `crates/yu-syntax/src/statement.rs` | `dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d` |
| `503ae9d2` | `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `503ae9d2` | `crates/yu-syntax/src/expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` |
| `503ae9d2` | `crates/yu-syntax/src/pattern/mod.rs` | `f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03` |
| `503ae9d2` | `crates/yu-syntax/src/lexical/observation.rs` | `730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641` |
| `503ae9d2` | `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `503ae9d2` | `crates/yu-hir/src/lib.rs` | `56aafd7d958acdfa3362ffcc7bf3e815d795f455597cf4f8e471194addb04c1b` |
| `503ae9d2` | `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `a58eefc3` | `crates/infer/src/lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `a58eefc3` | `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `a58eefc3` | `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `a58eefc3` | `crates/infer/src/lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| `a58eefc3` | `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `a58eefc3` | `crates/infer/src/lowering/expr_syntax.rs` | `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` |
| `a58eefc3` | `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-source-registration-block-core-crosswalk.md` only.
- Baseline SHA: `503ae9d21fc7b0e4a1062cd101804fb13183273c`.
- Legacy dependency revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; inventory above.
- Review status: frozen unreviewed bounded characterization and conditional bridge; no independent review or gate closure claimed.
- Checks already run: pinned-source locator inspection, SHA-256 inventory, current dependency byte equality, exclusive lease absence guard, note readback. No behavior verification.
- Proposed one-line research-checkpoint commit message: `research: map nested block CST through legacy lowering and production gaps`.
- Shared-record deltas intentionally left for primary/curator: distinguish first composite-body HIR stop, absent local/call resolved identities, independent nested-Lambda collector stop, and typed-registration obligation; add exact raw/legacy crosswalk and Defined-lambda branch correction. No task/index/theory/authority/question-board files changed.
