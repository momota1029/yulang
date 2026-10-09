# Written Any annotation: resolution owner audit

Date: 2026-10-10
Status: frozen, unreviewed research checkpoint; no implementation authority
Baseline: `6739dccf895660af6a1b4f2275af2bd21105279b`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Method: selected-rule owner inversion and frozen legacy resolver branch tracing
Scope: actual written Type in `my widened = 0 as Any`
Claim class: bounded source/artifact characterization; conditional code derivation

## 1. Result and authority

No audited selected current rule supplies an unconditional resolution of this
written `Any` occurrence into a completed ordinary Value(Any) descriptor/root.
The earliest missing selected operation is **scoped written-Type resolution**:
identify what declaration/intrinsic/import this actual Type names, and retain
its completed contract and source incidence. Ordinary-root construction and
its full Any interpretation remain subsequent obligations.

There is a genuine frozen legacy annotation resolver. Its builtin table does
**not** recognize `Any`. An unqualified `Any` can resolve through supplied
type aliases, declarations or imports; their presence and interpretation are
additional premises. Without such a binding it yields `UnresolvedTypeName`.
Wildcard `_` produces an internal Top upper bound through another branch.
Neither route supplies the selected current ordinary Value root contract.

This does not establish that a new language decision is globally unavoidable,
or that the approved program must be rejected. It identifies what has not been
selected. Choosing a scope-independent `Any` intrinsic, its precedence over
type declarations/imports, or an implicit import would settle observable name
resolution not specified by the inspected current rules. Those choices need
the primary's authority resolution and, if new, the separate narrow decision
required by the one-case design. Retaining incidence for an independently
selected existing contract can instead be constructor work under that contract.
The selected Any membership meaning itself is not reopened here.

The integrated `source-annotation-typed-root-bridge/q1/d1` bundle, receipt's
integration commit `b7e5569db9cad28ce1410faf29cc1fffbf1db046`, approves detailed
source-owned design with conditional Direct consumption. It does not approve
a type-name policy, API, implementation, production route or cutover. Current
bundle files were compared with the pinned baseline and had no differences.
The one-case design §§2–4 and predecessor construction attempt §§1–5 govern
the complete root/premise boundary. This audit changes none of their meanings.

## 2. Exact owners and distinct outputs

| Stage / locator | Actual output | Remaining premise |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs:18`, `type_annotation_tail_normalized`; `crates/yu-syntax/src/type_expr/mod.rs:857`, `type_expr_from_primary_started_normalized` | `as` owns one full TypeExpression; ordinary Identifier primary is emitted and tails scanned | A syntax node is not a resolved semantic type. These functions receive syntax/layout context, not a typed namespace. No exact-program parse was run. |
| Authoritative `docs/yulang3-architecture.md` §4.2 / §4.2.2, especially lines 225–280; §5 | Resolve/Lower consumes semantic imported interfaces; compiler/module-resolution owns module graph; HIR owns resolved names | Header/operator syntax dependencies do not supply semantic type imports or descriptor contracts. The document allocates responsibility, not an Any resolution rule. |
| Authoritative `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md`, Scope, Product and phase boundary, Admission/resolution/identity | Two-pass ordinary module-local **Value namespace** resolution | Types and import/module graphs are outside this gate. Value namespace precedence/duplicate rules cannot be transplanted to type names. |
| `crates/yu-hir/src/module.rs:104` (`SemanticImports`), `:414` (`NameResolution`), `:1994` (IdentifierExpression resolution) | Empty import input and value/parameter reference resolution | No actual written-Type/builtin import contract is supplied by these owners. This narrow positive-owner inspection does not repeat the predecessor's annotation-variant inventory. |
| Authoritative source Generalize selection §2; SRC construction §§3.1, 3.2(6), 3.3 | Name uses an already resolved binding; annotation checks a written target; Intrinsic distinguishes written constants from inference introductions | These premises retain resolution/contract evidence; they do not define a type-name lookup or introduce a complete Any target from spelling. |
| CE construction §3, Top/Any registry entry; PE construction §§6.1–6.2 | Hereditary membership law and Direct over supplied actual ordinary records | Complete registered interpretation, typed operands and scope maps must already exist. PE `v_Any := the actual ordinary Any target root at q` is an input assignment. |

The desired dataflow therefore still has a missing first semantic arrow:

```text
q_type = written Any, original sigma_q
  -- selected type-name resolution --> resolved target identity/contract
  -- ordinary-root formation       --> v_Any with full Value interpretation
  -- independent Top law          --> same-value/provider membership evidence
  -- Direct                       --> boundary certificate / target export
```

The architecture names ownership; it does not require a particular crate/API
for the unresolved descriptor supplier. No `spec/` directory or
`crates/yu-compiler/src` exists in this baseline; attempted locator reads failed
with missing-path errors. These are directory facts, not semantic arguments.

## 3. Frozen legacy correspondence and smallest derivation

The primary separately authorized reading the charter §2's frozen legacy
reference `a58eefc31e22141574b6f20c6a5748151c6d79f1`, initially the annotation
builder/annotation/builtin-op files, then direct Any call sites. This is
operational correspondence only; no legacy policy is adopted.

Exact chain at that revision:

1. `crates/infer/src/lowering/expr/tail.rs:51–88`,
   `lower_type_annotation_tail`, takes the actual child TypeExpr and builds
   with the actual modules/module/site and aliases. It then connects annotation
   constraints and returns `acc`. This is not the selected current target-root
   export constructor.
2. `crates/infer/src/annotation/builder.rs:116`, `build_type_expr`, requires
   TypeExpr; `:180–193`, `build_type_base`, sends Ident `_` to Wildcard and
   other Ident paths to `resolve_ann_path`.
3. `builder.rs:345–383`, `resolve_ann_path`, checks (for a single name) self,
   builtin, bare-variable aliases/variables, type aliases, type-name aliases,
   then `lexical_type_at`. A found type yields `AnnType::Named(decl.id)`;
   private/missing paths yield their specified errors. Multi-segment paths use
   `type_path_at` separately.
4. `crates/poly/src/types.rs:64–86`, `BuiltinType/from_surface_name`, exhaustively
   recognizes `int`, `float`, `bool`, `file_handle`, `unit`, `never`; there is no
   Any variant or `Any` spelling arm.
5. `crates/infer/src/module_table/mod.rs:1016–1041`, `lexical_type_at`, searches
   current declarations, current imports, then parents at their stored order;
   it returns Missing if the parent chain ends. `:873–895`, `type_path_at`,
   handles qualified module/import paths. Lookup implementation, export
   installation and an actual annotated module instance are not proved here.
6. `crates/infer/src/annotation.rs:35–42` explicitly represents a resolved
   annotation value distinct from constraint nodes. `annotation/constraints.rs`
   `:298–327` lowers Named to Pos/Neg constructor paths and Wildcard to
   `Pos::Bot/Neg::Top`; builtin lowering `:771–799` supplies ordinary primitive
   constructor paths or Never bottom. No branch examined produces the current
   complete ordinary Value(Any) root package.
7. `crates/infer/src/builtin_ops.rs:44–57` defines operation signatures and
   `builtin_op` resolution. It is an operation namespace, not the written-Type
   resolver or an Any descriptor introduction.

**Conditional code derivation.** Let H1 be a valid legacy TypeExpr whose head
is the single Ident `Any`, without application/tail; H2 a builder with no alias
or bare type variable named Any; H3
`modules.lexical_type_at(module,Name("Any"),site)=Missing`. These are candidate
instance assumptions, not a constructed or accepted full source module.

```text
H1 -> build_type_base -> resolve_ann_path([Any])
from_surface_name("Any") = None             [finite exhaustive match]
H2 -> all alias/variable branches fail
H3 -> lexical lookup has no Found/Private arm
    -> Err(UnresolvedTypeName { path: [Any] })
```

This one-token witness discriminates the candidate shortcut “Any is always
recognized by the frozen builtin resolver.” It is a source-code branch
derivation, not an executed counterexample to Yulang acceptance and not a
current semantic theorem. If H3 is changed to Found(d), the exact same code
returns `Named(d.id)`; its ordinary Any meaning remains an independent premise.
If H2 admits an alias, the earlier alias branch applies. Replacing `Any` with
`_` selects Wildcard and bypasses this path, so treating printed Top/Any or
wildcard bounds as resolution of the actual written token fails this witness.

A read-only exact `git grep -n '\bAny\b' a58eefc3 -- '*.yu'` returned two debug
comments under solved bug notes, and no non-comment source occurrence. This is
coverage of tracked `.yu` files at that commit, not all generated/module-table
declarations, external libraries or possible user programs. It does not prove
that an imported Any declaration cannot exist.

## 4. Independence, failure conditions and next action

There is no executable checker, oracle run, seed/range, enumeration or mutation
run. The legacy finite builtin-match trace is independent of the conditional
native Top/root assumptions: it examines a concrete earlier source resolver.
Both native construction notes share their supplied complete Any contract and
independent local law; this audit does not prove those membership rules.
The named spelling substitution and lookup-branch changes above are analytic
discriminants, not executed mutations.

Failure conditions for an unconditional bridge include an unselected type
namespace/prelude policy; unresolved, private, different or aliased Any;
missing actual descriptor interpretation or source incidence; incomplete
guard/evidence/scope record; or a Top/Direct term whose operands differ from
the constructed records. Exact source parse acceptance, full import lookup,
primitive registration, Any membership signature, compiler implementation,
arbitrary annotations and final acceptance remain unverified. The legacy
annotation route cannot be copied merely because it has a real resolver: it
returns constraints over `acc` and provides no correspondence to the newly
selected current final ordinary target.

Recommended next action: the primary should resolve the narrow written-name
introduction premise for this occurrence (cite an already selected Any
declaration/intrinsic/import, or obtain the missing scoped type-name decision),
then assign its complete descriptor/root constructor. This is the precise
premise that another conditional Top model would leave untouched.

Checks were read-only `rg`, `sed`, `cat`, `git show/grep/ls-tree`, baseline diffs,
identity/status reads and hashing. No tests, builds, probes, scratch files,
Git mutations or children were used. Commands were lightweight, occasionally
batched with up to five concurrent read-only shell processes; no heavyweight
process started. CPU time/peak RAM and total wall time were not instrumented;
the packet supplied no numeric compute cap and prohibited tests/builds/probes.
Large initial task/index locator capture was truncated and is not claimed as
complete inspection; governing dependencies were subsequently read narrowly.

## 5. Frozen dependencies and commit packet

Current direct dependencies were unchanged against the pinned baseline when
checked. Hashes below are SHA-256; legacy dependencies use Git blob hashes at
the fixed full legacy commit above, avoiding live-tree dependence.

| Current dependency | SHA-256 |
| --- | --- |
| `questions/2026-10-10-source-annotation-typed-root-bridge/question.md` | `7ff42d0a11f9b1535e9423d41c52ed51266b1712f4317e801949a9dda02f3cd6` |
| same bundle `answer-draft.md` | `b414ef4f99423158161a848090e21aa8a04dc1604f8b9719dbad78f73f092cfa` |
| same bundle `approved-answer.md` | `766c3575dcded7dc2ed95de24e7c4dc97a1211494b683f2d0aac954f323c4222` |
| same bundle `receipt.md` | `aa9cb81d91d265d9cb6e862f78fc2edab62e59b2d7802562cc863932bb315528` |
| `notes/theory/2026-10-10-source-owned-annotation-any-design.md` | `bfff9fdfa6e5aa9258949992d0711fa674b91fdde501e0a658e02b3712999a3e` |
| `notes/theory/2026-10-10-source-annotation-any-root-construction-attempt.md` | `f336a0d8081607debe27ffd0c9d46716b39e55ce8ec14fb05c25ab28bf77e9b5` |
| `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` | `494a6973ced88a031688213990ea380e64cb74fea3bb1396236a8d1bb911f11a` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `docs/yulang3-architecture.md` | `76b59a473c84a0654a40b7598c9a2d4ce54eeb512c6aa3f5213e95aa8fab44a5` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/theory/2026-10-08-native-projection-certificate-constructors.md` | `04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs` | `edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |

| Legacy dependency at `a58eefc31e22141574b6f20c6a5748151c6d79f1` | Git blob |
| --- | --- |
| `crates/infer/src/annotation.rs` | `9bbe1aabe74c4e17030c3fb622ab4f7a90b01a66` |
| `crates/infer/src/annotation/builder.rs` | `c49d83984bb470c349e92064377ed45a7a21dc40` |
| `crates/infer/src/annotation/constraints.rs` | `d2cf0e18266233c1e3c2943448244ee2a3499529` |
| `crates/infer/src/builtin_ops.rs` | `2fcddfe8015df988e7c05ce23651c63467719d96` |
| `crates/poly/src/types.rs` | `472e3ae280cf5aaeb81fa49f9104fcde83214d0a` |
| `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `crates/infer/src/module_table/mod.rs` | `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558` |

- Exact leased path: `notes/progress/2026-10-10-source-annotation-any-resolution-owner-audit.md`.
- Baseline SHA: `6739dccf895660af6a1b4f2275af2bd21105279b`.
- Changed dependency hashes: none at producer validation; recheck before integration.
- Review status: frozen unreviewed bounded characterization/conditional derivation;
  no source theorem closure, semantic selection or implementation authority.
- Checks already run: narrow governing-source/owner reads, frozen legacy branch
  tracing, exact tracked `.yu` spelling search, baseline dependency diff and hashes;
  no executable verification.
- Proposed commit: `research: trace written Any annotation resolution ownership`.
- Shared-record deltas intentionally left for primary/curator: link this audit in
  the annotation lane; record the missing scoped Any introduction and subsequent
  complete root supplier separately. No DAG status/prerequisite, authoritative
  index, task, question or production change is proposed by this checkpoint.

Writing stops at handoff. Independent review is pending.
