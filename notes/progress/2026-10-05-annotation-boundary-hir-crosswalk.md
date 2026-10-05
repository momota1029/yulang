# Approved annotation boundaries: pinned source/HIR crosswalk

Date: 2026-10-05
Status: frozen, independently reviewed research characterization and source-inspection derivation
Implementation authority: none
Method: source/HIR correspondence audit; no new transition model, compiler edit, or test
Lease: this file only

## Objective, baseline, and governing premises

Determine whether the three approved annotation forms supply a direct-target
comparison followed by target export and preservation of local realization
evidence through the existing syntax, associated HIR, resolved HIR, collector,
types, and core boundaries.

- Primary baseline: `f50c8a88882a10f109a71e2842f4d1b02982de53`.
- Inspected source/design snapshot: `0ab7620e167f190691a9ec50fde507d039265aa4`.
- Selected decision bundle: `28dddc75fd598faf34dd4d069ffb231cb64a82f1`,
  `questions/2026-10-05-source-annotation-boundaries/` question `q1`, draft
  `source-annotation-boundaries-answer/d1`, approved answer's numbered
  decisions 1–5 and explicit approval provenance. At inspection, the three
  current bundle files were byte-identical to that commit.
- Exact governing scope: concrete-compatibility boundary §1's one inequality
  and concrete-success non-composition; structural-tails design sections
  `as Type` and `Type exit and continuation` for syntax; redesign charter
  §§1–4 for research scope and §21 for parameter entry; typed-computation-core
  §6's `Source parameter-role generation before body synthesis` for the
  conditional core construction. The core design is Draft, and the charter
  is Reviewed with selected user amendments; neither grants implementation
  authority.

The approved contract names binding annotations, argument annotations, and
expression `as Type`. Each boundary compares its current endpoint directly
with its target. Success exports the target and local evidence; a later
boundary consumes that exported endpoint and preserves the preceding evidence
while adding its own. No source-free intermediate concrete adaptation is
allowed. The existing Value-entry/retained-Computation roles remain binding
for argument annotations. `x as int as str` is not reinterpreted as two
expression boundaries. These are selected premises, not results proved by
this audit. The approval excludes complete adequacy, solver changes, compiler
implementation, and expectation changes.

Source reads used `git show`/`git grep` on the pinned revision. Working-tree
replacement documents were not used as semantic authority. The relevant
production sources listed below have no committed delta from `0ab7620` to
the supplied primary baseline; uncommitted compiler changes were not consumed.
For exact repository paths, package-relative locators such as
`yu-hir/src/module.rs` are rooted at `crates/` (`crates/yu-hir/src/module.rs`);
the same mapping applies to `yu-syntax`, `yu-solver`, `yu-types`, and `yu-core`.

## Crosswalk and first loss

All line locators below refer to `0ab7620`, not to the live working tree.

| Approved form | Syntax owner and retained input | Associated/resolved HIR | Collector, types, and core | First unavailable information |
|---|---|---|---|---|
| Binding annotation, e.g. `my x: T = 1` | `BindingStatement → BindingHeader → Pattern`, with `IdentifierPattern(x)` and `PatternTypeAnnotation → TypeExpression(T)`. Pattern colon branch `yu-syntax/src/pattern/mod.rs:1077–1097`; type RHS `1294–1337` protects declaration `=`. Binding owner delegates the full pattern. | `plain_binding_header` in `yu-hir/src/module.rs:1471–1517` admits only a plain identifier, optionally one plain identifier argument. An extra annotation child falls through to `None`. `plan_root:1060–1066` chooses `UnsupportedTarget`, and `lower_root:1139–1148` emits `HirItem::Error`. No `HirBinding` with a target is emitted. | Collector `yu-solver/src/lib.rs:1001` skips `HirItem::Error`. No target query or realization reaches it. `HirBinding:545–554` has no annotation field. No core annotation implementation exists in `yu-core`. | Root planning/header admission, before binding/parameter/endpoint creation. CST retains the target, but resolved HIR retains only error ownership and ranges. |
| Argument annotation inside an argument pattern, e.g. grouped `my f (x: T) = x` | ML argument owner is `PatternMlApplicationTail → Pattern → ParenthesizedPattern → Pattern`, whose inner pattern can contain `IdentifierPattern(x)` plus `PatternTypeAnnotation`. Parenthesized items restart at `PatternPrecedence::Lowest` (`pattern/delimited.rs:312–326`), permitting colon. Explicit outer computation annotations retain their Type CST here as well. | Header admission requires its single argument's child to be an `IdentifierPattern` (`module.rs:1498–1512,1519–1533`); a parenthesized or annotated pattern fails. `HirParameter:361–365` contains only identity/name/range, and `ResolvedExpr::Lambda:427–431` only parameter identity/body/range. Neither stores the target or Value/Computation role. | Same `HirItem::Error` skip, so no annotated argument recipe or role-directed target comparison. Current plain-parameter lambda recipes at `yu-solver/src/lib.rs:1041–1051,1557–1610` do not constitute the approved annotated entry/realization construction. | Header admission. Before rejection, the argument's inner CST distinguishes its annotation. The ordinary resolved parameter representation would also be insufficient if admission alone were relaxed. |
| Expression `e as Type`, e.g. `x as A` | `OperatorChain` contains the expression and `TypeAnnotationTail`, with `AsKw` and a complete `TypeExpression`. Tail owner `yu-syntax/src/expression/tails/type_annotation.rs:17–49` forwards the Type exit unchanged. | Association recognizes the outer boundary (`yu-hir/src/lib.rs:305–313`) and emits `HirExpr::Value { kind: TypeAnnotationTail, children: [associated e, ...recovery/nested-expression children], range }`. `collect_nested_items:505–528` ignores valid Type tokens and normal Type nodes, so the annotation target itself is absent. `direct_atom:176–185` rejects the multi-child chain; `lower_simple_chain` returns `Unsupported` at `module.rs:1419–1423`, producing `ResolvedExpr::Error` at `1260–1269` for direct roots, or `1374–1385` for bodies. | A direct error expression produces no integer/name/lambda facts in the inspected collector dispatch; a binding error body is classified Error (`lib.rs:913–964`). `ResolvedExpr:426–449` has no annotation/adapter case, and `yu-core/src/lib.rs` contains only its module doc comment. | Normal Type detail disappears during associated-HIR construction, earlier than semantic HIR's explicit `UnsupportedExpression` rejection. CST plus ranges can still recover the target; the standalone associated object cannot. |

`yu-types/src/lib.rs` is the closed type arena/polarized scheme implementation.
Its inspected source has no `ResolvedExpr`, `SyntaxKind`, or annotation-to-type
elaboration entrypoint. Its manifest depends on `yu-hir`, but that dependency
does not establish a source annotation translator. No later production layer
inspected here reconstructs the annotation target lost in the preceding seams.

## Discriminating source-inspection derivation

The smallest witness here uses two one-character annotation identifiers:

```text
x as A
x as B
```

Hypotheses: use the pinned ordinary expression entry at outer precedence,
with annotations enabled, identical operator environments, no recovery, and
the valid one-token Type targets `A` and `B`. `A` and `B` are distinct symbolic
targets; the argument concerns preserving their spelling, not proving that
they resolve to distinct denotations in a particular type environment.

1. The Type primary branch (`yu-syntax/src/type_expr/mod.rs:874–891`) emits
   an identifier token within `TypeExpression`; the annotation tail owns it.
   Each source has extent `0..6` and an expression identifier at `0..1`.
2. `collect_nested_items` collects nested `OperatorChain`, `Invalid`,
   `Missing`, `Error`, and Error tokens. For the valid `TypeExpression(A)` or
   `TypeExpression(B)`, it recurses and ignores the identifier token. Thus
   `value(TypeAnnotationTail)` contains no target child in either case.
3. `structural_continuation:458–482` prepends the identical associated `x`.
   Both resulting public associated trees are therefore exactly:

   ```text
   Value(TypeAnnotationTail, 0..6,
     [Value(IdentifierExpression, 0..1, [])])
   ```

4. Any deterministic translator receiving only that associated tree and a
   fixed external environment must return the same result for both inputs.
   It cannot retain both original target spellings. An additional dependency
   on the original CST/source is necessary, or the association representation
   must retain the target. This is an information-loss result for this
   standalone representation; CST-aware reconstruction is not ruled out.

This derivation uses the actual parser/association clauses, not a supplied
annotation transition model. It is a conditional source-inspection theorem
for the named recovery-free identifier subcase, unreviewed and not executed.
The witness is minimized within that subcase to a one-character expression
and one-character target; no claim of global shortest syntax is made.

## Parameter-location and repeated-boundary traps

`my g x: T = x` must not be used as evidence that an annotation belongs to
the parameter `x`. Pattern precedence is ordered
`Lowest < TypeAnnotation < Alternation < Alias < MlApplication`
(`pattern/mod.rs:164–171`). The unparenthesized ML argument is parsed at
`MlApplication` (`1111–1114`), where colon is not admitted; the pending colon
returns to the enclosing pattern. The pinned test
`crates/yu-syntax/src/tests/pattern.rs:3059–3065` asserts the direct children for
`f x: T` are `IdentifierPattern`, `PatternMlApplicationTail`, and
`PatternTypeAnnotation`. The annotation is on the outer pattern. The HIR test
`crates/yu-hir/tests/simple_module_resolution.rs:607–627` proves only current rejection of this
header, not argument-annotation location or semantics. A delimited argument
with an inner annotation is the source-derived location described above;
no runtime test of the grouped full declaration was run in this audit.

For expression boundaries, `x as int as str` is one full Type target following
one annotation introducer, as selected in q1/d1. The pinned parser test
`crates/yu-syntax/src/tests/expression_structural_tails.rs:516–525` records recovery-free consumption of
that source; the syntax authority delegates the full Type and forbids guessing
expression re-entry. Nesting/grouping must be inspected as distinct CST owners
when deriving multiple checks; this audit does not certify a complete nesting
grammar. Repeating the word `as` is not a boundary counter.

## Exact bridge obligation

An approved-boundary judgment needs, at minimum, the actual boundary occurrence,
its target derivation, the incoming endpoint/interface, and the accumulated local
realization evidence. For argument annotations, the source-selected role and
the corresponding entry/body binding must also remain available. Charter §21
and conditional core §6 determine Value-entry versus retained-Computation;
ordinary Value entry forces once before body execution, while retained entry
preserves the carrier. Empty solved effect rows or unused parameters do not
change that choice. This audit does not select an additional comparison stage,
new receipt mechanism, carrier API, or wildcard rule.

Writing the selected contract schematically, with existing evidence `E`:

```text
current boundary: direct query(a, target T) succeeds with local evidence rho
export:           endpoint T, with E preserved and rho added
later boundary:   direct query(T, target U), preserving E and rho
```

This is an obligation from the approved decision, not an implementation or
an adequacy proof. The two local successes do not establish `query(a,U)`.
The existing associator supplies an expression boundary's position and input
shape, but loses the target. The production lowerer supplies none of the three
annotated resolved forms. Therefore the premise that all approved annotations
already feed that judgment is false at the inspected source snapshot. Current
rejection does not select permanent exclusion from the replacement envelope.

## Evidence independence, coverage, and omissions

The approval bundle is independent of the implementation snapshot and fixes
the required contract. The parser, associator, lowerer, and collector are
mutually dependent production components, so agreement among their inspected
clauses is not independent semantic validation. Existing test assertions are
supporting characterization only; they were read, not executed. No Yulang2
Oracle execution, independently grounded realization oracle, model comparison,
random seed, enumeration range, mutation run, compiler build, or performance
measurement was performed. Seeds/ranges/mutations are not applicable to this
read-only method. The equal-tree witness discriminates retained target input
without assuming a concrete-comparison algorithm or adaptation semantics.

Inspected production scope: `yu-syntax` binding/Pattern/parenthesized Pattern
and expression-annotation owners, identifier Type primary; `yu-hir` association,
header/root/body/direct-root lowering, `HirBinding`, `HirParameter`, and the full
`ResolvedExpr` variants; `yu-solver` item collection and plain-lambda emission;
`yu-types` annotation/source-entrypoint search; the complete one-line `yu-core`
source. Supporting tests read: binding annotations/recovery, pattern annotation
precedence, expression annotation ownership, HIR plain-header restrictions and
complex-root error ownership. Earlier HIR/callback bridge progress notes were
read as research context, not source authority or new checks.

Unverified: malformed/recovered annotations, full nested Type elaboration,
type-name binding and alias equivalence, arbitrary pattern annotations,
delimited declaration spellings beyond the source-clause derivation above,
complete entry/adaptation execution, evidence coherence, recursive-group
endpoint generation, adapters/casts, solver success conditions, source/core
adequacy, principality, native/VM paths, and production cutover authorization.
Failure conditions for the characterization are changes to the cited parser
precedence, Type-token retention, header admission, or collector/error routes.
Such changes require a delta audit; unrelated branch changes do not.

Resources: lightweight Git/Python reads and one artifact write;
zero builds/tests/probes and zero measurement repetitions. No numeric process,
CPU, RAM, or wall-time budget was supplied; peak RAM and total CPU were not
measured. Read-only commands were occasionally batched; no heavyweight process
was launched.

Recommended next action: prepare a narrow design gate for retaining each
approved boundary's complete target and role/evidence inputs at the CST-to-
resolved-HIR seam, with explicit argument-owner mapping. Seek implementation
authorization for that gate separately; research approval does not supply it.

## Reproduction and commit packet

Read checks used `git show 0ab7620:<path>`, line-numbered excerpts,
`git grep -n` over the named production/test files, `git rev-parse <rev>:<path>`,
and byte equality of the current q1/d1 files against `28dddc75f`. The explicit
production-path comparison `git diff --name-only 0ab7620 f50c8a8 -- <inspected
production paths>` was empty. `git diff --no-index --check /dev/null <leased
path>` passed for this new note; no compiler tests are required for this artifact.

- Exact leased changed path:
  `notes/progress/2026-10-05-annotation-boundary-hir-crosswalk.md`.
- Baseline: `f50c8a88882a10f109a71e2842f4d1b02982de53`.
- Source dependency: `0ab7620e167f190691a9ec50fde507d039265aa4`;
  approved bundle: `28dddc75fd598faf34dd4d069ffb231cb64a82f1`.
- Dependency hashes changed by this work: none. Pinned direct blobs:
  `yu-hir/src/lib.rs=0c5e1ac6c1acba5707b33911be82fe4a1d75caa0`,
  `yu-hir/src/module.rs=668d1b6f82fb17a96178a2353543d288c32e2762`,
  `yu-syntax/src/pattern/mod.rs=3884e2ec6c309a2c995a4c055cd6a7214dcd241d`,
  `yu-syntax/src/pattern/delimited.rs=a28f69350dc79aaec3376f535fd62e95e1bff417`,
  `yu-syntax/src/type_expr/mod.rs=8d042baa5fc8b69008a36e007dfad2b51679a7e1`,
  `yu-syntax/src/expression/tails/type_annotation.rs=1bc122c28a12a58233a0b5ab14f43fa4b0d3b3f9`,
  `yu-solver/src/lib.rs=fa118b726ebbfdc7d32b617373b4e2cb04e84682`,
  `yu-types/src/lib.rs=c3a4e95d199fba0784b7e6448b6bb37a1f2c7798`,
  `yu-core/src/lib.rs=b2f06181fd47a991935cd7d1d8f117db9523beec`,
  question `524c23ebb0b8cb008cf5e5d71ee8c3879431a782`, draft
  `2adbf2dd6209bfa1debf915bd5d69cc61917a193`, approved answer
  `1b87624d94d01aff386f31acb81cc40b2bb3b441`.
- Review: frozen and independently reviewed by `regression_auditor`; no
  blocking or major finding. One minor locator ambiguity was closed by the
  package-to-`crates/` mapping above and fully qualified test paths here. The
  expression equality remains an unexecuted, bounded source derivation. No
  theorem or production gate is declared complete.
- Proposed commit: `research: map approved annotation boundaries through pinned HIR`.
- Shared-record deltas left to primary/curator: record target loss before
  expression resolution, distinguish outer binding annotation from argument
  annotation by CST owner, and retain the open production boundary/evidence
  gate in `tasks/current.md`, `tasks/research-lab.md`, and applicable theory
  records. No authority/index/question-board change is proposed by this worker.
