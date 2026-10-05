# Mixed effect descriptors: pinned source/artifact correspondence audit

Date: 2026-10-05
Status: independently reviewed research characterization; no semantic selection, theorem closure, or implementation authority
Branch assigned: `research/simple-sub-intrusion`
Baseline: `a38e79e6157f641674103073ce1527831d3480eb`
Method: one-process read-only source audit; every source and prior-art input below was read from that committed revision
Write lease: this file only; shared records deferred to the primary

## Result and distinct contribution

The semantic gaps already identified by the descriptor, membership, capture-profile,
and complete-Function audits remain open. No new semantic bridge, source
counterexample, or evidence-carrier insufficiency was established.

There is a distinct artifact-correspondence correction: a valid expression
annotation's detailed type target survives in the parser CST, but **does not
survive as type children of the associated `HirExpr`**. Association retains
the `TypeAnnotationTail` kind/range and its preceding expression; its generic
recursive collector omits ordinary type nodes and their non-error tokens.
The earlier source-boundary audit's assertion that remaining associated-HIR
children retain the annotation target is too strong. This correction pinpoints
an earlier producer seam than merely adding an annotation case to
`ConstraintBatch::collect`. It is not evidence erasure in an accepted resolved
program: current resolved lowering rejects this expression shape.

The other useful characterization is that plain Function/computation
`BracketRow` and standalone apostrophe-bracket `EffectRowType` are distinct CST
constructs. A reader must locate the former at its original arrow/head position
before assigning a polarized port. Neither CST construct resolves `'e`,
`write`, `int`, or their same-fiber meaning.

## Authority and source locators

The assignment's governing sources were used within their declared scopes:

- `notes/design/2026-10-03-concrete-compatibility-boundary.md` §§6–9,
  especially §7 at lines 1040–1114, §8 at 1116–1910, and §9 at 1912–1957:
  role precedes port interpretation; both polarities retain shared evidence;
  the approved deep-handler fragment permits only targeted removal supported
  by the complete image. The document is a Draft recording approved directions,
  not implementation authority.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` §6 at
  303–519 and §9 at 904 onward: syntax-directed parameter entry,
  `Value(Fun(P,Result(I_b)))`, complete invocation distinct from body/result,
  and directions derived from interactions. These derivation rules assume
  admitted annotation/declaration interfaces; they do not generate arbitrary
  raw annotation membership.
- `notes/design/2026-10-02-typed-boundary-realization-draft.md` §6 at
  665–1027: original profile positions, `Flow`, `Receive`, event-specific
  `Observe`, scoped `Inc_C`, and shared `K,D`. **There is no §8 in this file at
  the assigned revision.** The requested §8 locator supplies no additional
  premise; §6's explicit source-realization boundary was retained.
- `notes/design/2026-10-03-callback-context-delivery.md` §§2–4 at 36–178:
  normative B delivers the expected Handler boundary before body constraints,
  synthesizes endpoints independently, then emits `F_lit <: F_cb`; existing
  Pure values preserve actual introduction and entry.
- Committed `questions/2026-10-05-function-effect-row-denotation/approved-answer.md`,
  exact `function-effect-row-denotation-answer/d1`: covariant allowance,
  contravariant `int <: 'a` example, and deep targeted removal; general
  membership, variance, parser spelling and implementation remain unselected.
- Committed `questions/2026-10-05-production-function-denotation/approved-answer.md`,
  exact `production-function-denotation-answer/d1`: Option A interprets complete
  observations in original `Rel_C` at one `(nu,K,D)` and keeps admission
  comparison-independent; Option 2 does not require membership to equal
  constructor-generated `P_ref`.

`notes/design/INDEX.md` entries for these sources were used as navigation.
`rules/design-authority.md`, `rules/research-lab.md`, and
`rules/git-concurrency.md` supply authority, duplicate-investigation stopping,
and the pinned-input/disjoint-output protocol. No dirty note or pending answer
was consumed.

## Exact source-to-artifact crosswalk

| Required step | Artifact actually present at the baseline | First missing producer/consumer seam |
|---|---|---|
| Abstract component `'e` | Type parser admits `SigilIdentifier` and emits its token unchanged (`yu-syntax/src/type_expr/mod.rs:858`, especially 875). The committed CST test `effect_row_type_keeps_its_compound_opener_and_items` (`src/tests/type_expr.rs:2847`) includes `'['e]`. | No effect-variable binder resolution, descriptor occurrence, or complete correlated view is produced from that token. Repeated spelling is not a proof of shared semantic assignment. |
| Concrete item `write int` | Generic `Identifier` primary plus `TypeApplyArgument` parses the type-application shape (`type_expr/mod.rs:875,1329,2143`). Row items are direct `TypeExpression` children, in source order. | This is a type name/application, not an operation declaration lookup or an owned request occurrence. No current semantic HIR producer connects this item to a concrete `Γ_b` contract or typed family incidence. No special concrete-effect CST tag is needed or implied. |
| Mixed components in one source row | `BracketRow` uses the same delimited Type parser (`type_expr/mod.rs:1595`; `type_expr/delimited.rs:38`); comma/semicolon/newline separate ordinary items. Original separate item nodes/ranges remain available in CST. | Co-location in a bracket node does not define joint satisfaction at one nonempty `(nu,K,D)` fiber, attachment, or the same abstract view in another port. That requires source elaboration over the original occurrences. |
| Row at a Function input/result position | A trailing plain row belongs to `TypeArrowTail` before `->` (`mod.rs:1532`); a leading plain row belongs to `TypeExpression` before its required head (`mod.rs:1355`). Existing CST tests pin both layouts (`tests/type_expr/bracket_arrow_cst.rs:16`; `leading_row_cst.rs:15`). | This establishes syntactic positions only. Handler/Pure role, retained/value entry, original boundary/profile, and complete argument/invocation port construction are absent from resolved HIR. Interaction-derived polarity is a later source rule, not a parser tag. |
| Expression annotation carries these type occurrences toward elaboration | `type_annotation_tail_normalized` (`expression/tails/type_annotation.rs:17`) parses full Type after `as` below `TypeAnnotationTail`. | `yu-hir/src/lib.rs:305,458,494,504` preserves the outer annotation wrapper/range and operand but flattens away ordinary type structure/tokens. A consumer must still consult the original CST or receive an explicitly elaborated immutable source-interface input; this audit selects no API. |
| Resolved annotated Function/callback | `ResolvedExpr` has Lambda/Integer/Name/Error only (`yu-hir/src/module.rs:426`); `HirParameter` has ID/name/range only (`:361`); `SemanticImports` is empty (`:106`). | `plain_binding_header` (`:1471`) admits only plain identifier targets and a single plain parameter, rejecting annotated headers. `lower_simple_chain` (`:1402`) requires a direct atom and a childless associated Value, rejecting annotation/call structure. There is no resolved annotation/application/operation/handler node. |
| Source facts reach production Function term | `ConstraintBatch::collect` (`yu-solver/src/lib.rs:815`) receives only `Arc<HirModule>`. `emit_lambda` (`:1555`) and `LambdaRecipe` (`:689`) retain the accepted pure-body effect link; `admit_lambda_fact` (`:10539`) emits a four-child positive Function fact. | Accepted lambda generation has no annotated boundary or expected callback formal input. Current body effect rows contain only the existing polarized bottom/empty facts and links. An internal effect-row variable is not source `'e`; `EmptyEffectNegative` is not a definition of source annotation meaning. |
| Deep targeted subtraction | The selected shallow source image and derived deep expansion exist in `ordinary-computation-semantics-package.md` §5 at 400 onward, with `wrap_H(k) = λa. D_H[Resume(k,a)]` at 448 onward. Typed-boundary §6 supplies conditional event/path eligibility and transport. | Current resolved HIR has no handler or request producer; current Function fact emission supplies no source-selected subtraction attachment/image. The bridge must establish actual delayed recursive reapplication, fresh active-owner paths, concrete compatibility, and complete output preservation before subtracting a contribution. Capture eligibility alone is not that proof. |

The grammar distinction follows the committed public syntax contracts:
`syntax-reference/en/src/types/bracket-row-grammar.md` §§1–4 and
`effect-row-type.md` §§1–4. Plain `['e, write int]` in a Function signature
position is a `BracketRow`; standalone `'['e, write int]` is an
`EffectRowType`. A bare plain bracket row is not a complete standalone type:
the leading form requires a type head, and the trailing form requires an
arrow. Both contracts explicitly exclude type meaning and lowering.

`TypeExpression` ML application is independently specified by
`syntax-reference/en/src/types/type-expression-core.md` §§2–4. The audit
deduces the `write int` syntactic shape from those generic rules; it did not
run a new parser probe or claim a committed test for that exact spelling.

## Narrow correction to the prior associated-HIR claim

In `ChainParser::value` (`yu-hir/src/lib.rs:494`), `collect_nested_items`
walks descendants and outputs only associated `OperatorChain` nodes,
`Invalid`, `Missing`/`Error`, or raw Error tokens (`:504–526`). All other
nodes are recursively traversed; ordinary non-error tokens are discarded.
Therefore a recovery-free type target composed only of ordinary type nodes
and tokens produces an empty `tail_children` vector.

`structural_continuation` (`:458`) prepends the preceding expression to that
vector. Its resulting annotation Value preserves the annotation kind and a
range spanning the operand through the syntax tail, but not the target's
ordinary type children. The existing
`type_annotation_receives_the_reduced_dynamic_segment` test (`:2516`)
checks the wrapper and first operand; it does not assert target preservation.
Recovery-bearing targets can retain recovery descendants, which does not
restore the missing ordinary type structure.

This is a structural read of committed code, conditional on the named
recovery-free target grammar, rather than an executed parser/HIR experiment.
The complete target remains in the `ParsedFile` CST passed into lowering
(`module.rs:802`); `HirModule` itself (`:705`) retains source revision/items
and errors, not the parser tree. A proposed resolved-HIR elaborator cannot
recover semantic `'e`/concrete-item occurrences from `HirExpr` children alone.

## Existing mixed/deep source witness and its limit

The committed stable-core public-signature fixture
`tests/contracts/stable-core/v0/public-signature/pass/data_position_effect_function_public_signature/main.yu`
contains `act tick 'a`, a stored `run: () -> [tick 'a; 'e] ()`, and
`b.handle(...): ['e] ()` with recursive `loop` handling `tick::ping` and
resumption. Its `signature.toml` expects
`box('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()` and excludes `tick`,
`AllExcept`, and `#` from the public signature. The VM fixture
`tests/contracts/stable-core/v0/run/vm/pass/example_effect_handler/main.yu:13–14`
explicitly uses a retained `x: [_] _` and recursive resumption through
`listen(k (),...)` under `catch`.

These establish retained source/expected-output artifacts for mixed rows,
typed operation arguments, and recursive handler reapplication. They do not
establish current successor acceptance or the approved `write int` comparison
instance, derive the annotation-to-profile bridge, or prove full-image absence
of same-point re-emissions. The assigned current crates contain no
`crates/infer/src/annotation` implementation; legacy locators quoted in older
designs are not current successor producers. No frozen-main implementation
was read or treated as successor authority.

## Prior audits checked and duplication boundary

All identities below refer to their contents at the assigned baseline:

- `2026-10-05-function-effect-descriptor-derivation.md`: already isolates the
  mixed comparison-independent annotation clause and event-identity issue.
- `2026-10-05-effect-component-membership-playground.md`, including visibility
  reconciliation: exact-origin veto is already rejected for the selected
  callback subcase; annotation-to-`Γ_b` and mixed composition remain open.
- `2026-10-05-concrete-capture-profile-derivation.md`: already derives the
  conditional local eligibility consequence while assuming the profile.
- `2026-10-05-effect-attachment-subtraction-playground.md`: already separates
  typed support, contribution attachment, and complete-image removal.
- `2026-10-05-production-complete-function-interpretation-audit.md` and
  `2026-10-05-production-function-denotation-followup.md`: membership/admission
  rule construction is not supplied by four endpoints or source `P_ref`.
- `2026-10-04-hir-source-core-boundary.md` and
  `2026-10-04-lambda-endpoint-owner-trace.md`: resolved source grammar and
  accepted F5 lambda facts already delimit the production bridge.
- `2026-10-04-value-entry-bind-projection.md`: joint port/profile arrows and
  flat normalization are already conditional; another support-union argument
  would duplicate it.
- `2026-10-05-source-boundary-coverage-audit.md`: annotation rejection remains
  correct; its associated-target-preservation sentence needs the narrow
  correction above.

The smallest new artifact bridge is consequently the CST-to-associated-HIR
target-retention correction and its required source input, not another
membership rule or subtraction model. The next useful consumer can start from
the original, role-positioned row CST plus independently resolved interfaces;
it cannot assume the associated expression is already a typed annotation.
Whether a complete semantic clause can be derived still belongs to the
constructive lane. This audit stops at that boundary.

## Verification, omissions and handoff

Verification was static inspection of pinned files with read-only `git show`,
`git grep`, and `git ls-tree`, plus direct comparison of the named prior audits.
The three initially read rule files were byte-compared with the baseline and
matched it. Read commands were batched with at most five lightweight shell
calls concurrently; this exceeded the packet's literal one-process read limit.
No compute experiment, compiler test, build, measurement, generated artifact,
Git mutation, or child agent was used. No runtime/parser execution is claimed.
Independent read-only source review found one minor fixture-line locator error,
repaired above; it found no blocking or major issue in the bounded source/HIR
correspondence scope. Semantic annotation adequacy and production containment
remain open and outside that review.

Omitted: frozen Oracle execution/implementation, complete arbitrary annotation
typing, solver membership/admission construction, unrestricted operation
variance, State/import worlds, and the deep-handler complete-image theorem.
Existing evidence was not shown unable to represent any required fact. A
same-family residual obstruction to blanket cancellation is prior evidence,
not a counterexample to approved targeted deep removal.

Commit packet: only this leased research note; all dependencies pinned to
the full baseline above; bounded source/HIR review complete after the minor
fixture-locator repair; suggested message
`docs(research): trace mixed effect source correspondence seams`.
`tasks/current.md`, theory maps, design index/status, and the inaccurate prior
audit sentence are intentionally deferred to primary-owned adjudication and
integration. No coherent semantic gate is declared complete.
