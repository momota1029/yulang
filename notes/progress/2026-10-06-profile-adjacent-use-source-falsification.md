# Adjacent formal uses: bounded source falsification of profile shortcuts

Date: 2026-10-06
Baseline: `f19fb4f473344e8f4478ae145d0915e04d250b09`
Status: frozen, unreviewed research submission; non-authoritative
Method: manual source-shape audit and conditional address derivation
Scope: repeated formal use, formal annotation, and later higher-order calls
Implementation authority: none

## 1. Result and precise claim boundary

The accepted exact-source constructor introduces
`p_0=(beta,call.effect)`, where `beta=(d_f,R_f)`. The address does not contain
the Call occurrence. Consequently, **if that constructor extends to several
direct calls of the same original formal root**, their generated addresses
coalesce while their elimination witnesses remain distinct. One syntactic
Call per original position is therefore not the constructor's general counting
law. For direct calls at one root it is a plausible repeated-use recipe, not
an established component-wide profile-completeness rule.

The exact candidate's unresolved converse remains:

```text
Applicable_original(C,d_f,R_f,p;xi) => p = p_0.
```

This audit does not refute it. A written formal annotation changes an input
premise and requires its own occurrence-to-profile constructor. An explicit
call of a returned Function supplies a second source elimination at a result
view; assigning it an original `beta` path requires a typed source
correspondence not supplied by the direct-formal constructor. Returning the
captured `step` closure and subsequently calling it instead reuses its body
Call; transport or execution does not duplicate that original introduction.

The useful separation is between an original address, an occurrence's
elimination witness, and a transported/activated view address. Counting any
one as another fails even before complete profile applicability is proved.

## 2. Authority, dependencies and explicit hypotheses

Authority is [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 and the [exact nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4. The integrated call-view answer a2 decisions 1–6 and nested-block
answer a1 items 1–4 were read with their receipts. They select shared source
contracts, stable original positions/scopes, one joint `xi=(nu,K,D)`, Q
independence, annotation-dependent protection, and only the named block's
sequential binding/final-value/capture interpretation. No broader brace
meaning, generic Value-entry role theorem, or detailed profile rule follows.

Research premises are the [initial Call construction](2026-10-06-source-call-generation-construction.md)
§§3–4.4 and the [least-generated footprint](2026-10-06-profile-source-normal-form-construction.md)
§§3–6. Their independently reviewed exact-source results are dependencies;
this producer does not independently certify them. Typed-core §6 result
synthesis and typed-boundary §6 indexed packet transport are conditional
mathematical rules, not completed raw-source profile formation.

The derivations below state additional hypotheses where used:

- **Hroot:** two direct callee references resolve to the same `d_f` and share
  the same original `R_f,beta`; occurrence instantiation retains an
  original-to-view correspondence rather than freshening the original source
  identity. Shared formation is selected; the exact generalization proof is
  still required outside the established source slice.
- **Hdirect:** the initial direct-formal Function-elimination address recipe
  applies at both occurrences, without extending the one-use `Role_0`
  resolution theorem to a computed argument.
- **Htransport:** every packet image uses an independently typed
  correspondence and the same joint assignment, retaining original witnesses,
  `K,D,L`, and each indexed actual-provider/result input.
- **Hresult:** when explicitly stated, source typing establishes a returned
  callable and a matching original-result-to-view correspondence. Neither
  solved type shape alone nor Q success establishes this hypothesis.

## 3. Checked source envelope and classifications

“Source-valid shape” here means justified by selected source syntax and
existing source-occurrence contracts. It does not mean this audit ran the
parser, established satisfying inference, or proved production acceptance.

| Shape | Classification and evidence | Profile consequence actually supported |
| --- | --- | --- |
| `my apply f = { my step x = f x; step }` | Exact source meaning Authoritative; retained in existing HIR source-occurrence fixture | Established initial research construction generates one `p_0`; full original completeness remains open |
| `my apply f x = f(f x)` | Source-valid shape: exact repeated-use fixture in `shadow_call_use_source_inputs.rs`, with two distinct Calls/uses and one binder | Under Hroot/Hdirect, two elimination witnesses share the same original `p_0`; full typing and outer-use role refinement are unproved |
| `apply(f: _ -> [io] _, x) = f x` | Exact approved source-contract example, call-view §§1.1/4 | Scoped `io` removal permission, with occurrence/contribution realization still open; no unconditional removal |
| `my apply (f: T) x = f x` | Source-valid annotated shape: existing `shadow_annotation_positions.rs` fixture; arbitrary `T` is a supplied annotation interface | Annotation occurrence/binder incidence exists as source data; typed profile correspondence remains pending |
| `my apply f x = (f x) x` | Source-valid shape: exact computed-callee fixture in `shadow_call_use_source_inputs.rs` | Two Calls, only the first directly names the formal; second Call has a result-view effect address, requiring Hresult to relate it to original `beta` |
| Exact captured-step declaration followed by `my use k = k 0` and `my run f = use (apply f)` | Conditional composition: ordinary Name/Lambda/Call source rules justify the constituents; no whole-program parsing, inference, or use-generalization proof performed | Later execution can reach the original captured `f x`; caller's `k` and `run`'s `f` are separate source formals, not identical `beta` by spelling |
| `my apply f = { my step x = f x; my again y = f y; step }` | Grammar-shaped but **conditional source meaning**, outside the exact block addendum | Not used as a source-semantic counterexample or proof of a second original position |
| A supplied signature containing `call.effect` and `result.call.effect` without a source derivation | Merely abstract | Not a source-valid witness of original applicability |

The existing fixtures are read evidence of intended source contracts, not
new execution results. The source-call-use accessor deliberately excludes a
grouped or computed callee from its direct-formal incidence rows; its pending
judgments make that distinction explicit. This absence is not a claim that
computed calls are semantically forbidden.

## 4. Repeated direct calls: smallest counting discriminator

Use the existing source shape `my apply f x = f(f x)`. There are two distinct
callee occurrences `u_1,u_2`, resolved to `d_f`; call the inner elimination
`c_1` and the outer elimination `c_2`. Under Hroot/Hdirect:

```text
beta_1 = (d_f,R_f) = beta_2 = beta
p_1 = (beta,call.effect) = p_2 = p_0
ElimOrigin(c_1,u_1,d_f,R_f,p_0,p_out(c_1))
ElimOrigin(c_2,u_2,d_f,R_f,p_0,p_out(c_2))
G_direct(beta) = {p_1} union {p_2} = {p_0}.
```

The elimination records remain distinct because they retain `c_i,u_i` and
the occurrence-specific `p_out(c_i)`. Any actual per-use instantiation
correspondence likewise remains indexed. Union at the original address must
retain those witnesses rather than deleting an occurrence or its constraints.
Distinct dynamic boundary activations, if later realized, remain distinct
even when their static template is the same.

This is a minimized conditional falsifier of the shortcut
`number of original positions = number of direct Calls`: two direct Calls
and one original root suffice. With one Call the shortcut cannot be
distinguished. It is not a counterexample to full original singleton
applicability, because Hdirect specifies only the displayed generated leaves.

The inner argument is the returning Name `x`. The outer argument is the
whole computation `f x`, not another Name-return argument. Typed-core §6
therefore requires whole-argument compatibility at the outer Call. Copying
the exact one-use ordinary-value `Role_0` certificate to both occurrences
would change its premises. A fixture showing the same binder does not prove
that both formal/use relationships satisfy the accepted role refinement.

## 5. Annotation boundary: a genuine extra input, not a slot count

The approved annotated example has one direct Call but violates
`NoAnnotation(d_f)`, a premise of `Foot-Call`'s unannotated policy. Reusing
`Gamma_gen(beta,p_0)=(FullProtection,NoGrant)` unchanged at that source is
therefore not a valid derivation. The annotation provides the selected scoped
`io` permission; it does not assert a literal final inferred Function shape,
an empty row, or actual removal.

The relevant additional source occurrence is the annotation-owned effect
contract, whose scope and original position must survive elaboration and
use. The minimal `_ -> [io] _` example does **not** prove a second original
address: an annotation-to-profile rule might associate the permission with
the already introduced immediate-call position. The missing correspondence
must be shown, not inferred from equal families or printed type equality.

Nested annotated contracts could distinguish multiple positions, but no new
nesting example is promoted here. Typed-boundary §6 requires separately
tagged annotation positions and prohibits copying an outer grant onto all
latent descendants. This is the exact failure condition for a proposed
component-wide “one Call means the whole profile is p0” rule: an independently
applicable annotation or formal-signature introduction can add a position or
policy obligation that Call counting does not classify.

## 6. Later higher-order calls: two different source routes

For the exact captured-step source, the returned `step` keeps `f` privately
in its environment. Calling that closure later reaches the same body Call
`c` and same original `beta_f,p_0`. Htransport retains the original packet;
another execution or Name reference does not become another source
introduction. The helper `use k = k 0` adds a real elimination of its own
formal `k`. Its original root is different from outer `apply`'s `f`, even
if actual receipt later relates their views. The caller `run`'s formal named
`f` is also a different binder. Type equality, spelling, or a shared runtime
value cannot identify those source roots.

In contrast, `my apply f x = (f x) x` has a source Call of the **result of f**.
Under typed-core result synthesis, the first Call has symbolic result `A_1`;
the second imposes callable constraints on that result before satisfiability.
It supplies its own immediate complete-invocation observation address.
This conclusion needs no recursive force based on latent type shape.

The direct-formal `Gen-Call-0` rule only covers the first Call. To count the
second as an original position of `beta_f`, a generalized rule would need:

```text
SourceCalleePath(c_2, beta_f, result; xi)
  and typed original/result correspondence
  => original address (beta_f,result.call.effect).
```

That is a **conditional candidate**, not a selected source rule. An
alternative introduction rooted at the computed call/view also needs its
source identity rule; merely inventing a binder for the result does not
derive it. Existing transport says that independently supplied matching
result positions project into the result view. It does not prove that the
original `beta_f` profile introduced such a position. In particular,
`call.effect` does not project to a returned `latent.effect` or a nested
call's `call.effect` merely because the returned value is callable.

Thus the computed-callee occurrence is a concrete source-shaped discriminator
for any proposed general profile rule: the rule must classify its origin and
matching result path. It is not an established counterexample against the
exact captured-step singleton, which returns a separately introduced local
closure and contains no call of `f`'s result.

## 7. Checks, independence, omitted scope and resources

Commands used: bounded `rg`/`cat`/`sed` reads of the named Authority,
research, syntax and source-fixture sections; `git rev-parse HEAD`;
`git status --short`; `git diff --name-only f19fb4f47 -- <direct paths>`;
dependency `sha256sum`; and the leased-note whitespace check. Direct
dependencies matched the pinned baseline at the recorded pre-write check.
Initial locator searches named nonexistent `spec/`, `web/docs/reference`,
`2026-09-17-syntax-architecture.md` and `tests/expression.rs`; their absence
was not used as semantic evidence. The actual syntax architecture and
existing source-shape fixtures were then located. Broad architecture search
was truncated and only its indicated relevant matches were inspected; this
is not an exhaustive grammar or whole-repository audit.

There is no checker, independent executable oracle, Oracle semantic input,
test/build, randomized seed/range, or executed mutation. The conditional
derivations share the published constructor/transport assumptions. Existing
fixtures independently constrain source occurrence bookkeeping, but they
leave semantics pending and may share the selected source assumptions.
Agreement is not an independent proof of the original profile rules.

Conceptual mutations examined: adding one direct Call; changing annotation
absence to the approved `[io]` contract; explicitly calling a result;
freshening original `beta` per occurrence; equating Call count with address
count; copying outer protection to a latent result; and merging distinct
formals by spelling or runtime identity. Their discriminating premises are
stated above. None is an executed mutation test.

The finite manual envelope is the eight classified rows in §3, plus the
direct-source construction and the relevant source-fixture branches. No
complete satisfying decorated source realization, runtime receiver/liveness,
recursive component, general local polymorphism, adapter, arbitrary annotation
elaboration, all-view principality, A admission, or production Option A/2
containment was verified. No source-valid second original applicable position
at the exact candidate was found within this envelope. A two-position abstract
signature alone leaves the same original-introduction premise untouched;
another supplied-profile toy probe would not advance this lane.

Resource use: manual audit with short read processes; zero heavyweight
processes, builds, tests, or unbounded searches. No numeric CPU/RAM/wall-time allowance
was supplied beyond bounded manual work. Peak RAM, cumulative CPU and total
authoring wall time were not instrumented. Only the leased note was written;
no Git mutation, child delegation, compiler edit or shared-record edit occurred.

Recommended next action: require the proposed original-applicability rule to
classify direct repeated uses, an annotation-owned clause, and the computed
callee of `(f x) x`, with original-to-view witnesses preserved, before claiming
component-wide completeness. Keep the exact candidate's P converse open.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-profile-adjacent-use-source-falsification.md`.
- Baseline SHA: `f19fb4f473344e8f4478ae145d0915e04d250b09`.
- Dependency hashes changed from pinned baseline: none at final comparison.
  Direct dependency SHA-256 values:

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
ea32179888d41ceaddda7ba5c3566e1e83bf489da3fba763a28fda37e8876fad  notes/progress/2026-10-06-profile-source-normal-form-construction.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
6ad83cc0169353c37c9b14e72b4e283d7bdd905571c124f348dca8ae4150ce94  crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs
9b7be467a0a2bb56fd9576549e50b23350f378f16d35382b410d331b4aec3b37  crates/yu-hir/src/tests/shadow_call_source_occurrences.rs
```

- Review status: producer-frozen and unreviewed; no independent certification
  or theorem/source-authority promotion.
- Checks already run: narrow source/rule reads, baseline/dependency checks,
  final exact-path status, and whitespace check; no executable semantic check.
- Proposed one-line checkpoint message:
  `research: bound profile rules at repeated annotated and result calls`.
- Shared-record deltas intentionally left for primary/curator: record the
  occurrence/address distinction and computed-callee applicability obligation
  if accepted; retain P open and no production authority. No shared record or
  question bundle was changed. Writes stopped before this frozen submission.
