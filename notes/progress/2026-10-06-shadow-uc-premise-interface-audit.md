# Shadow local source-use premise interface audit

Date: 2026-10-06
Baseline: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`
Status: frozen research-only source/implementation correspondence audit; unreviewed
Claim class: bounded representation characterization and conditional structural derivation
Authority: no new semantics, implementation approval, or main-gate closure
Lease: this note only

## Objective and governing boundary

Identify which existing shadow objects can reference the first missing local
source-use producer `U_c`, without pretending that its interpretation exists.
The governing sources are `tasks/current.md` “Objective and authority” and
“Active unrestricted proof gates”; the reviewed
[minimal source clause](2026-10-06-main-source-generation-minimal-clause.md)
§§3–6; and Authoritative
[inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§2–3, with §§1.1/4–5 preserving view/protection and implementation boundaries.
The exact nested candidate has only the source meaning selected by the
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4. The approved call-view answer `a2` supplies direction, not a completed rule.

The selected singleton outcome is fixed: annotation absence gives the internal
fully protected Handler seed; ordinary-value evidence later determines
`NonHandlerFormal` on that inferred formal/use relationship. The actual
callable's role/entry remains its own. This audit neither chooses another
meaning nor extends that outcome to mixed uses or arbitrary Value-entry calls.

## Existing identity and evidence map

All code locators below refer to the pinned baseline. `LocalId` equality uses
the artifact's `Arc` identity and arena index (`crates/yu-hir/src/shadow.rs:270`).
IDs are stable within one retained artifact, not persistent IDs across reparses,
serialization, generalization, or instantiation. Those preservation operations
are absent from this shadow slice.

| Requested input | Existing object and exact locator | What it establishes / limit |
| --- | --- | --- |
| Call and source occurrence | `ApplicationSourceOccurrence` at `shadow.rs:289`; scan at `:999`; `Form::Apply` at `:406` | Existing call `ExprId`, exact tail `PositionId`, source form, callee and whole argument `ExprId`. The tail's range can equal the argument's range: range containment is not occurrence identity. |
| Direct resolved callee | `ResolvedCallIncidence` at `:317`; filter at `:1026`; `Form::Use` at `:399` | Existing direct callee `UseId` and resolved `BinderId`. It skips grouped/computed/integer callees; it is not an inventory of every eligible semantic use. |
| Use occurrence and binder position | `use_expression`/`use_position` at `:1062`/`:1068`; `Binder::position` at `:958` | Exact IdentifierExpression and IdentifierPattern occurrences in this artifact. `Binder` has no formal/type/role tag; parameter status must be established from the retained header or an existing Lambda parameter edge. |
| Argument expression | `ApplicationSourceOccurrence::argument` at `:310`; `Expression::position`/`form` at `:971`/`:977` | Entire retained argument expression, including Group/Apply structure; a direct argument Use exposes its own resolved binder and occurrence. No `Value(A_x)` or `Comp(empty,A_x)` certificate is stored. |
| Parameter annotation | `ParameterAnnotationIncidence` at `:243`; exact producer at `:518`; `parameter_pattern` at `:636` | Atomic unannotated parameter or one grouped `(f: T)` association to an existing `AnnotationId`. Whole-target/expression annotations are not formal annotations. Unsupported skeleton projection prevents claiming its associations are complete. |
| Annotation occurrence | `AnnotationOccurrence` at `:225`; retention at `:143`; lookup at `:70` | Branded occurrence and raw position. Its correspondence is explicitly `PendingTypedPortAndProfile`; no permission or effect contribution is identified. |
| Lexical source scope | `Position::parent`/`ordinal` at `:209`/`:213`; Lambda/Bind edges at `:383`/`:391`; exact nested recognizer at `:1113`; scope validator at `:822` | Raw CST ancestry, declaration/parameter edges where projected, and selected sequential lexical visibility. There is no `ScopeId`, original semantic environment, generalized interface, or joint assignment. Several multi-formal skeletons have no projected declaration Lambda; raw ancestry still survives. |
| Captured direct use in exact candidate | `CaptureUseIncidence` at `:343`; producer at `:1276`; validation at `:789` | Same outer binder, local Lambda, exact callee UseId and position. This is lexical capture incidence, not typed capture attachment, receipt or runtime ownership. |
| Existing unresolved call obligation | `Premise`/`PendingPremise` at `:421`/`:433`; insertion at `:1088` | Each Apply receives four pending markers, including Q-independent source formation. A marker contains only call ExprId and enum; there is no separate interpreted `U_c` or symbolic endpoint arena. |

`crates/yu-core/src/shadow.rs:4` merely reexports these HIR-owned objects.
Its facade mints no identities or judgments. The feature gates are
`crates/yu-core/src/lib.rs:3` and `crates/yu-hir/src/lib.rs:9`.

## Conditional structural derivation and exact missing premise

Hypotheses: (H1) one immutable artifact whose skeleton projection succeeded;
(H2) an Apply selected by the existing direct-Use incidence iterator;
(H3) every joined reference is read from that same artifact; (H4) any assertion
of parameter-annotation absence is restricted to successfully recognized
parameter shapes, and parameter status is checked separately from BinderId.

Under H1–H3, the following join is a derived source-reference tuple:

```text
c = incidence.application.expression
p_c = incidence.application.position
u_f = incidence.occurrence
d_f = incidence.binder
e_arg = incidence.application.argument
p_arg = skeleton.expression(e_arg).position
p_f = skeleton.binder(d_f).position
annotations_f = exact parameter_annotations whose parameter == d_f
source_context = original retained CST ancestry plus available Lambda/Bind edges
```

The scan emits an existing Apply; its filter matches that Apply's direct
callee Form::Use; validation checks branded references and the UseId inverse
map. Thus no new callee/use/binder identity is invented. Under H4, the empty
annotation match means absence in the bounded formal association, rather than
absence of all annotations in the file. This proves only a reference join.

For `my apply f = { my step x = f x; step }`, the selected recognizer adds
outer/local Lambda edges and sequential Bind; `CaptureUseIncidence` points
back to the same `d_f,u_f`. The argument is a resolved use of local `x`.
The exact candidate's complete singleton callee inventory is supported by its
narrow recognizer, not by counting the direct-use iterator for arbitrary input.
For the flat `my apply f x = f x`, raw header ancestry supplies the formal
context although the multi-formal declaration has no projected Lambda root.

The reviewed source derivation can *conditionally assign* symbolic
`A_f,A_x,E_c,A_c` and `Comp(empty,A_x)` to the exact ordinary name use. Shadow
does not store or prove that derivation. In particular, IdentifierExpression,
Form::Use, or `e_arg` cannot stand in for actual ordinary-value typing.
The unresolved semantic premise remains exactly minimal-clause §5:

```text
U_c(xi; inferred_seed_view, inferred_refined_view,
         whole_argument_view, complete_invocation_view), xi = (nu,K,D).
```

The source tuple can locate this premise; it cannot provide its permitted
correlated tuples. `F_cb`, provisional/refined typed views, `beta/Slots(beta)`,
typed paths/Flow, effect contribution, receipt, owner/receiver, original joint
`xi`, and independent context/admission require the missing semantic judgments.
The last two source-definition clauses in minimal-clause §6 remain separate;
neither is discharged by appending fields to a pending U_c record.

## Smallest safe next shadow slice

The existing API already permits the source join above. If an explicit
interface is useful, the smallest safe addition is a read-only view over that
join, restricted to the already admitted exact source envelope, with local
formal-use interpretation explicitly pending. It may expose callee use/binder,
whole argument expression, exact annotation incidence and original syntax
context. It should reuse identities, keep the current four premises pending,
and store no `Value` classification, role answer, protected seed, profile or
semantic acceptance. A separate local pending marker can name the dependency
without declaring the whole shared-component producer satisfied.

The primary needs separate exact implementation/test authorization before
writing that slice. Proposed focused checks are: exact flat/nested joins;
foreign-artifact rejection; noninitial grouped formal annotation; distinct
repeated callee occurrences sharing a binder; and explicit pending status.
Grouped/computed callee exclusions must stay visible rather than being counted
as zero semantic uses. No general use aggregation or lexical scope carrier is
needed to exercise the exact singleton reference.

## Evidence, discriminators and omissions

This is source/code correspondence, not an executable probe or semantic
counterexample. The inspected existing structural witness `my f x = 42 x`
(`shadow_resolved_call_incidence.rs:104`) retains one Apply but zero direct-Use
incidences. It discriminates Apply inventory from resolved formal-use inventory;
it establishes no well-typed acceptance or selected role. The nested/repeated
witness `my f x = x(x x)` (`:6`) distinguishes shared binder from distinct use,
call and source identities. Neither witness falsifies the chosen language meaning.

Existing tests were read, not rerun: `shadow_call_source_occurrences.rs:69`
checks the exact captured candidate, `:154` checks artifact separation;
`shadow_annotation_positions.rs:224`, `:308`, `:322` discriminate formal
association, invalid association and noninitial identity shortcuts;
`shadow_source_core.rs:724` derives the exact nested lexical structure from
direct CST ownership and a separate lexical environment. That differential
shares the parser tree and selected source meaning with shadow. It is
independent of the shadow lexical traversal, not an independent source-typing
oracle. The call-incidence tests cross-check the same skeleton and therefore
provide internal identity consistency only. No Oracle was invoked or relied on.

Proposed mutations, not performed: equating annotation zero with every formal;
equating one binder with one call/use; treating direct-use filtering as complete
inventory; treating argument syntax as Value typing; promoting raw ancestry to
typed Flow or Q success to admission. The first two are targeted by existing
tests. The last three require explicit boundary checks and cannot be disproved
as semantic rules by a checker that assumes them.

Coverage is bounded to the baseline code paths and listed fixtures, with no
random seeds, enumerated ranges, executable mutations or exhaustive search.
Failure conditions for this audit are changed dependency bytes, failed skeleton
projection, foreign IDs, an unrecognized parameter shape, or extending the join
to claims about grouped/computed/mixed uses without additional derivation.
General recursion, polymorphism, annotation-to-profile formation, admission,
source adequacy and production/F5/Oracle semantic parity remain unverified.

Commands: bounded `cat`/`sed`/`rg` source reads; read-only `git rev-parse HEAD`
and `git status --short`; a Python byte comparison of 15 direct dependencies
against `git show <baseline>:<path>` found all unchanged. No code/test/build,
formatter, checker, benchmark, Oracle run, Git mutation or child process wave
was performed. One lightweight shell process per tool command; reads/checks
were brief, with no heavy process or performance sample. Total wall time and
peak RSS were not measured; there was no assigned numeric compute budget.

Recommended next action: have the primary choose the exact syntax-only
pending-input view as the next shadow slice, retaining ordinary-value typing
and U_c interpretation as separate unresolved judgments.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-shadow-uc-premise-interface-audit.md`.
- Baseline SHA: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`.
- Dependency changes: none in the 15 direct source/design/task/test/facade
  dependencies checked against that baseline; revalidate before integration.
- Claim/review status: frozen research-only bounded characterization;
  independent review pending; no semantic or production authority.
- Checks already run: narrow source/contract reads and baseline byte equality;
  no runtime verification. No code or test edits.
- Proposed commit message: `research: audit shadow inputs for pending local U_c producer`.
- Shared-record deltas intentionally left for primary/curator: link this audit
  from the shadow next-slice record if accepted; record that the join is already
  representable while Value typing, symbolic endpoints and U_c interpretation
  remain absent. Do not promote the main source-generation gate.
