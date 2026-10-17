# Accepted Call: association, projection and the HIR admission obstruction

Status: frozen candidate source-correspondence analysis; independent review pending.
Author: `/root/astra_accepted_call_hir_projection`, sole author; session `current-session`.
Assignment: `accepted-call-hir-projection`, revision 1.
Contract: `accepted-call-hir-admission-contract-20261017`, revision 2,
SHA-256 `f92c1269f47ae1ba3c002244f7254ebc7792af5270ad6a634f033e91323cf19a`.
Semantic baseline supplied by Luna: `577172e30fe9e282f910cb5ff8267a42beea4a75`.
Contract checkpoint supplied by Luna: `328f813d9`; no Git inspected or invoked.
Requested model/effort: gpt-6-astra / medium. Observed model/effort: UNKNOWN / UNKNOWN.

## Result and original parent application

Existing authority determines structural left association. It does **not**
authorize error-free ordinary HIR admission of application bodies. The pinned
constructors explain why retaining the applications in `LocalSource` does not
pass the prior zero-HIR-error assertion. The missing clause is an explicit HIR
admission and diagnostic rule for structurally supported applications, together
with its chosen ordinary representation and identity contract. This is a
language/API authority seam for Luna's design lane, not an inference lemma.

The original inference/execution parent retains every original A/B, F1/FK1,
N-Transport, complete Call, soundness, principality, termination and source/native
quantifier. Zero original premises are discharged here. The result removes a
false proposed bridge, “associated or retained source Call implies no HIR error,”
from the next step. It neither refutes the parent nor weakens ordinary inference.
No constraint generation, accumulation, propagation, levels, extrusion,
qualifying intrusion or generalization is changed or bypassed. Provider,
residual, witness and foreign-continuation obligations remain distinct.

## 1. Source and CST association

Exact source (51 UTF-8/ASCII bytes):

```text
my id x = x; my apply f = f 1; my answer = apply id
```

SHA-256: `bdf41b8059d37dea354a6b6e45a4e0a9f5a0dc412bcee40efb44a0a8bff10ba1`.
The prior run established empty structural recovery and successful return from
`lower_module_with_local_source`, then failed `hir.errors().is_empty()` before
`CandidateInference::solve`. It did not publish a CST dump or individual errors.

The source-directed projection uses these CST shapes: three direct binding
statements; plain identifier targets `id`, `apply`, `answer`; one plain
`PatternMlApplicationTail` formal for each of the first two; body chains `x`,
`f` followed by `MlArgument(OperatorChain(1))`, and `apply` followed by
`MlArgument(OperatorChain(id))`. Header pattern tails are **not** expression
`MlArgument` occurrences. The source has two expression applications and no
nested application body. This shape instantiation is a static source reading,
not a newly executed parser observation or an independently audited parser
constructor theorem. The association derivation below has that explicit CST
premise; the prior no-recovery receipt alone does not prove all node shapes.

Let `V(n)` denote the associated value for a source node and `M(l,a)` the
`HirExpr::Value { kind: MlArgument, children: [l,a], ... }` result. The exact
source-body association is:

```text
id:     V(x)
apply:  M(V(f), V(1))
answer: M(V(apply), V(id))
```

This is derived from `lib.rs::ChainParser::expression`: read the head into
`left`, consume a fixed postfix/MlArgument at the current cursor, and replace
`left` by `structural_continuation(left, tail)`. That function puts the existing
left child first, then the tail's nested children. `collect_nested_items`
associates each nested OperatorChain before its enclosing consumer. There is
no dynamic operator in this source. No type or solver choice selects the tree.

For a chain with tails `t1,...,tn`, induction on cursor steps gives
`L0=V(head)`, `Li=M(L(i-1), V(argument_i))` for unary ML tails. Thus `f x y`
associates `(f x) y`; a nested argument chain associates within its own operand
before insertion. This is a structural extension of the rule, not a claim that
this exact program contains a nested application or that every nested form is
accepted by the module lowerer. The ownership amendment retains each nested
chain only through its enclosing owned tree, not a second standalone copy.

## 2. Occurrences, ranges and lexical identity

Half-open **token** ranges below follow directly from the exact literal:

| Source role | Token range | Resolution/identity at the owning constructor |
| --- | --- | --- |
| declaration `id` | 3..5 | module value DefId, same-name ordinal 0 |
| formal `x` | 6..7 | parameter ordinal 0 of id's branded definition root |
| body `x` | 10..11 | that same parameter, not a module name |
| declaration `apply` | 16..21 | module value DefId, same-name ordinal 0 |
| formal `f` | 22..23 | parameter ordinal 0 of apply's branded definition root |
| callee `f` | 26..27 | that same formal parameter |
| argument `1` | 28..29 | integer spelling `1`; no name resolution |
| declaration `answer` | 34..40 | module value DefId, same-name ordinal 0 |
| callee `apply` | 43..48 | unique module definition apply |
| argument `id` | 49..51 | unique module definition id |

Token coordinates do not substitute for source identities. Node ranges can
include parser-owned trivia: this artifact does not invent numeric ranges for
MlArgument, BindingBody, or BindingStatement. Their exact constructors are
`range_of(node)`; associated application ranges are `span(left, tail)`; ordinary
unsupported-body diagnostics use `range_of(chain)`. The semantic token spans
26..29 and 43..51 therefore are not asserted to equal every retained node range.
No numeric `SourceNodeKey` paths or branded IDs were observed in a run here.

`module.rs::plan_root`/`plain_binding_header` and `namespace` give the three
unique value definitions. Current code admits a single plain parameter on the
ordinary route and these same headers on the opt-in route. This code observation
does not retrospectively enlarge the September 19 document's initial slice.
`lower_plan` constructs parameters from the admitted roots; `ScopeStack` and
`lower_leaf` prefer lexical parameters to the complete module namespace.

`source_identity.rs::source_keys`/`try_source_keys` retain parser-supplied node
keys. `HirSourceIdentity` maps definition roots to statement keys and parameters
to identifier-pattern origins. Keys are retained from actual nodes; equal text
or equal ranges are not enough to identify occurrences. Artifact-branded
occurrence identities are distinct from stable module DefIds and from
`LocalSourceIndex` positions. Cross-run numeric equality is not promised.

`local_source.rs::form` reuses the admitted root, parameter IDs and namespace.
Its lexical table is initialized with each formal. `Builder::expression` maps
`f` to `LocalSourceResolution::Parameter` and `apply`/`id` to their unique
`ModuleDef`s. `Builder::set` records each new occurrence against its exact node
key. Each Apply's source/range is its **tail**, whereas its callee and argument
point to distinct child indices and source occurrences. A tail's key must not
be replaced by its argument's key, nor by the whole chain's range.

For the source shapes above, the retained carrier forms are:

```text
id:     Lambda(parameter x, Name(Parameter(x)))
apply:  Lambda(parameter f, Apply(Name(Parameter(f)), Integer(1)))
answer: Apply(Name(ModuleDef(apply)), Name(ModuleDef(id)))
```

The builder processes tails in reverse to allocate the outer node first, threads
`current` through callee slots, and pushes arguments onto its LIFO worklist.
The resulting references have exactly the left nesting derived above; reverse
allocation is not right association or evaluation order. Nested argument chains
use the same worklist rule. Each formal use is a lexical source fact only: it is
not evidence of semantic callable-role registration or a solved formal Call.

## 3. Actual HIR value projection and error contract

The failed test imports `shadow::lower_module_with_local_source`, whose adapter
calls `module::lower_module_with_local_source`. That sets `local_source=true`;
it does **not** set `shadow_applications=true` or call ordinary `lower_module`.
`lower_plan` forms the carrier before lowering its ordinary-shaped value.

At the end of `local_source::form`, `SimpleBodyProjection` is an Atom only when
`direct_atom(body_chain)` succeeds (and the listed Boolean/String/If exclusions
do not apply). `direct_atom` requires exactly one child, IntegerLiteral or
IdentifierExpression. Consequently the x body projects as Atom; both application
chains project as Unsupported. `module::lower_body` converts Unsupported to
`SimpleChainLowering::Unsupported`, calls `ErrorSink::lowering` with
`HirErrorKind::UnsupportedExpression`, attachment `Value(def_id)`, chain range,
and returns `ResolvedExpr::Error` holding that causal ID. `lower_plan` wraps the
apply body's Error in its retained Lambda.

Under the stated CST premise, the exact static prediction is two lowering
errors/diagnostics in root order: first `Value(apply)`, then `Value(answer)`.
No unresolved-name error is needed for either carrier name. Ordinary unsupported
body lowering does not descend to resolve hidden operand names. ErrorSink gives
each lowering error a diagnostic; inherited syntax markers have none. This
prediction is stronger than the prior observed failure receipt but has not been
executed or independently reviewed here. It explains the failed nonempty-HIR
gate without claiming the prior run printed those two error records.

Ordinary `lower_module` also leaves `shadow_applications` false. It calls
`lower_simple_chain`, which associates the chain but requires both a direct Atom
and an empty-child associated Value. It rejects the same two applications.
Ordinary `form_ordinary` builds carrier outcomes afterward; its result does not
remove these errors. It stages identity changes and preserves previous ordinary
occurrence allocations. The opt-in route allocates carrier occurrences earlier;
its ordinal layout must not be substituted for the ordinary route's layout.

Enabling the other experimental switch is not a solution: `lower_shadow_application_plan`
retains `ResolvedExpr::Apply` but unconditionally creates UnsupportedExpression
at every retained application. `shadow_resolved_call_inventory` even requires
nonempty authentic error IDs on such Apply nodes. A changed admission policy
would therefore need a consumer audit of that inventory, not silent deletion of
errors while preserving its old assumptions.

## 4. Recovery, unsupported forms and finite resources

The September 19 recovery interpreter remains the authority for Missing, maximal
raw Error and Invalid preorder/attachment. Ordinary `lower_body` suppresses
operand resolution for recovery-bearing simple bodies and keeps their causal
errors. Its indented-block rejection occurs before the generic recovery branch;
this note does not assert that every recovered unsupported block has no lowering
error. Missing bodies, unsupported item/target/body shapes, duplicate declarations
and unresolved/ambiguous leaves retain their owning paths and diagnostics.
Direct-root unsupported chains use `DirectRootItem`, not `Value`; the exact
source here contains only binding bodies.

`local_source::form` refuses recovered roots and unsupported grammar. In the
ordinary staged route these become `SourceCarrierOutcome::Unsupported` without
changing ordinary errors. In the opt-in route `From<FormationError>` maps source
refusal to `HirAvailabilityError::StructuralProjection`. These are different
public outcomes and must not be conflated.

Concrete inspected bounds: `form` refuses root parameter count >=128 as
SupportedDepth; opt-in `lower_plan` rejects >127 parameters; shadow application
preflight requires planned height <= `128 - parameters.len()` before publishing
its occurrences/errors. Its `allow_nested` planner supports bounded special
shapes, not arbitrary recursion: leaf calls, the two-tail ML callee case, and
specified single nested arguments/groups, with comma-bearing groups rejected.
The general association rule does not prove this planner is complete.

`ShadowArtifact` raw preflight separately limits node/token depth to 128 and raw
elements to 65,536. That preflight is **not** called by every module lowerer;
these constants cannot be advertised as ordinary HIR's global resource bound.
The source builder uses an explicit worklist and checked ordinal/allocation
operations; the inspected local-source code does not establish a universal
128-level application-chain bound. Identity exhaustion, inconsistent identity,
structural projection and exact-operator-environment failure remain availability
failures. No total parser/resource/termination theorem is claimed. Any new
ordinary admission envelope must specify its own measured dimension and safe
rejection point instead of borrowing a shadow bound.

## 5. Admission decision, semantic boundary and next cut

The authoritative September 18 association and September 19 ownership rule
establish structure, not module admission. The September 19 module slice
excludes application syntax and preserves UnsupportedExpression. September 20
adds direct-root atoms without admitting complex chains. October 10 expressly
preserves ordinary admission, errors, diagnostics and occurrence identities.
October 11 preserves natural Simple-sub inference but does not silently grant
this unrelated HIR/API change. Thus no direct error-free admission theorem
follows from these authorities.

Smallest missing clause, `HIR-APP-ADMISSION-1` (owner: Luna's HIR admission design,
implementation owners `lower_body`, `lower_simple_chain`, `lower_plan`): specify
when a recovery-free structurally associated application is an admitted HIR
value rather than UnsupportedExpression, its representation and exact source
identity/operand ordering, and which errors remain for its operands. Explicitly
scope supersession of the existing unsupported-expression contract. Draft and
review permission is not adoption of this clause.

Unselected proposals: (A) ordinary resolved Apply with recursively retained
operands and source identity; (B) an explicitly specified source-backed admitted
value representation, with an honest distinction between structural admission
and later semantic rejection. Both need their own error, identity, resource and
consumer contracts. Merely ignoring `hir.errors()` or feeding the carrier to a
solver does not establish the failed gate and is not a third solution.

Mutual TODO `HIR-APP-ADMISSION-1`: Luna drafts the narrow clause using these pinned
owners; fresh reviewers check authority and source identity; only a subsequent
approved implementation packet may change code. Exact falsifier for such a
packet: the fixed source still emits UnsupportedExpression for either admitted
application, or the new representation swaps/merges callee/argument identities,
alters existing ordinary identities without an explicit approved rule, or turns
recovery/resource refusal into successful partial publication. Preserve the
zero-HIR gate as a diagnostic of the intended admission contract; do not lower
its expectation merely to reach the solver.

Mutual TODO `HIR-APP-CST-1`: before promoting the concrete literal's full
source-to-HIR correspondence, obtain the smallest authorized exact CST/source-key
receipt or a parser-constructor audit for the stated three header/body shapes,
including trivia-bearing ranges. Falsifier: either body is not the stated unary
MlArgument chain or its operand is a different source occurrence. This does not
block the authority-level obstruction: association alone never licensed admission.
No parser-constructor audit, test, probe or new dependency is authorized here.

Source constructors -> retained source forms is the bounded correspondence
above. Source forms -> generated constraints -> propagation -> consumer/native
execution is unestablished in this packet. `CandidateInference::solve` was not
reached by the prior run. Source T, SV-CONSUMER-1, Call typing, solver acceptance,
effects and production authority remain OPEN. Historical frame or hygiene proofs
are neither needed nor promoted: no local frame lemma could discharge independent
F1/FK1 obligations here. Reused evidence is solely the exact prior failure and
the listed structural/ownership authorities within their actual premises.

## Freeze, checks and resources

Six substantive stages: authority/pin reconciliation; association derivation;
carrier/identity construction; failed-gate application; recovery/resource audit;
freeze/handoff. Source reading and SHA-256 checks only; no tests, builds, probes,
Cargo, Git, code edits, descendants or scratch files. One hash-check command
initially used unavailable `python`; rerun with `python3` checked all 14 direct
pins and rev2 contract successfully. No compiler behavior was executed anew.
Conservative charge: full 480-second assignment reservation; remaining 0,
unused time retired. This is budget accounting, not measured CPU/active seconds;
actual active duration is UNKNOWN. The original pause did not reset the budget.
Three inherited UNKNOWN writer reservations remain untouched.

All authored paths: this file and
`tasks/agent-loop/inbox/20261017-accepted-call-hir-projection.md` only.
No descendants. Writing ends after the two frozen files and their hash receipt.
No independent certification by the author. Stop condition reached: exact
missing admission decision explicit. Next action belongs to Luna's granted
review/design lane; this worker does not continue while waiting.

## Frozen direct dependency manifest

- `crates/yu-hir/src/module.rs` — `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`
- `crates/yu-hir/src/lib.rs` — `5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464`
- `crates/yu-hir/src/module/local_source.rs` — `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`
- `crates/yu-hir/src/source_identity.rs` — `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2`
- `crates/yu-hir/src/shadow.rs` — `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`
- `notes/design/2026-09-18-hir-operator-association-first-slice-draft.md` — `ff113c3641f791788bea97e22b4f5dfcb91037be523e8198d3add8e6e89e17ed`
- `notes/design/2026-09-19-hir-associated-chains-ownership-amendment.md` — `e78d2d9865e35828e38c353ee77c359850d8be1884828f75aa931be2bf1556f3`
- `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` — `494a6973ced88a031688213990ea380e64cb74fea3bb1396236a8d1bb911f11a`
- `notes/design/2026-09-20-hir-direct-root-expression-slice.md` — `e2ca3943817e70de5b51bf432d696e3b3fdf90d85539e92ba429c6102691237b`
- `notes/design/2026-10-10-ordinary-hir-successor-carrier.md` — `c5fb75bdeb302a1f490398589b823f26d296d4cff3889cd0fddd5be4f801dad1`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` — `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs` — `78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963`
- `tasks/agent-loop/inbox/20261017-accepted-call-vertical.md` — `e4fa2d76284f6713fef74fb34467f9b29e5c91d3c2b9e52ee10f6874f496362a`
- `tasks/agent-loop/sprints/20261017-accepted-call-vertical-closeout.md` — `58d78ad936498e0484299d5611e81b4126ea7e24bc2a30e64ada6ab7509bdcd3`
