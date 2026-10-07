# Original association: current nested-call producer ordering

Date: 2026-10-07
Baseline: `4a9d969db09be881bdc0ce6888cc3d651dfc2405`
Status: research-only characterization; regression-auditor reviewed after one minor repair; no further findings
Lease: this note only
Method: source/implementation correspondence and a bounded structural derivation
Implementation authority: none

## Objective and governing premises

Trace the producer and retention chain for exactly:

```text
my apply f = { my step x = f x; step }
```

Determine whether an actual source-owned original association
`OriginalAssocType_X(beta,p0,j_call;s,c)` is constructed before the pending
Function comparison. This is not an Oracle search or another crosswalk of the
eight Apply labels. The previous shadow correspondence audit and current local
application tests supply the already retained identity joins; this note adds
the ordering and semantic-collection separation at the current baseline.

Governing sources are inferred Function call views §§1.1–5, source contracts
§§2.1–3 and 10, and typed computation core §§6 and 9. The exact-source authority
is `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md`
§§1–3. The assignment's possible
`notes/design/2026-10-07-nested-call-source-boundary.md` is absent at this
baseline; the design index locates the existing approved addendum.

Accepted meaning is fixed: sequential local binding, final return of the
`step` value, outer `f` capture, distinct local `x`, and the ordinary call in
the local body. Preserve callback B, actual callable role/entry, the source
annotation/public scheme/internal-view distinction, and the selected upper
output protection direction. No generic brace meaning, local polymorphism or
new receiver rule is inferred here.

The authorities have different claim classes. The nested source meaning and
Function-view formation direction are Authoritative. Source contracts provide
conditional results whose independent kernel/local typing inputs remain
required. Typed core is Draft and supplies the cited structural construction
relative to lexical/declaration and complete-call premises. This audit adopts
no additional source semantics and closes no semantic gate.

## Bounded claim and explicit hypotheses

The inspected exact-source path retains structural coordinates before solve,
but constructs no original association at that stage or during solving. In
particular, its local initializer is traversed for pending applications and
never submitted to semantic collection. Solving preserves that pending row.
The Core structural views are separately called consumers of the source
artifact; they are not an upstream typed producer feeding this solver path.

This claim assumes:

1. The pinned constructors/consumers in the dependency manifest, without
   out-of-band modification, plugins or alternate caller-supplied semantics.
2. One parse artifact, successful exact topology validation and its compatible
   HIR identity sidecar; foreign/missing identities do not count as a join.
3. The exact opt-in `lower_module_with_shadow_local_binding` route, followed
   by `ConstraintBatch::collect` and `SolvedModule::solve` with the
   `yu-solver/shadow-f5` feature enabled. Ordinary lowering is compared only
   at its existing Error/body/diagnostic boundary.
4. Existing test bodies are inspected as contracts, not reported as newly
   executed results. No compiler execution was authorized for this lane.

This is a bounded code characterization, not a repository-wide semantic
absence theorem, a theorem that the existing original fiber is empty, an
admitted-source counterexample, or proof that source adequacy is impossible.

## Producer and consumer chronology

| Stage | Producer/consumer and current effect | Association consequence |
| --- | --- | --- |
| Parse | `yu-syntax/src/full_parse.rs:317` checks source/header allocation correspondence, creates the ordinary CST and fresh parse identity. `statement.rs:562` constructs a `BracedStatementBlockExpression` through the ordinary statement sequence. | Syntax ownership and occurrence identity only; no typed owner/view kernel. |
| Shadow source projection | `yu-hir/src/shadow.rs:433` retains the parsed root, rejects syntax diagnostics, and invokes `build_skeleton`. Its nested branch at `:1426` invokes `project_selected_nested` (`:2155`). The local initializer is projected while only `f,x` are in scope; `step` is then installed before projecting its returned use (`:2287`). | Constructs the approved lexical topology and capture incidence. Closure correspondence remains `PendingTypedCaptureProviderReceiverAndSemanticDischarge`; Apply construction adds pending categories (`:2130`). |
| Ordinary HIR plus captured source | `shadow.rs:37` first calls identity-retaining ordinary lowering. It validates the source root/formal against the captured topology, then stores the source artifact. | The ordinary item remains an outer Lambda whose block body is Error. Attaching the source artifact is not typing that Error or the inner application. |
| Cold local sidecar | `shadow.rs:92` calls `module.rs:2235`. The latter requires the ordinary Error body, builds exact HIR names resolving to the outer/local formals, local Lambda and Apply, stores `ShadowLocalBind`, and publishes source identity metadata. `module.rs:2428` installs the sidecar without replacing the ordinary body. | Binding/capture/use identities exist; no `Value/Computation` tags, typed receipt, complete invocation, profile or association witness is added. |
| Core structural consumption | `yu-core/src/shadow_derivation.rs:20` builds the exact-candidate `IncompleteDerivation` separately; Apply becomes `Node::PendingCall`. `:357` and `:198` separately build raw and pending structural views. | These consumers borrow source structure and pending premises. Their names `Result`, `Bind` and `PendingCall` are not judgments proving semantic membership. No connection submits their nodes to `ConstraintBatch`. |
| Collection: root scan | `yu-solver/src/lib.rs:1047` traverses the ordinary root for retained applications before ordinary fact emission. The outer Lambda's Error body contributes no Apply. | No comparison or source-association production on this scan. |
| Collection: local initializer | `lib.rs:1093` finds the sidecar and calls `retain_pending_applications` on its initializer (`:1102`). The traversal (`:1308`) borrows Lambda/Apply/operand occurrences and records `ApplicationTypingRuleUnresolved`; it does not feed operands to semantic collection. | One pending inner Apply exists before constraints are admitted. It has no typed invocation judgment and no `DefinitionUseId`. |
| Collection: semantic recipe | Immediately afterward, collection registers outer `f` in `parameter_recipes`, then calls `emit_lambda` with the unchanged ordinary Error body (`:1105`). `emit_lambda` (`:1667`) accepts only its selected Name/Integer cases and returns from the fallback before emitting a Lambda recipe. | Local `x`/`step` never enter these semantic recipes. For this exact input: no collected occurrence facts, no Lambda recipes, no definition-use dependencies; the root remains an Error body status. |
| Solve | `InferenceSession::run` (`:9897`) admits collected facts, executes the existing SCC plan, accounts and finishes. Admission (`:10613`) iterates occurrence facts and Lambda recipes, not pending applications. SCC execution (`:13139`) consumes existing definition-use and member inventories, not the local sidecar. | Nothing converts the retained inner Apply to an application fact or complete Function query. Scheme finalization does not supply a typed source association. |
| Publication/observation | Finish (`:15862`) moves the pending rows and same HIR Arc to `SolvedModule`. Its accessor (`:15893`) returns the unchanged unresolved rows. `shadow_f5.rs:67,96` only enumerate their direct Name references or borrow the retained source. | The already retained source/core/HIR joins remain inspectable after solve. A finalized current scheme and its Q/R binders are not original `beta/Slots` or the pending semantic comparison `Q`. |

The inspected existing local test
`crates/yu-solver/tests/shadow_legacy_local_application_provenance.rs` joins
the exact source and sidecar to Core and solver rows, while preserving ordinary
HIR diagnostics and the Error body. The existing unit test
`shadow_local_bind_retains_only_one_unresolved_application`
(`lib.rs:16511–16704`) separately asserts empty occurrences, empty Lambda
recipes, one outer parameter recipe, empty definition uses and unchanged
pending state after solve. These assertions are corroborating static evidence;
they were not executed in this assignment. The earlier Apply endpoint
crosswalk is used as a dependency and is not reconstructed here.

## Structural derivation: the semantic input cut

Let `H` be the ordinary HIR with its outer Lambda/Error body. Let `H+L` be the
same ordinary item tree plus the validated local source sidecar. This notation
does not equate all metadata, allocation or counters.

For this exact input, collection's ordinary tree scan sees Lambda then Error,
so it emits no pending application. The sidecar scan sees local Lambda then
Apply and pushes one structural row. After that scan, `emit_lambda` still
receives the Error body of `H`, so its fallback exits before adding facts or a
recipe. The resolved-definition Name branches likewise do not match. Thus:

```text
semantic occurrence facts(H+L) = semantic occurrence facts(H) = empty
Lambda recipes(H+L)            = Lambda recipes(H)            = empty
definition-use dependencies(H+L) = dependencies(H)            = empty
pending inner Apply(H+L)       = one unresolved structural row
```

These equalities are derived from the inspected branch conditions, not from
solver success. The outer root/parameter bookkeeping remains present and can
be finalized by the ordinary current solver. The trace establishes that its
scheme is derived through the ordinary Error-body path; it does not establish
what source type should have been inferred for the approved nested function.

Admission and SCC processing never read the pending row to form a typed Call.
Finish only moves it. Consequently this chain cannot furnish a newly produced
source-owned original association by treating retention-before-admission as
formation-before-`Q`. On this path no complete source Function comparison for
the inner call is emitted at all. That is the discriminating ordering fact;
the pending row's existence is not a semantic pre-query certificate.

The displayed 38-byte no-LF source is the exact approved scope witness. It is
not minimized to another source, because that would change the assigned
source boundary. No shortest counterexample or semantic failure is claimed.

## Separate helpers and precise remaining source clause

A scoped Rust search found `OriginalAssocType_X` only in a Core documentation
disclaimer, not an executable constructor. Inspection, rather than that name
search alone, excludes the plausible separate helpers:

- `shadow_directional_protection.rs:66` consumes caller-assumed source upper,
  output and seed witnesses. `AssumedOriginalContext` takes `beta,scope,xi`
  from the caller. Its conclusion remains `ConditionalStatus::Assumed`.
- `shadow_typed_evidence.rs:26` validates and queries supplied ports, profiles,
  Flow, observations and receipts; it does not generate them from this source.
- The scoped call-site search for those constructor APIs found test uses,
  not a production caller inserting their results into collection. The
  source/Core projection APIs similarly appear in the inspected tests as
  separately requested structural observations.
- `shadow_scc.rs:21` requires an existing SCC dependency occurrence before
  borrowing a pending use-instantiation view. Here the local callee is a
  Parameter and produces no such collected occurrence. Reclassifying it as a
  definition dependency would alter the input, not expose a hidden producer.

The missing clause is an independent source/owner/view introduction at the
existing original signature incidence. It must produce an actual witness
`(t,w)` in the already interpreted `I_orig(X)`, with `t=(beta,s,p,c)`, original
typed `p=p0`, original receiver/use/scope ownership, and `w` typing `c` over the
complete receiver-invocation family. The query is the existing fiber in
`2026-10-07-successor-source-association-falsification.md` §4; no new relation
is defined here. It must retain provider/result arms and one original
`xi=(nu,K,D)` before pending comparison, and account for legitimate original
incidences rather than select a singleton by ID convention.

Even granting independent complete Call typing does not introduce that
owner/view/signature witness. Inferred Function views §2 requires its source
direction and §5 explicitly leaves its generation judgments open. Source
contracts §2.1 takes independently typed owner/view kernels as input, §2.2
requires active joint interpretation, and §3.5 assumes the local typing and
emission certificate. Typed core §§6,9 supplies a complete-call skeleton
relative to its interfaces and constraints; it supplies neither this original
signature membership head nor its original licensing. The seven pending
source-view categories expose that prerequisite; they are not its proof.

This is a precise missing source clause and implementation correspondence cut,
not a proposal to replace current carriers or language meaning. Adding another
address label, enlarging a toy model that assumes the clause, or observing a
successful solved Function would leave this same premise untouched.

## Checks, independence, coverage and resources

Checks run: read-only `cat`, bounded `sed`, scoped `rg`, `git rev-parse HEAD`,
`git status --short`, scoped `git diff --name-only <baseline> -- <paths>`, and
Python SHA-256 plus byte equality against `git show <baseline>:<path>`.
All 19 direct dependency comparisons were PINNED; no dependency hashes changed.
The initially absent lease target was checked before writing. Some exploratory
searches used nonexistent `lower.rs`/parser directory guesses and returned
errors; corrected searches located `module.rs`, `full_parse.rs` and
`statement.rs`. No conclusion relies on those failed search scopes.

No tests, builds, compiler execution, formatting, benchmarks, Git mutation or
child agents ran. No Frozen Oracle source or executable was consulted. The
existing fixture contains historical Oracle comments; their IDs/spans were not
used as semantic evidence. Source/Core/HIR tests share parser and identity
machinery, so they are not independent semantic oracles. No transition checker
was built; code branch analysis proves only this code-path characterization.

Seeds/ranges/enumeration and executed mutations: none. Inspected failure
conditions include syntax diagnostics, foreign parse/HIR brands, missing
source joins, wrong topology, non-Error ordinary body, unsupported Core source
and supplied assumption category/context mismatches. They remain structural
rejections, not a production source acceptance theorem. The one selected
fixture is the complete coverage envelope of this derivation. Other braces,
annotations, generalized/recursive sources, grouped/computed callees, operations,
handlers, imports, worlds, production-only Option 2 extras and full licensing
inversion were not audited.

Resource usage: small read-only shell/Python inspection commands; no heavyweight
processes, zero Cargo processes and no generated scratch outputs. Aggregate CPU,
peak RSS and wall time were not instrumented. Output is this note only. A change
to the named producer/consumer dependencies invalidates affected deductions;
unrelated branch movement does not certify or invalidate semantics by itself.

Recommended next action: construct and independently review the missing
source-owned original owner/view/signature introduction for this exact retained
Call, explicitly conditional on any still-open complete typing/admission
premises. Keep production implementation and ORIGINAL_ASSOC closure gated.

## Pinned direct dependencies

All hashes are SHA-256 and matched the baseline blobs before writing.

| Path | Hash |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-08-original-association-shadow-correspondence-audit.md` | `91a327aa28cf36f7ec8885fe5e3efde1be74a3bc25ed5fe32f3410c0b29d260e` |
| `notes/progress/2026-10-08-call-type-shadow-correspondence-audit.md` | `de4b87744a9e791c2483c9fdd7f1f38354d17f223f71500f2196800764f7f172` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/statement.rs` | `dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d` |
| `crates/yu-hir/src/shadow.rs` | `cc0ab762e6717d8f1689c460c4f9d38c471aed049f1a3b25243c2deceefeb50f` |
| `crates/yu-hir/src/module.rs` | `50d0f1040a29f66c7b2640f2e4ce7fe9ed4def58daaf41e6cc3c3b5e8fab8e4a` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-core/src/shadow_directional_protection.rs` | `9bb4fa098d275874dc0349b115dcc9031648b788fedefd1466af60889e460493` |
| `crates/yu-core/src/shadow_typed_evidence.rs` | `dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95` |
| `crates/yu-solver/src/lib.rs` | `1513dc92db0e29fd8258fc5521637d91a603dd72a3e8af1fb1d11fef8121dcd7` |
| `crates/yu-solver/src/shadow_f5.rs` | `61d530aacbc3a58b7d532157d8ec090d9025705248c4b6666352bbf6fd4835c3` |
| `crates/yu-solver/src/shadow_scc.rs` | `ba5d3a98c3e9723cd131fe347602cf2e11df543aa8ad3f70bcb552f4fb2c2648` |
| `crates/yu-solver/tests/shadow_legacy_local_application_provenance.rs` | `91452cb80f3cd51a9317779825973e4e077d6c0ccce50eac03d211022ec1eb42` |
| `crates/yu-solver/tests/shadow_f5_differential.rs` | `6f12b94f86919dc2f7e22188d911399086df04fcc2f6c2197ef09329e376d8e7` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-07-original-association-current-producer-crosswalk-round1.md`.
- Baseline SHA: `4a9d969db09be881bdc0ce6888cc3d651dfc2405`.
- Dependency hashes changed: none; all 19 manifest files matched that baseline.
- Claim/review: bounded producer-order characterization; regression-auditor
  review found one missing feature premise, now fixed with no further findings.
  No semantic closure claimed.
- Checks already run: narrow source/call-site inspection, existing test-body
  inspection, baseline byte/hash comparisons and lease/diff scope checks.
  No tests/builds or semantic experiments run.
- Proposed checkpoint message: `research: trace nested-call producer ordering before comparison`.
- Shared-record deltas intentionally left to primary/curator: optionally link
  this chronology and record that retention precedes admission while the local
  initializer never feeds semantic collection. No authority/status promotion,
  new DAG edge, compiler edit or question-board change is proposed. Keep the
  original owner/view/signature introduction and ORIGINAL_ASSOC open.
