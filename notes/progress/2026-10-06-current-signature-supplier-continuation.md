# Current signature supplier: parameter/Application continuation

Date: 2026-10-06
Baseline supplied by primary: `ea3ae1706e318ffd2261694b17244353f0ea4c0a`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: frozen unreviewed research-only correspondence audit
Method: constructor/consumer tracing and interface-level derivation
Exclusive lease: this note only
Semantic and production implementation authority: none

## Objective and result

Determine whether the new parameter and Application crosswalks compose with
current F0–F5/SCC/generalization, annotations or direct constraints to supply
an original source-owned signature-position/contribution relation and its
exhaustive inversion. The earlier supplier map's source inventory and
`U_u/p0/a0` construction are retained as dependencies, not repeated here.

The new identity compositions are real. In addition, production has a private
parameter-recipe-to-live-row conversion and a source-caused lower Function
constraint. These suffice for structural correspondence and attribution of
the inspected constraint to its HIR occurrence. No inspected consumer turns
either route into original signature attachment or inversion. In particular,
the production parameter row is not an independently generated inferred-formal
upper demand. Its Lambda fact is a **lower Function to definition-root** fact.

This is a bounded characterization of the named current implementation paths,
not repository-wide absence, source impossibility, an accepted-source
counterexample or a new semantic decision. The residual is the existing
`Attach_C/Lic_C` source clause and exhaustive origin inversion, now located
after the available structural identities and before any solver-derived
signature association. Full profile/admission existence remains separate.

## Authority and hypotheses

Read directly: FVIEW `2026-10-05-inferred-function-call-views.md` §§1.1–5;
directional addendum §§2–4; source contracts §2, §3 opening, §6.1, §§8–10;
nested source addendum §§1–3; approved
`function-call-view-formation/q1 a2`. Current task, research startup seed,
design index and theory-map/dependency entries supply navigation/status.

The approved nested source meaning, upper-output direction, no lower backflow,
distinct source/public/internal layers, callback B and Option A/2 are fixed.
No source-profile law is inferred from old production behavior. The four
assigned source-gate records remain conditional at their recorded leaves.

Hypotheses for the correspondence are:

```text
H_id: one parse snapshot, its opt-in HIR sidecar and one retained ShadowArtifact;
      all joins pass their exact artifact/parse ownership checks.
H_prod: the current accepted unary Lambda/leaf collection route and a successful
        inference session when inspecting its admitted/finalized outputs.
H_source: the approved nested source/core and previously reviewed symbolic
          parameter/Call/seed rules, only when invoking their research results.
```

`H_prod` is an implementation-path condition, not complete successor admission.
`H_source` does not assume complete licensing, an admitted whole row or a
successful Q. Code inspection establishes the dataflow under `H_id/H_prod`;
it does not independently prove the language meanings of `H_source`.

## Exact identity conversions and consumers

Paths below are relative to the repository root; line locators refer to the
supplied baseline/current dependency snapshot.

| Route | Constructor and actual consumer | What the conversion preserves / where it stops |
| --- | --- | --- |
| Production formal to shadow formal | `crates/yu-hir/src/module.rs:1194` creates `HirParameterId(owner root,0)` and records the original admitted parameter key at `1200`; `shadow.rs:290` checks HIR ownership and parse before source lookup; `shadow.rs:107` borrows the indexed Lambda/Binder | Exact IdentifierPattern identity, HIR owner and retained lexical parameter. `parameter_at_position` mints no root/slot or typed position. |
| Call position to direct lexical callee | `shadow.rs:158` indexes existing Apply expressions by retained call-tail position; `124` validates ownership and borrows the Apply; `134` follows its callee only if already `Form::Use` | Exact Apply, Use and Binder remain distinct from HIR occurrence/parameter IDs. No conversion to a production Call occurrence or constraint exists in these APIs. |
| Collection identity to shadow identity | `crates/yu-solver/src/shadow_scc.rs:20` and `37` compose `DefinitionOrderId -> record.root -> definition_source_position -> definition_at_position` and `DefinitionUseId -> record.occurrence -> occurrence_source_position -> use_at_position` | Existing collection identities are retained when a projection is absent. Parameter reads are not top-level definition-dependency uses; these accessors do not accept `HirParameterId` or an Apply handle. |
| Root to finalized scheme | `shadow_f5.rs:22` validates the root and borrows its retained scheme; `62` maps the same owner root back to its declaration position | Structural owner attribution for endpoints/Q/R, after solving. Q/R are scheme-local identities. There is no endpoint/path-to-original-formal/Call attachment accessor. |
| Constraint cause to source | `lib.rs:395` identifies a constraint by HIR occurrence plus local slot; `419` retains that cause; `2892` records cause-to-fact provenance; `3404`/`3407` expose facts/provenance | One can recover the recorded cause occurrence and perform its existing raw-source lookup where present. The local slot is a constraint ordinal, not `Slots(beta)`; a store AdmissionReceipt is a transactional receipt, not a semantic callable receiver receipt. |

Cross-crate search for `parameter_source_position`, `parameter_at_position`,
`application_at_position` and `application_direct_use_at_position` in
`crates/**/*.rs` found the HIR definitions and their tests, with no solver/core
consumer of these new accessors. The existing solver SCC consumers use the
older declaration/use accessors. The core shadow facade is reexports only
(`crates/yu-core/src/shadow.rs:1`), not an elaborator.

This search locates current consumers; a future caller could compose the
available handles. That possibility supplies neither its source rule nor a
proof of coverage. No absence claim depends solely on identifier spelling.

## Production parameter row: the additional mechanism

The stronger current implementation route is inside `crates/yu-solver/src/lib.rs`:

```text
collect:1045
  exact HIR Lambda(parameter,body)
  -> parameter_recipes[i] = that HirParameterId
  -> LambdaRecipe(parameter_position=i, root/body components)       :1570

startup:9554
  parameter recipe i -> fresh live value row base+i
  metadata: Collected, non_generic=false, level=1

admit_lambda_fact:10576
  argument = NegativeValueRow(base+i)
  result = PositiveValueRow(base+i) if body is that exact parameter;
           otherwise the retained body value component
  argument_effect = EmptyNegative
  result_effect = retained body effect row
  Function(argument,argument_effect,result_effect,result) <: root
  cause = (original Lambda occurrence, local_slot=2)
```

`emit_lambda` checks the parameter ID against the recipe for an own-parameter
Name body (`1576–1588`). Thus the same parameter row really occupies both
value ports of the identity Lambda; it is not recovered by names or endpoint
coincidence. Integer and resolved-definition Name bodies use their own body
components. The recipe is skipped for other bodies. The production
`ResolvedExpr` enum (`crates/yu-hir/src/module.rs:426`) has no Apply variant;
this audit does not fabricate one.

The structural witness `my id x = x` exercises the smallest applicable
parameter-sharing route in the inspected test/source contracts. This is an
illustrative static dataflow witness, not a newly executed experiment or a
counterexample. It demonstrates the additional seam supplied by production:
an exact formal has a source-attributed live parameter row and a generated
Function constraint. It demonstrates no new seed/profile/slot conclusion.

The exact cause is recorded by `admit_and_record_provenance` (call site
at `10606`); normal name routing similarly creates a source occurrence
slot-zero constraint (`15087–15160`). Semantic facts store only lower/upper
terms, and cause remains a separate provenance edge. The Function term itself
contains only four term children (`crates/yu-solver/src/term.rs:170`), so a
semantic Function field address does not contain an original annotation,
slot, contribution or lexical owner. A caller may attribute the **whole
constraint** through its cause; attributing an arbitrary child as beta-owned
requires a further source correspondence rule.

For generalization, `component_generalization_draft` (`15241`) validates the
member/root, selects its live component row and invokes the existing
generalizer. `GeneralizationDraft` (`f5c_generalization.rs:505`) contains
quantifier count, recursive bounds and predicate. Function children and the
guarded cycle trace (`:453`, `:518`) retain endpoint structure and live-row
paths; the trace owner is a row ordinal. They contain no original
parameter/Apply/annotation-to-signature incidence. Preserving the owning
definition beside a finalized scheme does not add this missing association.
This statement concerns the displayed draft/observer interfaces, not an
exhaustive audit of every internal F5 algorithm.

## Annotation route and both directions

The shadow builder associates an exact grouped annotated parameter with its
retained annotation (`shadow.rs:960–980`); `ParameterAnnotationIncidence`
(`:548`) exposes BinderId/AnnotationId only. `SourceCallUseInput` (`:644`)
filters that retained association by exact callee BinderId. Its documentation
explicitly distinguishes an empty iterator from annotation absence.

Production header admission (`module.rs:1530–1578`) accepts the exact atomic
IdentifierPattern parameter shape. The grouped annotated shape has no
current production parameter recipe through that admission route. The raw
annotation inventory persists in the shadow, with correspondence pending.
Its path/position is a syntax address, not a typed signature path; neither
crosswalk supplies annotation permission, its contribution or exhaustive
annotation-to-profile correspondence.

There are two different bidirectional questions:

1. **Structural retrieval.** On present indexed objects, the parameter and
   Apply getters return the already retained objects. Given a retained
   skeleton binder/Apply position, the same index can retrieve them again.
   Collection/closed-root observers can recover the exact source owner for
   their present records. Foreign/missing/unsupported joins reject or return
   absence according to their APIs. These are partial structural joins.
2. **Semantic licensing.** Forward attachment would need to prove that a
   source exposure/contribution/position is independently beta-owned on X.
   Reverse coverage would need every original licensed incidence to recover
   a justified original formation witness on the same X. No inspected
   accessor, lower Function fact, provenance edge, draft or annotation join
   has either conclusion. Structural retrievability cannot substitute for
   either inclusion.

In particular, starting backward from a scheme Function field reaches its
scheme/root owner but no source formal/Call incidence. Starting backward
from an admitted fact reaches its recorded constraint cause, not every
original semantic signature incidence. Starting backward from a shadow
Apply reaches its lexical callee, not a semantic contribution or receiver.
These are distinct terminating paths, not three names for a completed
reverse supplier.

## Derivation and minimal remaining producer interface

Let `I` be all the present structural joins above and `P` the exact
production recipe/fact/provenance route. Their inspected conclusions have
only syntax, lexical, collection, term, row or closed-scheme sorts. Even
allowing all existing lookups to compose, `I ∪ P` provides no introduction
with conclusion `Attach_C(X,e,t)` or `Lic_C(X,t)`. The previously reviewed
symbolic source rule supplies the mandatory upper/output witness, while
policy/transport consumes licensed original incidences. Consequently the
following attempted derivation still has an open leaf:

```text
exact source formal and Call/callee identities       [I]
source exposure e, complete unsolved upper U         [H_source, prior result]
original contribution and signature attachment      [OPEN Attach_C]
independent original licensing of t                  [OPEN forward rule]
every licensed t recovers such an e/attachment       [OPEN exhaustive inversion]
```

This is interface-level nonderivation in the audited composition, not a
proof that no further source clause can be derived. It does not assume that
a generator is exhaustive merely because there is one Call.

The minimum missing **research interface**, not a selected runtime API, is:

```text
Input: original resolved source/component + binder tree/scopes;
       one whole X containing original xi=(nu,K,D), upper U,
       providers and complete source/descriptor/world obligations.

Independent judgment: Attach_C(X,e,t), t=(beta,s,p,c).
Retained witness: original formal/root, exposure, source arm,
                  original signature position and complete contribution,
                  shared scopes/dependencies (not endpoint equality).

Forward obligation: e generated and Attach_C(X,e,t) => Lic_C(X,t).
Reverse obligation: Lic_C(X,t) => some original generated e with Attach_C(X,e,t).
```

Inherited provider/result arms remain separate even when static beta or
endpoint values coincide. The existing identity seam can feed this input;
the attachment/coverage seam is absent from the inspected outputs. Finite
source lookup is decidable, but no decidability claim for this independent
judgment follows. Choosing its semantic clauses is outside this assignment;
this audit stops before adopting a new rule.

## Checks, independence, limitations and resources

Commands: bounded `rg`/`rg --files`, `cat`, `sed -n`, `head`, `sha256sum`,
output-path absence and note-local whitespace/link checks. One initial
read-only `git rev-parse HEAD` matched the supplied full SHA; no Git mutation
occurred. No tests/builds, formatter, solver/Oracle runs, checker, semantic
enumeration, scratch output or children. Existing test contracts were read,
including the four Application crosswalk tests, not rerun. An initial mistaken
`terms.rs` locator failed; `term.rs` was then located and read. Some large
initial combined captures truncated; decisive clauses were reread in bounded
windows. No conclusion rests on unobserved truncated content.

Oracle independence: no Oracle source/output supplies a premise. Current
implementation and shadow share parsing/source inputs; they are not independent
semantic oracles. The reused source rules are shared assumptions. A checker
assuming their transitions would prove consistency only. This note is producer
evidence, not independent review of this note or its dependencies.

Seeds/ranges and executed mutations: none. Logical rejected mutations are
identifying beta with a parameter/SCC/Q ID, calling constraint local_slot a
static signature slot, attributing a Function child solely through its whole
fact cause, treating a scheme root as a formal attachment, and using empty
annotation joins as absence. Each removes the required source judgment; no
runtime or accepted-source failure count is claimed.

Coverage: the current public crosswalks and named production collection,
parameter allocation, Lambda fact, provenance, SCC/root observation and
generalization interfaces. Non-absence envelope excludes exhaustive inspection
of every Rust module/callsite outside `crates`, all symbolic residual rules,
future implementations, arbitrary annotations, imports/adapters, recursion,
worlds/carriers/histories, all-view principality and production-only members.
No completion/profile/admission or production containment gate closes.
Failure conditions include missing/foreign identities, absent sidecars,
unsupported projection/production bodies, inference failure, or a changed
dependency altering the displayed interfaces. Any newly discovered actual
source attachment rule requires rechecking this bounded result.

Output budget: one leased note consumed; zero heavy processes and zero
performance samples. Numeric CPU/RAM/wall limits were not supplied. Short
shell reads used small independent batches; aggregate CPU, peak RSS and wall
time were not instrumented. Dependency freeze hashes follow; baseline blob
equality and integration status remain for the primary. Writing stops before
review submission.

Recommended next action: derive and independently review the original
`Attach_C` clause and licensing last-rule inversion, consuming the exact
formal/Call identity seam already present rather than adding another identity
crosswalk or interpreting finalized Function shape as licensing.

## Frozen direct dependencies and commit packet

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `notes/progress/2026-10-06-original-signature-source-supplier-map.md` | `9f160920a0aa43518e93ec8a139e80657a58032a69e13a7bcfd26ba6a3dd1c59` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `crates/yu-hir/src/module.rs` | `2cabe33fa9eda7130e556129be64d80409215018c7c46bf84cb5906819f8b156` |
| `crates/yu-hir/src/shadow.rs` | `9660a566968500952b8c6e7cd0dd7d6f9580c250b9ab8eaa2f2d2299de1f4155` |
| `crates/yu-solver/src/lib.rs` | `2733bb7df29dbeafc75ade2f0cc62488dd6da803f4e5815e4e0f841645fe7f27` |
| `crates/yu-solver/src/shadow_scc.rs` | `0174242bc4e5d7fac5ce99fdc47927b19babe65c43a8a1faa92d784a36d1dcb3` |
| `crates/yu-solver/src/shadow_f5.rs` | `b807ee333fb30d229a762626eb9542e5eaf518e9d2da60102f90ffc3f6710859` |
| `crates/yu-solver/src/term.rs` | `12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611` |
| `crates/yu-solver/src/f5c_generalization.rs` | `3d3aed964081996034fbb22a757c36a5da2c46c64b7f74ae51e86c14ee5bd5cd` |
| `crates/yu-core/src/shadow.rs` | `f9d44ae357b0af86db2c17b93bc56d33dd150cb460fab612876f16909f3d9f43` |

- Exact leased/changed path: `notes/progress/2026-10-06-current-signature-supplier-continuation.md`.
- Baseline SHA: `ea3ae1706e318ffd2261694b17244353f0ea4c0a`.
- Changed dependency hashes: none observed during the lane; current freeze
  hashes above. Earlier supplier-map baseline had older `module.rs/shadow.rs`
  hashes, superseded here by the assigned crosswalk baseline, not a worker edit.
- Review status: frozen unreviewed bounded characterization/interface derivation;
  no independent review, closed licensing theorem or implementation authority.
- Checks already run: governing/producer/source reads, exact public consumer
  search and constructor dataflow, forward/reverse premise audit, hashes,
  note-local whitespace/link checks. No executable semantic verification.
- Proposed one-line checkpoint message: `research: trace current signature supplier identity seams`.
- Shared-record deltas intentionally left for primary/curator: distinguish the
  present exact formal/Call joins and private parameter-row/lower-fact route
  from the missing original contribution/signature attachment and inversion.
  Preserve full-profile/complete-row/admission, principality and production
  gates as open. Shared task/theory/index/authority, compiler, manifests,
  lockfiles and question-board files were not changed.
