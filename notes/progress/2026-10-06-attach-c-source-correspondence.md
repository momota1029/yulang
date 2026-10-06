# Attach_C: source Call to candidate row/type correspondence

Date: 2026-10-06
Baseline: `cae29e238397cfa5dd490bf52d664c0f965806df`
Status: compiler-referee-reviewed research-only bounded correspondence; no findings in scope
Method: constructor/output-sort audit and conditional derivation
Exclusive lease: this note only; no implementation authority

## Objective and delta

Trace the first original attachment producer for
`my apply f = { my step x = f x; step }`, without repeating the supplier
continuation, typed contribution seam, raw-call crosswalk or pending-registration
maps. Those records already locate structural identities and the absent typed
invocation consumer. The additional inspected seam is whether the candidate
HIR synthesis or the production-backed Function reconstruction provides a
Call-to-row/type witness capable of supplying
`OriginalAssocType_X(beta,p0,j_call;s0,c0)` before query Q.

It does not in these paths. Candidate synthesis constructs symbolic Call
results and lexical scope indices. Production-backed reconstruction takes
already admitted Lambda recipe/fact endpoints and has no source Apply input.
The current raw endpoint skeleton explicitly leaves that association pending.
This is an output-sort obstruction in the inspected composition, not a source
impossibility or an accepted-source counterexample. The name OriginalAssocType
is research target notation, not an existing selected compiler API.

## Governing sections and hypotheses

Read directly: inferred call views §§1.1–5 (Authoritative direction, detailed
constructors open); source contracts §§2.2,3,10 (conditional decorated-input
conformance, no production authority); typed core §§2–3,6,9 (Draft and reviewed
conditional construction); typed boundary §6 (Draft supplied profiles and typed
transport). The original licensing construction, constructor derivation and
supplier continuation retain their own hypotheses and reviewed scopes.
The directional addendum §§2–4 retains the current user's upper-output/no-lower-
backflow decision; its proposed notation remains Draft. The nested addendum
§§1–3 fixes only this exact sequential binding and same outer capture.

Fix these hypotheses, keeping their sorts separate:

```text
H_id: one validated parse/ShadowArtifact/Skeleton and branded structural joins.
H_gen: the prior ordinary-core/Gen-Call-0 derivation at original scope;
       lexical formal d_f, shared inferred-contract root R, beta=(d_f,R),
       p0=outEff(U), and ElimOrigin for the source Call j.
H_X: one candidate whole X with original xi=(nu,K,D), providers, world,
     continuation and retained checking constraints. X need not be admitted.
H_prod: successful current admitted unary-Lambda recipe/fact path, only when
        discussing production-backed reconstruction.
H_assoc: independently interpreted original typed contribution/slot association
         on this same X; this is the missing premise, not assumed as a result.
```

A lexical BinderId, DefinitionRootId, live row ordinal and beta are different
sorts. A syntax PositionId/bookkeeping address and typed signature p0 are also
different. Neither H_id nor H_prod identifies them.

## Exact additional mechanisms and locators

| Mechanism at pinned baseline | Actual output and stopping point |
| --- | --- |
| `yu-hir/src/lib.rs:1149`, `:1186`, `:1214` | Test-only `ResearchApplicationProjection` retains occurrence and callee/argument/result endpoint strings. `research_synthesize` constructs ReifiedCall and `callN.effect/value` labels. It explicitly omits profiles, K,D and complete application constraints. No Function inequality, typed owner or association is emitted. |
| `yu-hir/src/lib.rs:1455`, `:1506`, `:1513`, `:1563` | Test-only `ResearchScopedCallEvidence` stores occurrence, lexical scope Vec, whole argument result and symbolic result. `ResearchScopedValue::Function` combines parameter with body result. This is a typed-core §6 notation skeleton, not a complete invocation relation, original slot inventory or source contribution type. It has no original xi or provider/world certificate. |
| `yu-core/src/shadow_derivation.rs:367`, `:401`, `:445` | `pending_apply_endpoint_skeleton` checks retained Apply/form identity and returns eight `(Apply ExprId, ApplyStructuralPosition)` addresses beside RawCall. Its labels explicitly assert no typed endpoint, applicability, owner, beta, xi or admission and leave OriginalAssocType pending. |
| `yu-hir/src/module.rs:426`, `:1431`, `:1457`; `yu-solver/src/lib.rs:918`, `:1045`, `:1568` | Production ResolvedExpr has Lambda/Integer/Name/Error. `lower_simple_chain` requires a childless Value atom; collection/emit_lambda handles only the displayed Integer/resolved-Name/own-parameter-Name bodies. No Apply recipe enters this production route. This is a bounded route statement, not a source rejection decision. |
| `yu-solver/src/tests/research_function_realization.rs:360`, `:371`, `:393`, `:406`; `yu-solver/src/lib.rs:10578` | `FunctionReconstruction` borrows an existing LambdaRecipe, body and construction rows/components. Its initial ports are placeholders; actual ports are recovered from admitted Function facts. `admit_lambda_fact` emits lower Function-to-definition-root with Lambda occurrence cause/local slot 2. This is not an upper formal Call demand, contribution type or original slot certificate. |

The older source joins remain the upstream references: `SourceCallUseInput`
(`shadow.rs:644`, `:1541`) retains exact immediate Use callee, argument and
same-binder annotation incidences; `CaptureUseIncidence` (`:768`) identifies
lexical capture. `PendingSourceCallRegistration` (`shadow_derivation.rs:535`)
borrows those validated references and pending rows. No newly audited mechanism
converts their references into H_assoc. Absence of a direct-use registration
for grouped/computed callees or an empty annotation iterator is not semantic
absence. `SourceViewPremiseLocator` (`shadow.rs:719–755`) separately enumerates
original profile, invocation, joint constraints, slot/typed paths, admission,
coverage and original applicability/contribution as unresolved requirements.

## Derivation and earliest missing edge

Under H_gen, the prior Gen-Call-0 establishes the original upper demand and
static immediate complete-invocation address. The semantic Call obligation is
not absent: source-call construction §5 already emits WF_Dec, VIncl,
WholeArgCompatible, the complete ExecuteCallableImage bound and
TypedCallCert_Dec on original xi. The latter retains supplied decorated
profiles/receipt/observation premises. None of the Rust candidates implements
that complete proposition or creates the upstream original association.

The inspected composition has this proof spine:

```text
retained resolved source j, callee d_f and argument d_x                 H_id
ordinary Name/Result operands; U, beta, p0 and ElimOrigin               H_gen
complete invocation operand j_call on the same candidate X            prior conditional rule
candidate structural addresses or symbolic Call-result endpoints      inspected code
original typed association (beta,p0,j_call; s,c,owner/view,xi)          OPEN H_assoc
Attach_C(X,e,(beta,s,p,c)) and independent Lic_C                        OPEN forward rule
all original beta-owned Lic_C incidences invert to source constructors OPEN inverse
```

**Bounded characterization:** for the displayed constructors, all newly
emitted outputs have structural/symbolic or existing production-term sorts;
there is no conclusion of the open association sort. The production
reconstruction is a consumer of admitted Lambda facts and cannot be moved
before source Call formation to generate that association.

**Conditional implication:** even supplying the complete invocation operand
on X leaves H_assoc open; typing an invocation at some Function or copying
its result skeleton does not establish its original beta/slot ownership.
Adding H_assoc as an independent premise would allow the candidate attachment
step to be studied, but is not a derivation of H_assoc from these outputs.
This is the exact first missing producer edge relevant to attachment. The
production path additionally lacks the earlier Apply lowering/recipe edge.
Neither finding selects a new semantic rule or requires a new runtime carrier.

## Inversion scope

Structural inversion is exhaustive only over the retained finite `Form`
variants (`shadow.rs:805`): Lambda, Bind, IntegerLiteral, Use, Group and Apply.
The exact candidate's one direct Apply yields the known upper/address witness;
Lambda capture, Use, Bind and final return preserve supplied source packets.
The generic direct-use scan (`:1522`) intentionally filters immediate Use
callees and does not justify exhaustive source Call formation.

Semantic inversion cannot conclude that these are all original beta-owned
licensing last rules. Source-contracts §3's declared source envelope additionally
has primitive/declaration alternatives, immutable field providers, operations,
reify/result, explicit one-layer elimination, recursive references and certified
whole transport. Typed-boundary §6 separately retains indexed provider/result
profile inputs, actual receipt and executing observation. These are potential
obligations for an original constructor inversion; the documents do not supply
an original beta-owned licensing conclusion for each. The exact candidate has
no operation, annotation or explicit elimination, but that fact proves only
its direct introduction inventory. It does not prove singleton Slots(beta),
exclude provider/result source arms, or close original applicability inversion.
There is no adopted list of extra licensing rules in this note.

## Checks, independence, limits and next action

Commands: bounded rg/rg --files/cat/sed reads; initial read-only status and HEAD
lookup; Python SHA-256 and pinned-byte comparison via `git show baseline:path`
for the 21 direct dependencies below. All matched. Large aggregate captures
sometimes truncated; decisive output fields and clauses were reread in bounded
windows. Note-local whitespace and hash-table checks were run before freeze.
No tests/builds, checker, solver or Oracle run, formatting, scratch outputs,
Git mutation, child delegation or source edit. Read historical test assertions
are not newly executed checks.

Oracle independence: no Oracle data supplies any premise. Structural core and
candidate synthesis share source inputs and selected source assumptions; they
are not independent semantic oracles. A checker assuming the association or
transition rules would only test those assumptions. This producer note does
not independently review itself or the reused constructions.

Seeds/ranges/executed mutations: none. Logical shortcuts fail at named premises:
using equal endpoints loses original contribution/slot identity; treating a
recipe row as beta conflates definition/formal roots; using the lower Function
fact for upper protection violates the selected direction; removing source
indices loses provider/result-arm inversion; using admitted fact recovery as
formation violates the pre-query source premise. No accepted-source witness or
semantic failure count is claimed.

Coverage is the exact source pipeline and the named candidate/production-backed
interfaces. Arbitrary annotations/callees/recursive components, all Rust
consumers, complete original profiles, initial/history admission, source
adequacy, principality, production Option A/2 inclusions and cutover remain
unverified. Missing/foreign identities, unsupported projection/production
bodies, failed inference, or changed constructor inputs invalidate the
corresponding structural path. A newly found independent source association
producer would require rechecking the negative characterization.

Resource use: short lightweight read/hash processes, zero heavyweight processes,
zero performance samples, one leased output. No numeric CPU/RAM/wall-time limit
was supplied; aggregate CPU, peak RSS and elapsed wall time were not measured.
No unbounded search was attempted.

Recommended next action: supply a source-owned typing introduction for
OriginalAssocType on the constructed complete invocation operand, retaining
beta, original p, source j, slot s, contribution c, typed owner/view and the same
xi; then invert its original licensing constructors. Another structural label
or admitted-Lambda reconstruction leaves this same premise untouched.

## Frozen direct dependencies

All bytes matched the pinned baseline; hashes do not confer authority/review.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |
| `notes/progress/2026-10-06-current-signature-supplier-continuation.md` | `1e42cf9be0576c12a057e9675d4c8c7bb9f5eac2538d5c62b1b9413593bcddc1` |
| `notes/progress/2026-10-06-current-attach-contribution-seam-audit.md` | `3e96fae0e04989596313c69329d063ddb4649e5c749590f6872d11f6d61b1851` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-raw-call-source-input-crosswalk.md` | `860e2b7816c359de6d24bfc06d29cb1ce70a6b27420dc2edbdce673d722e5ef4` |
| `notes/progress/2026-10-06-pending-source-call-registration.md` | `053608a5b32bd7e14449e3977381e52f408a34cf2221841095543923b2b3ddf2` |
| `notes/progress/2026-10-06-shadow-apply-endpoint-skeleton.md` | `4b138f6549f640abc91e4eb9219e3ea3563117ddf30b3f3b7694b6199f651afa` |
| `crates/yu-hir/src/shadow.rs` | `4b0914f3a29a5ca47fd912de23ebad690d57908ad628e5dc392b0d8b6df811ac` |
| `crates/yu-hir/src/module.rs` | `2cabe33fa9eda7130e556129be64d80409215018c7c46bf84cb5906819f8b156` |
| `crates/yu-hir/src/lib.rs` | `ce6fcff5d87a89d7185c0c748a5e0a9482e489f2c21a5548da8b72041dd65727` |
| `crates/yu-core/src/shadow_derivation.rs` | `1b46089cb0e3d8090cb2b0227b578b0eee926b224bd42e88d78b7b229d044342` |
| `crates/yu-solver/src/lib.rs` | `3c6fee29904859ed30957469a60aac71a4f6236de0155f2a22a597dcd81e2910` |
| `crates/yu-solver/src/term.rs` | `12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611` |
| `crates/yu-solver/src/tests/research_function_realization.rs` | `cd2bc00e91259c0c133900bf88912a0e43892c5bed60137fe7fa258357d9022c` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-attach-c-source-correspondence.md`.
- Baseline SHA: `cae29e238397cfa5dd490bf52d664c0f965806df`.
- Changed dependency hashes: none; all 21 direct dependencies match baseline.
- Review status: frozen unreviewed bounded correspondence and conditional
  derivation; no independent review, theorem closure or implementation authority.
- Checks already run: constructor/output-sort and original-scope audit,
  governing-section reads, 21 hash/pinned-byte comparisons and note-local checks.
  No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: locate typed association gap after candidate Call skeletons`.
- Shared-record deltas intentionally left to primary/curator: record that
  symbolic Call-result candidates and admitted-Lambda reconstruction do not
  supply the original typed association. Preserve the existing open Attach_C/
  Lic_C inversion, same-X/profile/admission and production gates. No task,
  theory, index, authority, manifest/lockfile or question-board file changed.

Writing stopped before frozen review submission; the primary owns integration.
Review: `compiler_referee` PASS on the frozen content SHA-256
`3b577f9e8430bb32f21a41fdaead713bc692098ac88ff60e4e3b59b214e2c70e`.
The review covered the bounded HIR/core/solver output-sort comparison and
current-source limitations; it did not independently validate every pin via
Git blob equality or review full source adequacy/production conformance.
