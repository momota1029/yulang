# Frozen Oracle: unannotated ordinary-argument producer boundary

Date: 2026-10-06
Status: frozen research-only historical characterization; independent review pending
Yulang3 baseline: `4b1f6b8d104e639353c7001d7333300e628defa3`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, dependencies, and result

Trace the source producer nearest the first missing clause of
[main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§5: one unannotated formal/use, one ordinary-value argument, and the same
shared formal endpoint. The method is static data/control-flow archaeology
and a local field-dependency derivation. The already traced frame selector,
call-upper inventory, generalization and annotation marker pipeline are inputs,
not repeated research attacks.

Governing current authority is
[inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, especially §3, and the
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. The protected internal Handler seed and ordinary-value refinement on
one shared inferred relation are selected. Actual provider role/entry remains
distinct. This note neither reselects those meanings nor uses historical code
as authority.

**Result:** the historical ordinary name contributes a shared value endpoint
and a locally constrained effect endpoint to an application Function demand.
The inspected producer does not inspect that argument's `Evaluation` tag or
`effect_view`, and its unannotated return-effect helper does not receive the
argument at all. Its next analysis edge submits the Function demand directly
to the constraint machine, which can drain immediately. No additional explicit
source-level Handler-to-non-Handler refinement was found on this bounded
path. This does not exclude refinement encoded through effect constraints or
later solver behavior. The investigation stops at that exact solver boundary.

Existing source archaeology, annotation/call archaeology, argument-effect
channel, multi-use frame continuation, and main Oracle crosswalk are historical
inputs. Their selected distinctions are retained: unannotated live-root/frame
machinery differs from the annotation-dependent call-upper/sidecar machinery.
None supplies current `U_c`, `Delta_formal`, typed footprint, or independent
admission.

## Hypotheses and claim classes

H1: the eleven directly inspected historical files equal the exact Oracle
commit blobs byte-for-byte; verified below. Nine current dependencies equal
the pinned Yulang3 blobs.

H2: ordinary defined-parameter lowering is reached with unannotated variable
patterns, no supplied parameter upper for these formals, and successful name
and ordinary application lowering. Fresh pattern locals initially have no
Scheme. This is a lowerer-state premise, not a new source-acceptance result.
For the nested candidate `my apply f = { my step x = f x; step }`, the
previously characterized structural route is retained conditionally; its
execution stack was not instrumented here.

H3: comparing two calls to the same producer begins with equivalent lowerer
states and equal expression/value/effect IDs and source ranges. Only the
argument's evaluation field differs; both calls complete normally. No external
observer is assumed to read an unpassed `Computation` field.

**Established provenance/representation facts:** H1 and the explicit field
reads/assignments at the cited revision. **Bounded characterization:** the
historical path below. **Conditional local derivation:** field erasure under
H3, not a language or source-rule theorem. No reviewed theorem, complete
historical absence result, current semantic closure or production permission
is claimed. H2/H3 are candidate analysis premises, not established accepted
program coverage.

## Actual source data/control flow

All following paths are relative to the frozen Oracle tree.

1. **Annotation absence produces argument metadata.**
   `crates/infer/src/lowering/expr/lambda.rs:1252–1264` returns
   `arg_eff=skeleton_arg_eff=never_neg()`, `local_effect=None`, no argument
   contract, empty output/call predicates, no public/erased call uppers,
   disabled projection, and `LocalCallReturnEffect::Unannotated`.
   `never_neg` allocates `Neg::Bot`
   (`crates/infer/src/lowering/expr/constraints.rs:31–33`). These historical
   fields are not an established encoding of the current protected Handler
   seed. A supplied parameter upper can separately change the historical
   annotation classification (`lambda.rs:690–696`); H2 excludes that input.

2. **The formal and its use share the live endpoint.**
   Defined-parameter lowering allocates `param_value` and installs the pattern
   with its annotation-local effect (`lambda.rs:664–722`). Pattern-local
   installation records `Def::Arg`, that value, the supplied optional effect,
   and `scheme=None` (`crates/infer/src/lowering/pattern.rs:236–281`).
   `instantiate_local_value` returns `local.value` when no Scheme exists
   (`crates/infer/src/lowering/expr/tail.rs:855–859`).
   `lower_local_name` resolves its fresh reference to this same definition
   and emits `Computation::value` (`crates/infer/src/lowering/name_ref.rs:146–173`).
   This is the established old-side identity prefix, not the missing current
   joint relation.

3. **The ordinary argument carries an effect constraint, independently of its
   evaluation tag.** With `local_effect=None`, name lowering calls
   `fresh_exact_pure_effect` (`name_ref.rs:176–187`). That helper allocates
   `epsilon_x` and submits

   ```text
   Pos::Bot <: Neg::Var(epsilon_x)
   Pos::Var(epsilon_x) <: Neg::Row([], Neg::Top).
   ```

   Exact assignments are at `lowering/expr/constraints.rs:7–28`. This note
   characterizes the emitted constraints, not their full denotation or solver
   correctness. `Computation::value` sets `Evaluation::Value`
   (`crates/infer/src/typing.rs:42–48`). The same file explicitly separates
   evaluation/value restriction from effect contents (`:14–24,59–72`). Its
   `Value` is not current callable role or actual parameter-entry evidence.

4. **Application lowering independently lowers the argument.**
   Ordinary Apply syntax routes through `apply_arguments`
   (`tail.rs:14–17,89–126`). It calls `lower_expr(&arg)` before
   `make_source_app` (`:116–123`); no expected Function port is passed into that
   argument-lowering call. The constructor-payload exception at `:129–155`
   changes the argument-node inventory for a known constructor. H2 concerns
   a formal rather than that constructor path.

5. **The argument's value/effect enter the demand; its evaluation field does
   not choose a formal refinement.** `make_source_app` passes the two
   computations to `make_app_with_origin` and records source spans
   (`tail.rs:630–686`). `make_app_with_origins`, read in full at `:535–628`,
   reads `arg.value`, `arg.effect`, and `arg.expr`, not `arg.evaluation` or
   `arg.effect_view`. It creates the negative four-port Function

   ```text
   demand = Neg::Fun(arg=Pos::Var(A_x),
                    arg_eff=Pos::Var(epsilon_x),
                    ret_eff=selected_return_upper,
                    ret=Neg::Var(result_value))
   Pos::Var(A_f) <: demand.
   ```

   The first constraint is submitted at `:560–563`. The already characterized
   unannotated helper is called as
   `unannotated_local_callee_return_effect(&callee, call_effect)` (`:552`).
   Its complete signature/body (`:740–798`) uses callee definition/annotation/
   frame state and return-effect state; it has no argument input. Therefore
   it cannot itself test this ordinary argument's evaluation tag or value
   evidence. This narrow dependency fact adds no new frame-selector result.

6. **Exact analysis stop.** `crates/infer/src/arena.rs:90–93` delegates
   `subtype` to the constraints machine. Its entry at
   `crates/infer/src/constraints/machine/entry.rs:493–499` enqueues a root
   subtype with empty weights and calls `drain` when work exists. Constraint
   submission is thus not necessarily deferred until after source lowering.
   No solver transfer rule, completed bounds, generalized output or printed
   scheme is inspected as evidence for the missing current source predicate.

There are two tempting name collisions. `LocalDefRole::{Value,Input}`
(`crates/infer/src/uses.rs:88–91`) is the formal-use classification written by
`mark_lambda_param_as_input` (`lambda.rs:887–894`), not a shown Handler/Pure
refinement. `RolePredicate` carries a named role path, ordinary inputs and
associated types (`crates/poly/src/types.rs:35–52`), not evidence of current
callable-role coordinates. The historical `Pos::Fun`/`Neg::Fun` structures
have four ports and no explicit callable-role field (`types.rs:740–750,781–791`).
None of those local field facts proves that all historical role behavior is
absent elsewhere.

## Smallest discriminating local witness

Take two supplied argument computations with identical expression/value/effect
and effect-view fields, differing only here:

```text
arg_V.evaluation = Evaluation::Value
arg_C.evaluation = Evaluation::Computation.
```

Under H3, `make_source_app` and `make_app_with_origins` read identical inputs at
all decisions and pass identical inputs to their helpers. They allocate and
submit the same demand, source provenance and result connections, up to
uniform fresh-ID renaming. Their result is `Computation::computation` in both
cases (`tail.rs:615–627`). Solver calls also receive the same submitted IDs
and equivalent pre-call state. This is a direct field-dependency derivation;
no executable checker or compiler experiment was run.

The witness rules out only the proposed explanation that **this application's
explicit evaluation-tag branch** performs the historical formal-role
refinement. It does not compare two accepted source programs, and it is not a
counterexample to the approved ordinary-value refinement. Changing the argument
source can change its effect bounds, expression and shared lowerer state; the
witness holds those fixed. Historical behavior could instead depend on those
bounds/stack interactions. Deriving that behavior would require a separately
assigned solver-correspondence investigation.

## Correspondence boundary and recommended next action

The concrete mechanism found is source argument → effect/value demand → shared
formal constraint → immediate solver analysis. It resembles a place to emit
current `Delta_formal`; it does not define its whole-tuple interpretation
`U_c(xi; seed,refined,argument,invocation)`. In particular, annotation absence
metadata, exact-pure effect constraints, and Empty push/pop weights do not
identify current protection, non-Handler refinement, typed contribution
footprint, complete profile/receipt schema or Q-independent admission.

The precise blocker is the unproved interpretation relating this old-side
effect/stack demand to the selected seed/refinement on the current single
joint `(nu,K,D)`. Repeating frame selection or enlarging a stipulated-transition
probe would leave it untouched. Recommended next action: derive the current
minimal-clause §5 predicate directly with explicit source-owned evidence and
joint coordinates; retain this historical trace only as a bounded mechanism
crosswalk. If further historical investigation is chosen, its new question is
specifically whether the already-submitted empty-argument effect and weighted
return demand induce a distinguishable solver transformation, with no
assumption that such transformation equals current Handler semantics.

## Independence, commands, coverage, and resource limits

Frozen source is independent of current toy transition checkers, but is not
an independent semantics oracle. Its producer and solver belong to the same
implementation; a source-built executable would share those assumptions.
Blob checks establish provenance only. No claim is inferred from printed
schemes or accepted programs, and the producer does not independently review
this artifact.

Checks: read-only `git rev-parse HEAD`; bounded `rg -n`, `sed -n` source windows;
Python/subprocess byte equality against `git show <SHA>:<path>` and SHA-256;
current dependency equality at the pinned Yulang3 commit. Seven sequential
frozen-source read/search captures and one combined blob-validation capture
were used. An exploratory search named nonexistent `lowering.rs` and returned
exit 1; it was corrected to the actual `lowering/expr/constraints.rs` file.
Some initial combined context captures were truncated, and several exploratory
locator searches were capped with `head`; omitted matches are not absence
proofs. Decisive producer/metadata/entry windows were recovered without
truncation. No whole-repository absence claim is made.

Local cap communicated to the primary: one sequential lightweight source
process, at most twelve frozen-source captures, approximately twenty-minute
wall cap. No heavyweight process, build, test, Oracle execution, formatter,
Git mutation, additional output path, seed, randomized range, executed mutation
or performance sample was used. CPU, peak RSS and full wall duration were not
instrumented. The two-value witness is an analytical field mutation only.
Unrelated current compiler edits were observed and preserved.

Unverified: surface acceptance and actual runtime lowering stack; all other
expression/parameter paths; solver decomposition, subtraction and normalization;
annotation marker transport beyond existing characterizations; arbitrary aliases,
methods and recursion; current original relation/profile/admission; soundness,
principality, source adequacy, and production conformance. Changed blobs,
different lowering routes, external instrumentation reading unpassed fields,
or failed calls invalidate the relevant local hypotheses.

## Frozen historical source hashes

Every listed file matched its exact commit blob; SHA-256:

| Path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `crates/infer/src/lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| `crates/infer/src/typing.rs` | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |
| `crates/infer/src/uses.rs` | `e3492318c6cb788097b350f1cd692023ffa7454b8a7c2f8fc448a0293520fdf3` |
| `crates/infer/src/arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Current dependency hashes equal their pinned baseline blobs. The nine checked
paths are the two governing designs, main minimal-clause note, initial source
archaeology, annotation/call archaeology, argument-effect channel, multi-use
frame continuation, main Oracle crosswalk, and `tasks/current.md`. Their
content hashes did not change relative to this assignment baseline.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-missing-source-producer-continuation.md`.
- Baseline SHA: Yulang3 `4b1f6b8d104e639353c7001d7333300e628defa3`;
  frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; eleven historical files and nine current
  dependencies matched their pinned blobs.
- Review status: frozen, research-only bounded characterization and conditional
  field-dependency derivation; independent review pending. Writes stop before
  submission. No current theorem or production authority.
- Checks already run: revision reads, seven bounded source read/search captures,
  source/current blob equality, SHA-256 checks, narrow artifact/path inspection.
  No executable, build, test, formatting, or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: localize Oracle unannotated call producer at solver boundary`.
- Shared-record deltas left for primary/curator: record the value/effect input
  route, evaluation-tag erasure at this call producer, and immediate solver
  stop; retain current `U_c`, typed footprint, independent admission, and all
  proof/implementation gates as open. No shared record was edited.
