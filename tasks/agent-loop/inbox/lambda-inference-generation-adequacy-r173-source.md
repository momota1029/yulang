# R173 Lambda construction and admission endpoints

Assignment: `R173-SOURCE`, revision 1; producer source evidence, frozen on
submission. Worker `/root/lambda_inference_generation_adequacy_r173_source`;
primary `/root`. Requested role `researcher`, inherited model/effort with no
override; observed model/effort **UNKNOWN**. Baseline: primary-pinned
`yulang3/a80f58d4f`. Contract SHA-256:
`00ea0e1db6fb88659d4b4e1f8b55d6fc5cd1e7c2f315cfb51d738c989f228b4c`.
Active-work acknowledgement was sent to the primary before any write.

Disposition: **NO_SAFE_CODE_SLICE**. This is a static construction derivation,
not an inference soundness theorem or an independent review. The parent remains
`YulangClosure.SourceProblem.InferenceSoundness`, with its original domain,
quantifiers and one shared witness. Runtime/evaluator correctness is excluded.

## Dependency snapshot and method

All contract inputs matched before substantive source inspection. Relevant
exact dependencies:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| R172 source handoff | `568a16bc3ca177e57ba0915c4b9dc96cf6c9aa6c364df0c31d57e61333e20a9e` |
| R172 theory note | `3558480ed78086ad7471b96a6e41aa88db3b7b8a6d8b54e092fae7b6dce26ef9` |
| R172 proof handoff | `388b20cfa8698c5e6a71b31661fbbc428a72bb2c1c720562a225da439ec7b37c` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `InferenceConstruction.lean` | `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0` |
| `OriginalProofProgress.lean` | `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39` |

Only the two named Rust source files and frozen R172 source handoff were used
for the source derivation; Lean inputs were hash checked, not interpreted.
The contract's Rust-source lane and original success/stop boundaries govern
this packet. Repository research, design-authority and Git-concurrency rules
and the authoritative top-level inference principles were read. No selected
language meaning was changed.

Method: follow concrete indices and payloads through successful collection,
session construction, schedule dispatch and `admit_lambda_fact`. Ordinary
Rust Vec/HashMap semantics and successful checked allocations are explicit
assumptions. Source freshness beyond the inspected construction is qualified
R172 evidence, not newly proved here. No semantic oracle, executable probe,
random seed/range, mutation run or exhaustive search was used.

## One Lambda from source to prepared registration

Write `S` for one borrowed `LocalSource`, `O = S.source_root()`, `i` for a
Lambda expression index, `L = S.expressions()[i].occurrence`, and
`Lambda { parameter = p, body = b }` for that expression. Let `q` be the
appended parameter recipe position and `r` its formal registration index.

Collection selects `S` through `hir.local_source_for(source_root)` and calls
`emit_candidate_source` (`lib.rs:1218–1239`; member route `1374–1386`). The
callee requires pointer equality to the owner's HIR source and matching
receiver ownership, retaining occurrence-to-owner/HIR-position maps
(`candidate_source.rs:1052–1069`). This establishes the local source snapshot
join for this invocation; it is not a global HIR immutability proof.

The Lambda scan appends `parameter_recipes[q] = p.id`, then registration `r`
with `(owner, lambda, parameter, recipe_position) = (O,i,p.id,q)`
(`1104–1118`). Its role is Computation iff `p.annotation.ty.effects` exists;
otherwise Value. Its initial native root and entry are `None`. Scope is the
binding-parameter scope if present, otherwise `for_source(O)`. Record field
recipes interleave after this recipe (`1119–1123`); therefore `q` is not in
general `r` plus one fixed offset. The map joins below require distinct keys
or the frozen HIR freshness premise; Lambda map insertion does not reject
an overwritten key.

For that same `p` at `Work::Visit(i,level,region)`, the collector records
`parameter_levels[q] = level` (`1280–1288`). If annotated, it clones exactly
`p.annotation` once into an Arc. With an outer effects row it first appends
`FormalEntry(r, annotation, L, registration[r].scope)` (`1323–1327`), then
appends `FormalAnnotation(annotation,q,L,scope)` using the same Arc (`1339`).
That annotation is the Lambda parameter annotation. A named binding's result
annotation is a separate action on the terminal body (`lib.rs` is not its
owner; `candidate_source.rs:2170–2190`). These identities must not be merged.

The collector schedules `Work::Finish(i,level)` before pushing its children
(`1228`), then pushes body `b`, and record defaults in reverse field order
(`1349–1353`). The LIFO walk consequently emits those default/body actions
before this Lambda's finish action. `BeginLambda`, parameter actions and
annotation actions precede them. At finish, the exact recipe is
(`2092–2112`):

```text
occurrence = L
parameter_position = q
formal_registration = Some(r)
root_component = positions[i].value
body_value_endpoint = endpoints[b.ordinal]
body_effect_component = positions[b.ordinal].effect
lambda_effect_component = positions[i].effect
default_effect_components = field-default effects in source field order
```

Here `endpoints[j]` is a parameter recipe for a direct parameter Name,
otherwise its value component (`1135–1141`); ascriptions can alias the
peeled child's endpoints/components (`1143–1159`). Thus the body result may
be a parameter endpoint instead of its syntactic expression's own value row.
`Action::Lambda(recipe_index)` and `EndLambda` follow the recipe append.

## Local startup order is now located

`InferenceSession::try_new` moves the batch into the session and sets
`B = parameter_live_base = number of value components`
(`lib.rs:10087–10143`). It allocates one dense live row per component and
then parameter row `B+q` per recipe (`10409–10463`). Only after all those
allocations, it calls `initialize_candidate_source_levels` (`10464–10467`)
and returns `Ok(session)` at `10473`. `try_new_candidate` calls `try_new`
before `start_candidate_graph` (`10501–10505`). Hence a successfully returned
session on this constructor route is prepared before ordinary later schedule
execution. This advances R172's missing caller-order evidence.

Preparation installs planned levels and iterates every registration
(`candidate_source.rs:2292–2327`). It checks
`parameter_recipes[q] == registration.parameter` and an absent native root,
then assigns a positive parameter endpoint and, for Computation, a fresh
effect row `E` at `parameter_levels[q]`. For Value the entry stays `None`.
Only `native_root` and `entry_effect` change. The allocation body's fresh
ordinal is the previous effect-row length, then a row/level/metadata is
appended (`lib.rs:10552–10581`). Thus successful preparation preserves the
origin tuple `(O,i,p.id,q,role,scope)` while computation entry becomes
`Some(E)`; it does not preserve the full collected registration.

Ordinary `run`/`run_candidate` call `execute` after construction
(`10702–10742`); source mode is graph present plus active source plan.
Expression/loose schedules enter the same driver, which retrieves the action
list from the retained batch, clones one action, executes it, then advances
its index (`candidate_source.rs:2358–2379,2423–2467`). Definition-root and
member entrypoints are visible at `2339–2356`; their external scheduling
callers are not in the two-file read set. Arbitrary direct private action
invocation and later mutations are outside this construction derivation.

`FormalEntry` dispatch forwards exactly `(r,annotation,L,scope)` to
`candidate_formal_entry_annotation` (`2475`). Its implementation is outside
this lane. The frozen R172 handoff supplies the qualified observation that
it checks source identity, uses prepared entry `E`, retains concrete local
entry permission, and equates a symbolic row tail with `E`; the observation
does not prove source semantic validity. The same qualification applies to
the `FormalAnnotation` value-pair links and retained negative domain.

For each computation-formal Name, the scan resolves the same `r` through its
parameter ID and emits `FormalNameEffect(r,N,positions[N].effect)`
(`1766–1776`). Dispatch reads prepared `E`, resolves that effect component
to its live ordinal `N_e`, and calls
`candidate_formal_effect_equal(N,1,E,N_e)` (`2476–2479`). This is an exact
argument identity, with the helper's equality semantics inherited from
R172 rather than rechecked here. Value-formal Names instead emit bottom to
their effect component and that component to empty (`1777–1782`).

## Exact Lambda admission equations

`Action::Lambda` clones the indexed recipe and calls `admit_lambda_fact`
(`2493`). In source candidate mode define `P = B+q`, `D` the negative domain,
`R` the positive body result, `C` its positive effect, `E` the argument effect
row, `T` the fresh return-effect row, and `V` the collected Lambda value
component term. `lib.rs:11622–11827` gives these construction equations:

1. `D = formal_domains[q]` when that retained domain exists; otherwise
   `D = live_value_term(Negative,P)` (`11623–11635`). Existence of a retained
   domain is not itself an interpretation of the original formal rule.
2. If the body endpoint is `Component(c)`, then
   `R = live_value_term(Positive,live_components[c].ordinal)`; if it is
   `Parameter(t)`, then `R = live_value_term(Positive,B+t)` (`11636–11650`).
   `C = live_effect_term(Positive,live_components[body_effect_component].ordinal)`
   (`11651–11655`).
3. Value mode allocates `E` fresh at the parameter's level and sets
   `force_entry = true`. Computation mode reuses registration `r`'s prepared
   `entry_effect = Some(E)` and sets `force_entry = false`. Both allocate
   `T` fresh at that level (`11662–11678`).
4. With occurrence ID `(L,3)`, Value mode admits and propagates
   `live_effect_term(Positive,E) <: live_effect_term(Negative,T)`.
   Computation mode omits this edge. With `(L,4)`, both modes admit and
   propagate `C <: live_effect_term(Negative,T)` (`11679–11744`). Slot 3
   also retains the inferred-entry construction `(L,E,T,id,cause)` before
   propagation/canonicalization (`11693–11709`).
5. Each default-effect component `c_j` adds
   `live_effect_term(Positive,live_components[c_j].ordinal) <:
   live_effect_term(Negative,T)` with wide slot `2^30+j`
   (`11745–11754`). The argument/return children become `E−` and `T+`.
6. `F = positive_function_term(D,E−,T+,R)` (`11755–11760`); the wrapper
   passes exactly those ordered children to the arena (`10631–10640`).
   Computation mode additionally retains `(r,L,F,E)` after checking that
   the argument-effect child is a negative live effect (`11761–11774`).
7. With `(L,2)`, admission records `F <: V`, where
   `V = batch.component_term_at(root_component)`, and propagates the value
   pair using `value_endpoint(F,Positive)` and `value_endpoint(V,Negative)`
   (`11776–11819`). Endpoint conversion may canonicalize rows; raw constructor
   child equality and equality of representatives are different facts.

Every admitted occurrence uses `CauseId::for_occurrence(id)`; recording
provenance and invoking live propagation are distinct calls. A completed call
does not by itself prove all recorded constraints have a source-semantic
solution or that the error set is empty. Lambda evaluation-effect facts are
also emitted through `candidate_local_lambda_effect` before recipe admission
(`candidate_source.rs:2093–2094`); that helper is outside this read set, so no
equation for those facts is asserted here. Noncandidate admission instead
uses `(empty,body_effect)` for function effect children (`11757–11759`);
it is not the two-mode source-candidate derivation above.

Smallest structural discriminator: a Lambda whose body has no use of its
formal has no `FormalNameEffect` action for that formal. Value mode still
generates slot 3; Computation mode does not. Therefore a proposed common
derivation demanding unconditional `E <: T` from both modes is unsupported
by the inspected constructor. This is a symbolic branch witness, not a
parsed/running program, semantic counterexample, or demonstrated Rust defect.
Likewise computation preparation changes `None` to `Some(E)`, so R171's
full-state equality shortcut remains unusable despite the located order.

## Remaining semantic seam and handoff

The inspected route now supplies explicit source identities and construction
equations for initialization, entry dispatch, body endpoints, effect flow and
Function admission. It does not interpret these Rust objects as parent
`generates`/`solves`, independent `Kernel`/`Satisfies (Build ...)`, source
admission, body typing, Shared validity or the parent `sameScoped` witness.
The missing bridge must express, for this exact `L,p,b,annotation,q,r`, how
a generated construction plus its solution yields the original Lambda
premises in both entry modes. Source endpoint equations alone cannot furnish
those semantic premises. The proof lane/primary owns the first independent
semantic registration and its precise constructor equation; this source lane
does not introduce a replacement relation that assumes the desired rules.

Coverage: successful local source collection, ordinary successful session
startup, retained action order and direct Lambda admission, both source
entry modes, optional parameter annotation, direct parameter-body endpoints,
ascription aliases, and record defaults. Unverified: all external callees,
external definition/member drivers, global HIR freshness/mutation, propagation
soundness, retained-permission consumers, all other source constructors,
abnormal publication and the original parent shared witness. No reachable
compiler bug under approved semantics was proved.

Checks: bounded `rg -n`, numbered source slices, exact dependency `sha256sum`
before inspection and before writing. Initial path discovery hash checked
`tools/inference-playground/src/lib.rs` by mistake, then corrected to the
pinned crate before any content read there; no runtime/quarantined content
was opened. No build, tests, Cargo, Lean, Git, cache, environment or scratch
was run or created. Only this exact leased handoff was written. Lightweight
read processes only; CPU time/RSS not measured; 600-second budget respected.
No descendants. Writes stopped after this revision, independent review pending.

Recommended next action: have the constructive proof lane use these exact
two-mode constructor equations to register the first independent Lambda
generation/solution interpretation and expose the remaining premise, without
identifying `generates/solves` with `Build/Satisfies` by definition.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/lambda-inference-generation-adequacy-r173-source.md`.
- Baseline: primary-pinned `a80f58d4f`; changed dependency hashes: none.
- Claim/review: static source derivation; unreviewed producer evidence;
  `NO_SAFE_CODE_SLICE`; original parent remains OPEN.
- Checks already run: bounded source search/read and all contract input hashes.
- Proposed message: `Record Lambda inference construction and admission endpoints`.
- Shared deltas left to primary: record startup-order advance, exact mode
  equations, retained semantic interpretation blocker, independent review
  outcome and frozen artifact hash; no shared records edited here.
