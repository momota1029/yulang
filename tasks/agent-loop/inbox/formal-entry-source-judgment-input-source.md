# R172 source construction snapshot and origin projection

Sprint: `FORMAL-ENTRY-SOURCE-JUDGMENT-INPUT / R172`, contract SHA-256
`08d2d7d1579ad01a09351d0244d49d6d76bef03d7e7ece44d63ff0341a4c758c`.
Assignment: `R172-SOURCE`, handoff revision **1**; frozen at submission.
Worker: `/root/formal_entry_source_judgment_input_source`, dispatched by `/root`;
observed model/effort **UNKNOWN**. No descendants.
Baseline: primary-pinned `yulang3` /
`008c5fd5bdc17b8a253daf9e5d79916a2db404b0`; no Git commands used.
Outcome class: **source-native-evidence / conditional source derivation**.
Disposition: **NO_SAFE_CODE_SLICE**; no concrete reachable bug demonstrated.
Review: independent review pending; this report is producer evidence.

## Objective, authority and dependency snapshot

Map collection, record-field recipe insertion, formal registration, native
preparation, action creation and the effect-row consumer in one inference
construction. Assess origin transport without reinterpreting the selected
source Lambda rule. Governing packet sections: **Parent and fixed outcome**,
**Frozen inputs**, **Lanes and exact outputs**, **Resource and stop boundaries**.
The original parent remains `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:127–130`, with unchanged source domain, quantifiers and shared
witness. The packet assigns Source Generalize §§2–3 and the original-source
generation theorem to the proof lane; neither those Lean files nor their
semantics were independently inspected in this source packet.

Accepted decisions retained: R171's conditional mathematics does not establish
its successful-trace source application; collected `entry = none` cannot equal
the required prepared `entry = some port`. Interleaved record-field recipes
must be represented. Candidate `Kernel`/`Satisfies` must remain distinct from
parent `generates`/`solves`. Runtime/machine correctness is excluded.

| Exact source dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-source.md` | `8db9a9730932aedd162ad4c918000c6c73176323eae797be022a197db2174f22` |

All three hashes matched before source inspection and immediately before this
write. The primary explicitly revised only the contract baseline during this
assignment; its new baseline/hash above was acknowledged and checked. No
source dependency changed. HIR allocation facts below are inherited evidence
from the frozen R171 handoff, not fresh reads of unleased HIR files.

## One construction, with distinct phases

1. **Collected source identity.** `emit_candidate_source` retrieves the
   owner's HIR source, requires pointer equality with its input, validates the
   parent owner, and retains occurrence ownership (`candidate_source.rs:1052–1069`).
   The expression scan and later work traversal read this same borrowed source.

2. **Recipes and registrations.** Root parameters append recipes without
   formal registrations (`1082–1090`). For each Lambda, the scan records the
   current recipe length, appends its parameter, records the current formal
   length, and appends the formal with exact owner, expression index, parameter,
   recipe position, role and scope (`1098–1118`). Both `native_root` and
   `entry_effect` start `None`. The role is Computation exactly when the
   parameter annotation has an outer effects field; otherwise it is Value.
   Each record field then appends one binder recipe, with no corresponding
   formal (`1119–1123`). The shared append helper reserves before pushing
   (`560–563`). These are successful-operation observations, not an atomic
   rollback claim for the entire scan.

3. **Duplicate behavior.** A field binder is appended before insertion into
   `parameters`; a previous map value makes collection return `Err(invalid())`
   (`1120–1123`). That failure may leave private partial state. Lambda insertions
   into both `parameters` and `formal_registrations` ignore previous values
   (`1108,1118`); arbitrary duplicate Lambda IDs would overwrite. Therefore
   successful map lookup alone proves neither unique origins nor first/last
   lookup equivalence. R171's frozen HIR evidence supplies owner-branded,
   fresh parameter IDs along its mapped formation routes, including field
   binders. Its scope and unproved global mutation boundary remain unchanged.

4. **Actions retain that Lambda's payload.** The work traversal reads the
   same source expression at its index (`1208–1214`), resolves its parameter
   recipe and records its level (`1280–1288`). For an annotated computation
   formal, it clones that parameter's annotation and appends `FormalEntry`
   with the map's registration, the expression occurrence and registered scope
   (`1323–1327`). It subsequently appends `FormalAnnotation` with the same
   annotation (`1339`). With `scoped_experiment`, only `receiver_body` is
   updated on that registration during body-region setup (`1343–1347`). The
   body and record defaults are scheduled for traversal (`1349–1353`).

5. **Preparation changes the native fields.**
   `initialize_candidate_source_levels` checks the stored recipe identifies
   the stored parameter and rejects a previously prepared `native_root`
   (`2303–2313`). It obtains the positive parameter endpoint. For Computation
   it reads the parameter level and allocates a fresh effect; for Value its
   entry remains `None`. It writes exactly `native_root` and `entry_effect`
   (`2314–2325`). This body leaves owner, Lambda index, parameter, recipe,
   role, scope and actions unchanged. A successful full preparation is a
   separate premise; failures can occur before all registrations are prepared.
   Its invocation/order relative to schedule execution is not established
   here: the caller is outside these two frozen files.

6. **Effect-row consumption.** Dispatch forwards the action payload unchanged
   (`2471–2475`). `candidate_formal_entry_annotation` requires an outer row
   with at most one symbolic variable; retrieves the registered Lambda from
   its owner's source; checks occurrence, parameter, role, annotation owner,
   scope, recipe, source owner, and absence of an existing domain or retained
   permission; then requires `entry_effect = Some(entry)`
   (`candidate_effect.rs:1991–2012`). These guards do not compare the stored
   source annotation with the action annotation. Their equality needs the
   construction join in items 1–4, with freshness and a stable source snapshot.

   Nonempty concrete atoms are copied in source order into an entry permission
   containing registration, recipe, formal ID, occurrence, source owner,
   annotation/row positions, scope and entry (`2015–2031`). If a symbolic tail
   exists, its variable is keyed by `(scope,name)` (`1712–1738`), and two
   directional constraints equate it with the entry (`2042–2045`,
   `1979–1986`). Those operations call provenance admission and live effect
   constraint handling; their external implementations are not inspected.
   Only after that operation succeeds is the permission appended
   (`2047–2050`). Empty concrete rows retain no entry permission. Concrete
   atoms grant local handling permission; this consumer does not constrain
   the supplied computation to a closed row (`2060–2062`).

7. **Type and body interfaces remain separate.** `FormalAnnotation` constructs
   the annotation's value pair and admits its positive/negative links to the
   parameter before retaining a negative domain (`2125–2204`). Function
   children use polarity reversal for the argument and retain their own
   effect ports (`1851–1876`); these nested permissions are separate from the
   outer entry permission. A computation-formal name generates
   `FormalNameEffect` (`candidate_source.rs:1766–1776`), whose dispatch equates
   that occurrence's effect with the prepared entry (`2476–2479`). At Lambda
   completion, the collector retains the parameter recipe, registration,
   body value endpoint, body effect component, Lambda components and default
   effect components in one `LambdaRecipe` (`2092–2112`). Dispatch calls
   `admit_lambda_fact` (`2493`); its definition is outside this read lease.
   Thus retained endpoints are available inputs, not an established body
   typing judgment or source-rule validity proof.

The exposed entry-permission binders authenticate one retained record against
registration and entry identities (`candidate_effect.rs:557–649`). They return
borrowed records; their definitions alone establish no handler discharge or
provider/body typing premise. Such consumers remain outside this packet.

## Conditional derivation and smallest discriminating scan

Let the pre-scan recipe length be `P0`, root-parameter count `H`, pre-scan
formal length `F0`, and the record-field count of Lambda `t` be `k_t`. In a
successful scan with ordinary Vec append semantics:

```
formal_index(t) = F0 + t
recipe_index(t) = P0 + H + t + sum(k_s for s < t)
```

Induction: roots append `H` recipes; each Lambda appends one recipe and one
formal, then appends its `k_t` field recipes. Appends preserve all earlier
indices. With fresh parameter IDs, the completed map still selects the
registration appended for that Lambda, so the later action annotation comes
from exactly its source parameter. No contiguous Lambda-only recipe interval
or fixed offset from formal index may be assumed.

Smallest scan distinguishing the fixed-offset shortcut at a later formal:
start with empty prefixes and no roots; scan two distinct Lambdas, with one
fresh field binder on the first. The resulting recipes are `[p0, field, p1]`,
while the formals refer to recipe positions `[0,2]`. The second registration
has index `1`, recipe `2`. Two Lambdas and one field are needed to exhibit a
later formal's displacement in this pattern. This is a symbolic derivation
of the inspected collector loop, not an executed program, parsed source
witness, or reachable compiler bug.

Define an origin projection on a registration as
`(owner, lambda, parameter, recipe_position, role, scope)`. Successful
preparation preserves this projection while assigning a computation entry.
For an emitted annotated-computation action, the origin join can therefore
be transported from collected to prepared state. A single computation formal
already distinguishes full-state equality: its collected entry is `None`,
its successfully prepared entry is `Some(e)`.

**R171 application assessment:** origin-preserving projection is a plausible
repair of origin transport, conditional on representing actual field appends,
fresh map keys and preparation. It cannot make the existing full collected
state equal the successful trace prestate. R171's reported uninhabited
application remains blocked until a theorem explicitly uses a prepared state
related to collection by this projection and establishes its trace premises.
No Lean theorem was inspected or checked in this lane, so theorem reuse or
required statement changes are for the proof lane to establish.

## Exact remaining premises, coverage and next action

The first local seam left open by these source bodies is **phase adequacy**:
the actual successful source schedule must consume the corresponding fully
prepared registration while preserving the collector's origin/action join.
Owners are the caller of `initialize_candidate_source_levels`, schedule
entrypoints, and the source-to-model bridge. The inspected preparation and
dispatch bodies alone do not prove their invocation order. The next separate
semantic seam is interpretation of the annotation value pair, entry/tail
constraints and `LambdaRecipe` as the independent formal interface and body
typing judgment; its actual Lambda admission owner is `admit_lambda_fact`.
No candidate `Kernel`/`Satisfies` premise, parent `generates`/`solves`, solution
soundness, or shared parent witness follows from these source reads.

Method: static source dataflow plus the explicit induction above. No oracle
or executable checker was used, hence no claim of independent oracle
agreement. Shared assumptions are ordinary Rust collection/index semantics,
successful operations, the frozen source snapshot, and the R171 handoff's
qualified HIR freshness evidence. No seeds, random ranges, executable
mutations, exhaustive enumeration or executable experiment apply. The two
symbolic discriminators attack omitted field slots and full-state equality.
They do not attack source typing semantics.

Checks: bounded `rg -n`, `nl -ba ... | sed -n ...`, dependency `sha256sum`
before inspection and before writing; contract hash rechecked after the
explicit primary baseline amendment. All source searches were restricted to
the two admitted Rust files. No runtime/machine paths were opened. No build,
test, Cargo, Lean, Git, scratch/cache/environment/target/dependency writes
occurred. Only this handoff was created. Commands were lightweight and serial
apart from one batch of independent read processes. CPU time and peak RSS
were not measured; no heavyweight process ran. The assignment remained
within its 600-second wall-time budget; precise launch time was unavailable.

Unverified scope: caller sequencing, fresh-effect allocator internals,
`admit_lambda_fact`, live propagation, failure publication/retry across the
whole inference session, unleased mutation sites, full HIR construction,
source-rule adequacy, semantic judgment, and all runtime/machine behavior.
There is no production code slice justified by this evidence.

Recommended next action: have the proof lane use the explicit append-aware
origin projection and prepared-state relation to identify the exact first
independent Lambda premise still missing; return phase/admission source-owner
reads as a proposed bounded follow-up to Luna if needed. Do not repeat an
equivalent model that assumes these source transitions or premise validity.

Worker state: **STOPPED; writes stopped after revision 1 submission**.
Unresolved descendants: none. Frozen research checkpoint ready for primary
intake; independent review/integration pending.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/formal-entry-source-judgment-input-source.md`.
- Baseline SHA: `008c5fd5bdc17b8a253daf9e5d79916a2db404b0` (primary pin).
- Changed source dependency hashes: none; all three authenticated hashes above.
- Contract dependency amendment: baseline-only revision explicitly acknowledged;
  final contract hash `08d2d7d1579ad01a09351d0244d49d6d76bef03d7e7ece44d63ff0341a4c758c`.
- Review status: unreviewed producer source evidence and conditional derivation;
  no theorem, production, or independent-review claim.
- Checks already run: bounded exact-source reads/searches and dependency hashes.
- Proposed message: `Record R172 formal origin projection and preparation source audit`.
- Shared-record deltas intentionally left to primary/curator: retain parent OPEN,
  record NO_SAFE_CODE_SLICE, field-aware recipe/formal indexing, preparation
  projection and missing phase/source-rule adequacy owners; record review result
  and immutable submission hash. No shared records edited here.
