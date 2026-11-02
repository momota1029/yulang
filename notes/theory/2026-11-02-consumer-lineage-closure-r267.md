# R267: Value-kind temporal reduction at the Function consumer

Revision 1. **Unreviewed candidate source-native evidence; original parent OPEN.**
Sole author `/root/sol_r267_consumer_lineage_r5`; no descendants or coauthors.
Contract R267 revision 5, SHA-256
`54d53b708f65e189d4efd91a049ea800483bcec4ba4e7e8f3df5f71e4a6411ad`.
Baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Parent and result boundary

The unchanged edge is inference soundness -> R70 copy correspondence ->
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`. Preserve the full accepted source domain,
original Simple-sub A/B, independent satisfying assignments, shared witnesses,
F1/FK1 and foreign continuations. Original parent/A/B closure delta is **0 -> 0**.

This packet derives a previously unresolved subcase from the actual Context
mutation owner: a retained Value relation cannot be discharged. Consequently
Value-preserving ordinary transports cannot acquire the temporal scalar-context
discrepancy proposed for arbitrary Effect lineages in R265. The actual reached
Replay -> Function consumer has Value kind, so this result applies there.
It does not establish which canonical lineage that source occurrence requires,
the existence of a matching opposite input, or coverage of Effect descendants.
No complete accepted-source occurrence/canonical-candidate/consumer join was
constructed. No source-qualified counterexample or production defect is claimed.
Lean theorem types and axiom audit: NOT APPLICABLE; no Lean work or checker.

## 1. R265 equations and the actual kind distinction

Retain R265's definitions without alteration: K(r) is immutable
`relations[r].key.context`, and

```text
P_t(r) = discharge_residuals_t[r] (or I) if r is discharged at t;
         K(r) otherwise.
```

R265's attempted equations, verbatim, are

```text
J(P_t(r), K(h))  ?~  J(P_t(c), K(h_c))                 (TEMP265)

Z_A(J(P_t(r), K(h))) = Z_A(J(P_t(c), K(h_c))),          (Z265)
```

J(I,I)=I; otherwise J(a,b) interns ordered ContextExpr::Replay. The notation
`?~` remains an unresolved consumer comparison, not an assumed equivalence.
Z_A remains the actual validated `(filters, residual)` from
`candidate_zero_word_filters` in fixed live arena A before callbacks, under
successful reservations/sampling. Failure of this stronger equality alone is
not a parent falsifier. Actual opposite inputs and subsequent child-local
observations remain part of the obligation.

The important distinction comes from the pair kind, not context equality or a
source restriction. The replay that dispatches a PositiveFunction against a
NegativeFunction is a Value task (`lib.rs:14908-14967`); its four ports contain
two Value tasks and two Effect tasks. An Effect relation does not become that
Function parent by endpoint canonicalization.

## 2. Source-native invariant VD267

For each live retained relation r in a Context state constructed through the
inspected State owner and its valid checkpoints:

```text
r in discharged  =>  relations[r].key.pair has Effect kind.
Hence pair(r) has Value kind  =>  P_t(r) = K(r).
```

This is a local constructor/mutation invariant derived below, not a premise
inserted to assume TEMP265, all-source ENTRY-WF, or successful-helper coverage.

1. `State` derives Default (`candidate_context.rs:1005-1006`), so its private
   discharge set/map/log and relation vector start empty. Those fields are
   private (`:1048-1087`); external source modules cannot insert into them.
2. The only relation construction appends an immutable RelationKey containing
   pair/context/sources/scoped (`relation_with_scoped:3481-3512`). Existing keys
   are returned by interning, not overwritten. The only removal is rollback's
   suffix drain (`:2255`). Exact-path mutation searches found no get_mut,
   iter_mut, last_mut, table assignment or relation-key overwrite.
3. The only insertion into discharged and discharge_residuals is
   `candidate_context_execute_relation:4299-4301`. Its initial assertion
   (`:4226`) ties the retained key to the canonicalized task, including kind.
   Identity context returns at `:4245`. Empty filters return at `:4249`.
   With nonempty filters, matching task as Value returns an error before
   callbacks or insertion (`:4250-4253`). The continuing branch is Effect.
   A publication followed by a resource-sampling error still has Effect kind.
   Nested synchronous callbacks do not replace this local `relation` argument.
4. Rollback removes every discharge/residual entry in its discharge-log suffix
   (`:2244-2247`) before draining relation suffixes. Entries retained from the
   checkpoint belong to retained relations. Later reuse of a truncated numeric
   RelationId therefore does not inherit that removed discharge. This concerns
   coherent Context checkpoints, not an unproved whole-solver rollback theorem.

Every private owner mutation preserves the invariant. Applying the exact
`post_check_context` definition (`:3716-3720`) gives P_t(r)=K(r) for Value r at
every cut where it remains the same retained relation. This does not assert
K(r)=I: payload-free directed contexts are left intact. It does not assert that
the Value executor must succeed when given a filter-bearing context.

## 3. Application to ordinary Value transport and actual consumer cuts

At an actual selected Value slot, Work::Bound's source and destination are
Value-kind BoundKeys. The scheduling retains the raw item and canonical child
separately (`candidate_extrusion.rs:110-180,399-417`). Exact raw-prefix copying
(`candidate_effect.rs:1045-1089`) calls the witnessed transport owner, which
creates child x with K(x)=P_t(r), exact sources, transported scoped flow, actual
Transport dependency, antecedent snapshot and FiberTransform
(`candidate_context.rs:4737-4751`). Therefore **K(x)=K(r)** for that Value input.

EqualityCanonicalization changes row representatives within kind. ParentCopy
matches Value/Value or Effect/Effect before copying (`candidate_intrusion.rs:
614-620,638-662`). Task transport canonicalizes a pair of the same kind and
asserts alignment (`candidate_context.rs:4186-4204`). Applying VD267 at each
ordinary Value-preserving transport gives K(child)=K(parent). A finite chain of
these actual transports thus preserves K, even when its RelationIds, keys,
snapshots and transform witnesses differ. No new transport edge is inferred.

For R265's fork, when r and c have Value kind and c is the actual equality
child produced at e:

```text
K(c)=P_e(r)=K(r);  P_t(r)=K(r);  P_t(c)=K(c)=K(r).
TEMP265 reduces to J(K(r),K(h)) ?~ J(K(r),K(h_c)).
```

This removes the r/c **discharge-time** discrepancy in this kind sector. It
does not assume K(h)=K(h_c). If the two actual opposite inputs are established
to descend through ordinary Value-preserving transport from the same retained
ancestor, VD267 also proves their scalar contexts equal; both J expressions
then denote the same ContextId, and successful Z_A observations in the same
arena agree. This is an application rule with an explicit outstanding path
join, not a completed source simulation. Replay/Derived growth that changes
the actual input ancestry is not such a transport chain.

The actual replay recipe reads immutable K(lower), K(upper), exact ordered
BoundKeys and RelationIds, unions sources and composes scoped flows
(`candidate_context.rs:4411-4497`). For its actual Value child q and canonical
task transport z, VD267 gives **P_v(q)=K(q)** and **K(z)=K(q), P_v(z)=K(z)** at
every retained consumer cut. Thus child-local Value discharge synchronization
is not an additional missing premise at this actual Function consumer.
The typed drain retains the processing relation through Transport, Context,
Dispatch and FunctionAdmission (`lib.rs:14411-14485,15060-15090`). The Function
port inherits that processing relation's K, then performs its actual Swap or
Preserve and child-local prefix (`candidate_context.rs:3924-3988`). Authentic
demand root, original call, input route and output scope are still checked.

If a future source join establishes the complete equal RelationKey for two
Value replay candidates at one live cut, interning yields the same q; all of
its own P_v(q) observations are then literally about one retained object.
Scalar equality alone does not establish equal pair/source/scoped components,
equal demand roots, evidence coverage, or equal exact transport lineages.

FreshUse remains separate. Preparation and emission both read relation_context
= post_check_context (`context:1796-1799; scheme:4694-4727,4947-4995`). For the
same retained Value parent VD267 removes the proposed intervening-discharge
change between these two samples. It does not identify independent use maps,
renames, use origins, scope remaps or provider/witness identities. Effect
parents can still have different samples; their equation remains open.

## 4. Forward source join attempt and the first missing evidence

The exact forward owners inspected here establish these genuine, separate
links. `candidate_value_graph.rs:329-344` constructs an Apply's association
from its source owner and resolved callee, keyed by that checking occurrence.
`candidate_source.rs:1872-1924` retains its argument, callee, application result,
effects, checking/cause and call index. `shadow_apply.rs:4302-4399` constructs
the actual negative Function demand, retains native registration before
admission, and constrains the actual callee against it. Context seed
`:3793-3838` retains its source event and an eligible scoped introduction.
Qualification uses those source events, and actual deep-row Visits retain
parent/copy/polarity/target/occurrence (`candidate_intrusion.rs:305-365`). The
two structural Value/row dispatch branches call ordinary extrusion at
`lib.rs:14822,14835`. These are source constructor equations, not an accepted
finite history realizing an aliased selected slot and its later consumer.

The forward construction has not joined those source associations to one
specific canonical candidate c independently required at a later actual
copying occurrence omega, with its actual opposite input h_c. In particular:

- an Apply result remains its own source endpoint; Action::Link emits a
  constraint (`candidate_source.rs:2482-2486`), not row equality;
- qualification retains the produced parent/copy pair but does not make every
  high structural slot belong to the eventual copied owner;
- a canonical bucket can accumulate from multiple physical slots, replay
  derivations and histories. The actual consumer does not demand every member
  merely because it appears in that bucket;
- every selected direct/exact slot is scheduled; raw-prefix transports,
  unscoped bootstrap, incoming Allowances, earlier canonicalization and both
  pre-merge copy sides must all be included before alleging missing lineage.
  The current merge's later sweep cannot justify its earlier lookup.

No candidate finite history in this packet completes that join, so no absence
claim is made from a preferred slot, unequal buckets or unequal ContextIds.
The remaining Value-side evidence is the **actual required-lineage and ordered
opposite-input join**, including pair/source/scoped payload and each physical
slot/alias/merge witness. The Effect-side temporal equation and later Effect
port executions remain independently unresolved. VD267 does not erase them.

## 5. Parent application, TODO and authority

R70's raw-prefix successful copy fact now supplies its Value transport with an
exact time-independent scalar context and the reached Value replay/Function
parent with its exact P_v observation. Its dependence on proving a possible
Value r/c/q discharge mismatch is removed locally. R71's original coverage
claim remains OPEN at the source-required canonical candidate/opposite-input
join and full kind-sensitive transport/consumer coverage. This is a smaller
local obstruction; it is not original parent closure or a reviewed theorem.
ENTRY-WF, drain/eventual Diagnostics, Q262-EPISODE, permitted histories,
whole-solver rollback, diagnostic adequacy, successful-helper coverage, full
soundness, A/B, F1/FK1 and foreign continuations remain OPEN.

Mutual TODO `R267-SOURCE-INPUT-JOIN-1` to Luna: retain original R70/R71. Inputs
must be one actual source-generated omega with origin/receiver Value and event,
all produced parent/copy identities/levels, every selected physical slot/raw
prefix, canonical candidate and its independently justified consumer need,
all ordinary/FreshUse/merge paths and exact transforms/snapshots, ordered
opposite inputs and source/scoped payloads, plus Effect and child-local cuts.
Owners are source Apply admission, Value association/qualification, Work::Bound,
merge/canonicalization, FreshUse, Replay, Context execution and Function ports.
Output must be a source-corresponding complete join/simulation or an accepted
source missing-lineage witness after complete competing-slot accounting.
Falsifier remains a named reached consumer requiring a lineage absent from all
actual transports; a failure of Z265 alone is insufficient. No new semantics,
source dependency or observer lease is granted by this TODO.

`NO_SAFE_CODE_SLICE`: inspected Work::Bound/raw transfer and Replay/Context/
Function owners reveal a proof correspondence gap, not an established violation
of an approved source clause. No production edit or implementation fix follows.
A separately authorized provisional observer, if chosen by Luna, should record
the exact join tuple above and retain kind; treating a Value discharge mismatch
as the sole falsifier would now be vacuous.

## 6. Evidence, provenance and freeze

Reused with actual premises: R70's successful local worklist facts; R71's
reviewed one-way raw retention/canonical forwarding; R265's independently
accepted conditional consumer formulas. Their authors are respectively
`/root/r70_ordinary_extrusion_proof` with complementary
`/root/r70_extrusion_countertrace`, `/root/r71_raw_canonical_proof`, and
`/root/sol_r265_consumer_lineage_51dd6af`. This packet assumes no R261/R262
result. Their five nested provenance paths, R255's excluded theory, R230 and
all quarantined outputs remain unread. R267 revisions 1-4 are history only;
their pre-technical stops provide no mathematical proof attempts.

Initial gate: all 19 immutable operational files and all 22 direct technical/
history files matched their R267-r5 pins, including the contract hash above.
R255 manifest `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`
authenticated **36/36** entries via sha256sum before source bodies; only the
14 enumerated Rust/HIR paths were eligible for body reads. Exact source claims
here use the current pinned bodies, not older line numbers or nested lists.
Luna's operational provenance clarification was separately authenticated at
`a37a17de572be2fbcf7a1cb69e44cb026be2f12a5e90b94d3814211acb22b258`.
Final revalidation, artifact hashes and resource/cessation receipt are in the
one frozen handoff and terminal return. No new proof dependency is admitted.

Three stages: kind-sensitive equation derivation; forward source/transport
join attempt and precise remaining premise; parent application and freeze.
Grant 1200 seconds, no reset/extension. Requested Sol/high (current assignment
records gpt-6-sol/high); observed model/effort UNKNOWN. No tests, Lean, builds,
probes, Cargo, production/expectation edits, Git, scratch/cache/generated output,
external contact or descendants. Only this theory and its exact assigned inbox
are new paths. This producer is ineligible to certify the result independently.
