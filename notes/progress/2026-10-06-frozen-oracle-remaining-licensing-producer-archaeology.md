# Frozen Oracle: annotation declaration identity before projection

Date: 2026-10-06
Status: independently compiler-referee-reviewed bounded historical characterization; research-only, no semantic authority
Yulang3 baseline: `27dc9b31da2b277dfdd09c97c161077f6c6b21c3`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none
Review: compiler_referee PASS on content SHA-256 `fec7314753f3faff4d7772e509c661a712ec8c35a3d29e7368f52565a229f5b2`, including delta review closing one minor atom-shape finding; scope limited to cited historical dataflow, conditional identity discriminator, and current-authority boundary

## Objective, method, and result

Inspect a remaining historical producer before solved signature projection,
without repeating the reviewed ordinary-call, frame/formal grouping, solver
transfer, call-upper feedback, occurrence export, claim-certificate or replay
ownership traces. The distinct seam is **parameter annotation return-effect
lowering and direct declaration of its stack facts**. Method: one bounded
source pass, explicit local dataflow derivation, and a two-occurrence analytical
discriminator. No compiler, Oracle or checker execution was used.

The producer is concrete: equal closed annotation rows can share one effect
variable, while their stack declarations receive distinct supplied fresh
marker IDs. Value constraints retain the annotation lowerer's source origin;
the direct stack-fact registration call omits that origin and submits
`Declaration(UnknownInternal)`. This separates effect endpoint, marker and
source-root identities before projection. It does not construct current
original-signature licensing or its exhaustive inverse.

Current authority is [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [nested-block interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3, and [directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4. The selected shared source contract, original scopes, typed incidences,
Q independence and one original `xi=(nu,K,D)` remain requirements. Upper-use
protection does not back-protect provider lowers; annotations, internal views
and printed schemes remain distinct. The exact nested block returns the local
closure capturing the outer formal. No meaning is reopened here.

The primary's active gate and [conditional licensing construction](2026-10-06-original-signature-licensing-construction.md)
identify the missing clause as independently interpreted `Attach_C(X,e,t)` /
`Lic_C(X,t)`, including attachment soundness and exhaustive original-rule
inversion on the same row. All listed predecessor archaeology was read first;
the newer [source-boundary eligibility note](2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md)
was also checked to exclude a duplicate classifier investigation.

## Hypotheses and claim classes

H1: the ten historical source files, two test files and fifteen current
dependencies in the inventory equal their pinned blobs. Verified byte-for-byte.

H2: two successful parameter annotation connections use the same carried
`closed_effect_rows` map and the same nonempty closed return-effect row R.
R has no tail or wildcard and contains one successfully resolved **nullary
Named/Builtin constructor atom**; its key and constructor lowering succeed.
Their argument/result shapes introduce no additional stack facts. Annotation
lowerers have separate source origins and fresh target value endpoints. No
unrelated operation changes the map between these connections.

H3: the allocation calls return distinct marker IDs `s1 != s2`, submission
and drain complete without terminal failure, and no unrelated declaration
uses either ID. This explicitly supplies the allocator property; this pass
does not prove it from a helper name or inspect the complete allocator/solver.

Established results are H1 and the cited assignments/call arguments at the
frozen revision. The result is bounded historical characterization with a
conditional local derivation under H2/H3. H2/H3 are candidate trace premises,
not established accepted-source coverage. No current conditional theorem,
reviewed theorem, source impossibility, repository-wide absence result,
soundness/principality result or implementation authorization is claimed.

## Exact historical producer

All following locators are relative to the frozen Oracle checkout.

1. `crates/infer/src/lowering/expr/lambda.rs:649–684` passes the same annotation
   variable/closed-row maps through the defined-parameter loop. At
   `:1266–1307`, `connect_lambda_pattern_annotation` moves those maps into
   `AnnConstraintLowerer`, calls `connect_parameter_computation_detailed`,
   and returns the maps to the caller. This is source annotation lowering,
   before a final generalized signature is collected.
2. `annotation/constraints.rs:54–78` gives each such lowerer an Annotation
   source origin; `:249–260` sets `parameter_function_boundary=true` for the
   connection and restores it afterward, including a returned error. A plain
   Function annotation reaches `connect_value_detailed` through `:264–285`.
   The Function case at `:363–390` lowers its return-effect port separately
   and builds positive/negative four-port Functions. The value connection
   submits both `bounds.pos <: target` and `target <: bounds.neg` with that
   lowerer's `self.origin` (`:124–138`).
3. `annotation/constraints.rs:426–472` handles a return-effect row. At a
   parameter Function boundary, the non-wildcard path obtains its variable
   from `function_boundary_effect_stack_inner`. That helper (`:602–619`)
   reuses a map entry for a matching closed-row key or inserts one fresh
   variable. `closed_effect_row_key` (`:939–958`) rejects empty, tailed or
   wildcard rows; its structural keys (`:960–1003`) carry type identities
   and shape, with no annotation occurrence, signature path or source origin.
   This is ordered structural-key reuse, not an assertion that all
   semantically equivalent effect rows receive the same key.
4. The same return-effect path separately calls `effect_row_stack` and
   `register_stack_facts` (`:458–459`). For the nonempty resolved atom case,
   `effect_row_stack` requests a marker and returns a push plus its ID
   (`:664–691`). Atom conversion at `:741–752` uses constructor lowering;
   `:1004–1010` selects the corresponding subtractability. Registration
   loops over stack entries and calls
   `declared_subtract_fact(var, entry.id, subtractability)` (`:593–599`).
   It passes neither `self.origin` nor a structural path.
5. `constraints/machine/entry.rs:901–918` delegates that default declaration
   call to the explicit-origin variant with `OriginId::unknown_internal()`.
   The variant records the supplied origin under the marker ID and enqueues
   `SubtractFact { effect, id, subtractability }` with
   `SubtractFactDerivation::Declaration(origin)`, then drains (`:919–944`).
   This is the exact stop point: direct declaration enqueue/drain. Its later
   proof transfer, source reconstruction or generalized use is not audited.

The alternative inspected declaration-side anchors do not provide a new
licensing route in these windows: method-body requirement connections submit
their value/effect comparisons with UnknownInternal
(`lowering/expr/method_body.rs:1361–1390`), and pattern lowering registers
an occurrence root after pattern lowering (`lowering/pattern.rs:25–50`).
The latter is the previously characterized occurrence mechanism, not a new
result here. Source-boundary location records are expressly separate from
derivation traversal (`lowering/source_boundary_provenance.rs:6–9`).
These local observations do not exclude other producers elsewhere.

## Smallest local identity discriminator

Use two supplied annotation connections satisfying H2/H3. One successful
closed row R and two return-effect occurrences are sufficient; no Call,
Function comparison outcome or solved projection is needed.

```text
first connection:  key(R) absent -> allocate e; map[key(R)] := e
                  allocate s1; submit Declaration(UnknownInternal,e,s1,A)
second connection:key(R) found  -> reuse e
                  allocate s2; submit Declaration(UnknownInternal,e,s2,A)

e1 = e2 = e       s1 != s2
value constraints retain source origins o1 and o2 respectively
direct fact declarations receive UnknownInternal in both connections
```

Here A is the same constructor-derived subtractability because the atom is
nullary. Map lookup proves endpoint reuse; the supplied distinct allocator
returns plus separate stack construction prove the marker distinction; the
default declaration call proves the passed-origin distinction. Under H3,
declaration-origin lookup for either marker yields only UnknownInternal. The
proof does not claim the final solver state has no additional provenance
sidecar.

Collapsing the two records to their endpoint e loses the marker distinction.
Using only their direct declaration origins cannot select o1 versus o2.
Conversely, distinct marker IDs alone do not recover a typed signature path,
formal/slot owner or contribution license. This is a representation witness,
not an admitted source counterexample, executable experiment or new static
slot-sharing rule. Two occurrences are the minimum needed to display endpoint
sharing alongside distinct markers. No cardinal-minimal language witness is
claimed. The analytical mutations are dropping marker identity or replacing
the annotation-origin channel by the default declaration-origin channel;
neither mutation was executed.

## Tests, independence, omissions, and stopping condition

Inspected test contracts in `annotation/tests.rs:202–236` retain repeated
named type-variable identity within a Function annotation and across two
expressions using one builder. They concern annotation building, not the
closed-row map or source-to-marker licensing. The bounded symbol search in
that test file found no direct closed-row reuse test. The separate local-var
boundary comparison test file was inspected only by locator searches; its
callback/solver comparisons are not used to infer this declaration's source
meaning. Neither test file was run, and no global test absence is claimed.

The Oracle source is an independently grounded historical artifact relative
to current stipulated-transition probes. Its annotation lowerer, declaration
ledger and solver share one implementation's assumptions; they are not
independent semantic oracles. Byte equality establishes provenance. The local
derivation establishes cited code consequences conditional on its trace
premises. It neither assumes and then proves source rules in a checker nor
validates the current language semantics through Oracle outcomes.

This distinct pre-projection declaration producer still lacks original
`beta/Slots(beta)`, typed position/owner/receiver correspondence, invocation
contribution identity, complete original profile and both licensing coverage
directions on one `xi`. An annotation-origin-bearing comparison and an
UnknownInternal stack declaration are different channels; unproved recovery
from later explanation cannot fill the upstream source judgment. Unannotated
protection and ordinary-value refinement also do not follow from this
annotation-only path.

Failure conditions include changed blobs, a different connection mode,
non-keyable rows, changed map lifetime, failed constructor lowering/allocation,
equal marker returns, unrelated declarations, or solver/resource failure.
Unverified: accepted surface realizations, broader signatures/annotations,
imports/method resolution, recursive groups, complete source occurrence
coverage, post-drain provenance recovery, admission/nonemptiness,
soundness/principality, source adequacy and production conformance.

The file budget is exhausted at ten source files; no expansion into the full
solver is justified here. This pass does not establish that all plausible
repository routes are exhausted. It identifies this remaining local producer
and its precise correspondence boundary. Recommended next action: derive the
current `Attach_C` source contribution clause and its exhaustive inversion
directly, keeping endpoint, original occurrence and contribution identity
separate; use this historical seam only to check identity-loss shortcuts.

## Commands, resources, and frozen dependencies

Commands used bounded `rg -n`, `rg --files`, `sed -n`, `nl -ba`, and Python
byte/hash comparison against read-only `git show <pin>:<path>`. All twelve
historical and fifteen current dependency comparisons passed. No Git mutation,
Oracle execution, build, test, benchmark, checker, formatter, random seed,
enumeration range, log/scratch output or other written path. At most four
lightweight context reads were batched initially; source inspection/hash work
was sequential. No heavyweight process budget was consumed. CPU, peak RSS and
total wall time were not instrumented; individual captures completed within
about 0.2 seconds. One initial aggregate context capture and one locator
capture truncated; decisive windows were recovered. Nonexistent
`lowering/tests.rs` and one current-tree Oracle locator failed and were not
counted as inspected files or absence evidence.

Historical SHA-256; paths below are under `crates/infer/src/`:

| Path | SHA-256 |
| --- | --- |
| `lowering/source_boundary_provenance.rs` | `9d9f1694d4848be9daddea986b80be833f081d1e78a31ce1a0e540b740d74412` |
| `uses.rs` | `e3492318c6cb788097b350f1cd692023ffa7454b8a7c2f8fc448a0293520fdf3` |
| `lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| `lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `lowering/tests/local_var_effect_boundary_edge_comparison.rs` (locator search only) | `1b5f285e1cd106652b88b2b08631e11512e44454a15e639d56188845e11db236` |
| `annotation/tests.rs` | `c94d9e62a762d4fc2cece87cc6acf8b92aa88057b885057460326ef2eedd1b7c` |

Current dependency SHA-256; progress entries below are under `notes/progress/`:

| Path | SHA-256 |
| --- | --- |
| `tasks/current.md` | `97d24eda811266b96dfb5f85c16828ec8c51994e2db6bbdc67b8af783a6254b5` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `1621abe333739b475222953ec52adfd5a67d54727c2b612bdee160186ede8b30` |
| `2026-10-06-frozen-oracle-missing-source-producer-continuation.md` | `7b31b95460725948b32f41a3f792c6efc125ade48d83389122f5f3145d36d552` |
| `2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md` | `68249800e84b767860b76a88086bbe9321c060304065f408fea4afc2f32cd3f9` |
| `2026-10-06-frozen-oracle-annotation-call-producer-archaeology.md` | `dae5c2813318acf4a875de5ee5a34e435f870ebd783f7b9b28a7abbb47b18d4d` |
| `2026-10-06-frozen-oracle-multiuse-aggregation-continuation.md` | `ba24a24339402daf9b24d089935754401c0af87786cca6b82dce74bcb9432b67` |
| `2026-10-06-frozen-oracle-claim-qualified-signature-attribution.md` | `c5a89fb3484d3eb95c524323994d86aa6ffeef1c8996275bdd520ad9f12f62fd` |
| `2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md` | `bfb7ed9b54fca51d64ae934df7c501b0322384f116e92c4f2144413e2572b223` |
| `2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `2026-10-06-frozen-oracle-source-producer-archaeology.md` | `4f3cfff031dd9e5a90b5df3e2f7aded3535007f16ca5abd45c7892f6567a244b` |
| `2026-10-06-frozen-oracle-whole-tuple-source-producer-correspondence.md` | `fcc23c134001e25f02a28a251c38ef083872b51458e39948fcfb3dc0c8652dae` |
| `2026-10-06-frozen-oracle-missing-producer-followup.md` | `d211a365acca703b782e2fc936864b9c0c189a5861ce34729326c3f3b642d6ee` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-remaining-licensing-producer-archaeology.md`.
- Baseline SHA: Yulang3 `27dc9b31da2b277dfdd09c97c161077f6c6b21c3`;
  Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; twelve historical and fifteen current
  dependencies matched their pinned blobs.
- Review status: frozen, unreviewed research-only historical characterization
  and conditional local derivation. Producer writes stop at submission.
- Checks already run: bounded source/test-contract reads and locator searches,
  pinned byte comparisons and SHA-256 inventory; no tests/builds/execution or
  Git mutation. Primary owns final lease/diff inspection and integration.
- Proposed one-line research-checkpoint commit message:
  `research: distinguish Oracle annotation endpoints, markers and source origins`.
- Shared-record deltas intentionally left for primary/curator: add this
  pre-projection closed-row reuse/direct-declaration seam and its identity
  discriminator; retain original `Attach_C`/`Lic_C`, exhaustive inversion,
  same-row complete profile/admission and all proof/production gates as open.
  No task, theory map, index, authority or question-board file was changed.
