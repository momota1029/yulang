# Omitted formal: bounded receiving-call dispatch observation

Date: 2026-10-15
Status: provisional test-only observation harness; focused execution passed twice; one reviewed minor repair integrated
Branch: `research/simple-sub-intrusion`
Assigned frozen HEAD: `eb8c607cc4b0191896d3cfa0155841733f0bd3c4`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Parent gates: H1/H2/U OPEN; H3/P disabled

## Scope and authority

This packet adds only
`candidate_context::tests::omitted_formal_receiving_call_records_authenticated_argument_dispatch`
and this record. The existing correlation test is preserved. The primary owns
execution, review, integration, task records and all Git mutations.

Governing sources are the Authoritative
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§1.1, [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5 and the independently reviewed
[consumer frontier](../theory/2026-10-15-omitted-formal-extrusion-consumer-frontier.md).
The frontier's assigned hash was corrected by the primary before editing to
`9b137da3b91756ffc71ad5262113eb31ba8c7744a233524e7adaabb76e53998a`.
No protection positions, grants, residual semantics, production behavior,
test expectations or public contracts are selected here.

## Single fixture and authentication

```yulang
my root = { my outer cb = { my inner x = cb x; inner }; my identity z = z; outer identity }
```

This exact proposed fixture is installed without alternatives. Its parsing/HIR
admission has **not** been executed by the producer. The focused primary run
must establish that premise before treating any logged output as an observation.

The test selects the three named local binders, follows their actual initializer
indices to Lambda occurrences, and authenticates the parameter IDs, source
positions, omitted annotations, FormalConstruction origins, lambda recipes,
raw domain rows and original domain Terms. Both Apply expressions are selected
from HIR, with `outer`/`identity` authenticated as those Local IDs and `cb`/`x`
as those Parameter IDs. Each retained ApplySourceInput is checked against its
source expression, callee/argument indices, checking occurrence and recipe.
No numeric row layout is assumed.

After normal same-session source execution, logs include each native Apply
interface and demand view, source admission RelationIds, formal constructors,
each retained Argument FunctionPort child/parent RelationId and their relation
keys, actual positive/negative Function Terms and views, and every immediate
Replay feeding that Function comparison, with **both** bound inputs and their
retained lower/upper RelationIds. Replay bound-pair consistency is checked;
this does not infer source identity from equal pair keys.

The receiving call's own Argument chain is labeled authenticated only if:

1. The existing bounded incidence reader authenticates the positive Function
   constructor as the source `outer/cb` constructor through actual retained
   FreshUse, optional Name handoff, Replay and FunctionPort dependencies, with
   `incidence.comparison == parent` for the FunctionPort currently inspected.
2. The immediate comparison Replay's upper bound can be traced through
   explicitly retained single-parent Derived/Transport edges to an origin
   with the exact receiving Apply checking occurrence.

Those traversed edges and the incidence transport witness are printed. The
test intentionally does not traverse multi-input Replay ancestry to attribute
the upper bound: such ancestry includes more than the negative supplier.
Unknown attribution is printed as unknown, rather than assigned by endpoint
equality, matching TypedPairKeys or a nonzero global Argument count. There is
no assertion that the authenticated-chain count must be positive. Assertions
authenticate constructors and retained dependency consistency, not a new
semantic expectation about successful reader coverage.

Other Function comparisons, including potential comparisons against the
`cb x` demand, retain their own records but are not counted as receiving-call
evidence. Their source attribution requires a separate authenticated chain.
The raw extrusion parent/copy records are printed with their polarity, target,
occurrence, sources and pair-only comparison record. They do not retain an
initiating contextual RelationId or a direct Function field path. Consequently
this harness cannot authenticate the earlier copying operation merely from
those records. The incidence reader explicitly excludes earlier extrusion;
reader failure does not mean protection was lost.

## Verification and observed result

Fresh compiler_referee review found one minor attribution-predicate issue:
the bounded reader can return a witness for another FunctionPort parent of
the same child. The batched repair requires the incidence's comparison to equal
the current FunctionPort parent before counting an authenticated receiving
chain. This same-comparison attribution check was integrated with no fixture or
scope change. The primary reran the exact focused test successfully after the
repair. This promotes no gate or status.

Producer check: `git diff --check` passed. The primary ran the exact focused
command below twice, before and after the minor repair; both runs reported
`1 passed; 688 filtered out`. No production files changed. Two Cargo processes
were used, with no broad suite or timing/resource measurement.

In this run, the bounded reader authenticated one Argument chain for the
receiving `outer identity` comparison through the original `outer/cb`
constructor. Later `cb x` Function comparisons were also observed. Their
Argument children returned no `candidate_formal_argument_incidence` result in
the bounded reader. One such comparison had an upper-bound `Transport` and
`Derived` chain ending at the exact source `cb x` Apply relation; another had
only a self-derived bound. This establishes a source-demand-to-consumer chain
for one later comparison, but it does not uniquely join the retained
extrusion Parent record to that relation: Parent stores only a pair key, and
no uniqueness check was added. The run therefore does not establish an
authentic relation→copy→consumer chain. The numeric `RelationId`s, terms and
rows are session-local observations, not fixed expectations.

The producer used one bounded pass, zero worker Cargo processes and zero
measurement samples. M1 used one fresh compiler_referee review; the primary
integrated its minor finding and reran the focused test. The bounded harness is
reviewed, not a proof or parent-gate closure.

Primary-owned exact command:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_receiving_call_records_authenticated_argument_dispatch -- --exact --nocapture --test-threads=1
```

The producer compared the live production dependency bytes against the frontier
inventory; all eight production source hashes matched. The test file started
from the frozen, already reviewed correlation-test baseline
`2d52f3f40fc0bcef76b946c9494e5dce3a4b9e8d0eb97f0ad2036b7303e365d0`.
The primary advanced HEAD to `493e6e9178e93c5d5d45ca141e5eb0b3a335ca45`
for the frontier/task checkpoint during this packet; it confirmed that the
production/test dependencies and frontier hash remained frozen.

Remaining evidence: independent adjudication of the observed receiving edge
and source-demand bound ancestry, and whether the pair-key-to-copy relation can
be authenticated uniquely in this session. No broader suite, copy-time
instrumentation, all-path transport, dynamic Receive/Observe, full Call,
soundness, principality or F5 cutover was verified. No source-profile matrix
or H1/H2/U closure follows.

Shared-record synchronization is deferred to the primary at `tasks/current.md`
and `tasks/research-lab.md`; they are outside the lease. The two leased files
are frozen for primary execution and independent review. No decision point
was resolved by this harness; a production retention change, if required,
needs a separately authorized packet at its actual owning constructor.
