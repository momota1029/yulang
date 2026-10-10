# Certificate generation: mutations outside relation/dependency insertion

Status: frozen, unreviewed research characterization and conditional falsifier.
No implementation authority or gate closure.

## Objective, authority and baseline

Test the proposed interpretation of Authoritative contextual admission §5:
certify a complete currently generated component before all source schedules
finish, provided every subsequent relevant mutation withdraws dependent results
before reuse. Attack only a proposed generation that changes on **new relation
or dependency insertion**. This is a candidate assumption, not existing code.

Baseline: `b92f965e7d8c2035b0456e882673e8cc8852dff9`.
Governing source: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§4 (retained origins, capture, rollback), §5 (per-contribution/origin count
relations; complete component, registrations, sharing and dependent observations;
dirty/withdraw/recertify/defer/rollback), §6 (bounded two-cycle gate).
Accepted decisions: exact unbounded contexts for the two reviewed shapes;
retain unsupported late edges and privately defer; no source rejection rule;
attachment grouping is per exact annotation occurrence (§3.1). The retracted
callback result remains unspecified. No selected language meaning is changed.

The primary owns theorem construction, review, authority and Git. This lane
uses source mutation inspection, not another cycle algebra or readiness proof.
Read `research-lab`, `design-authority`, `git-concurrency`, orchestration rules
and the `yulang-proofs` skill. Exclusive lease is this note.

## Decisive uncovered mutation

`candidate_context.rs:1614`, `candidate_context_seed`, interns `(canonical
typed pair, source context)`, then unconditionally appends an `Origin` with
the exact `ConstraintOccurrenceId` and optional inferred-entry handle.
`State::relation` (`:1418`) returns the existing ID on a cache hit. The seed
does not call `State::dependency` (`:1445`). Thus a new source incidence can
change a certificate premise without inserting either kind of graph record.

This premise is actually exposed: `CircuitEvidence::origins` (`:305`) selects
all origins belonging to included relations. §5 explicitly requires a count
relation per contribution and origin. A generation advertised as complete for
that retained evidence cannot infer unchanged origin coverage from unchanged
relation/dependency IDs.

### Minimal state trace

Hypotheses: a canonical relation `r=(p,I)` exists; its source origin set contains
`o1`; a certificate `K_g` claims the complete selected origin set for `r`; `o2`
is a distinct source incidence that the consumer considers relevant. The naive
epoch changes only when relations/dependencies are inserted. No row
representative change occurs in the traced seed.

1. Freeze `K_g` and a dependent observation `O_g=origins(r)={o1}`.
2. Seed the same task `p` with occurrence `o2`. `relation(p,I)` returns `r`.
3. The seed appends `Origin(r,o2,None)`; relation/dependency sets and epoch `g`
   remain unchanged. The actual selected origin set is now `{o1,o2}`.
4. Reuse `O_g` using only the unchanged epoch. Its purported complete set is
   stale. No newly inserted edge exists to trigger the naive withdrawal hook.

The trace needs one relation and one additional origin, no dependency, context
operator, Function or recursive cycle. `O_g` is a discriminating hypothetical
projection, not an implemented compiler observation or output oracle.
Removing the second origin or requiring a new relation removes this witness.

### Ordinary source ordering, separately from cycle membership

Existing fixture spelling supplies a source-owned repeated-pair case:

```yulang
my answer = (1 as int) as int
```

The child is retained at one Value row `v`. Both ascriptions emit slot-45
`v <: IntNegative` and slot-46 `IntPositive <: v`, with distinct occurrences.
Construction locators:

- `candidate_source.rs:388`: ascription action uses the child's computation
  mapping; `:549` executes its source action.
- `candidate_effect.rs:1051`: ascription uses the same child endpoint on both
  annotation directions; `:1059` emits `[45,46,47]`; `:1234` maps written `int`
  to the fixed positive/negative integer leaves.
- `candidate_scheme.rs:1108`: records the exact occurrence and submits the
  Value constraint; `lib.rs:11814` clears processing, seeds before enqueueing,
  and runs the live worklist.
- `candidate_context_tests.rs:1757`: retained regression source asserts two
  distinct ascription occurrences, a shared child row and those endpoint
  orientations. Read only; it was not rerun here.

Take a hypothetical certification point immediately before the outer slot-45
seed, after all earlier graph insertions. The inner slot-45 relation already
exists, and this exact seed changes its selected origins without new graph
records. Identity execution does nothing (`candidate_context.rs:1807`);
initial enqueue has cleared processing, so admission adds no parent dependency.
For an already completed canonical relation, `pair_is_current`
(`lib.rs:11354`) can take the ordinary duplicate path (`:11881`) after the
origin append. Reusing that ordinary semantic memo is not itself a defect:
the new occurrence repeats the same integer check.

This establishes source producer ordering by direct construction inspection.
It does **not** establish that this source forms either approved Effect cycle,
that `K_g` is currently built at that point, or that a certificate-derived
acceptance/publication is stale. Those are distinct unsupplied hypotheses.
To instantiate this trace inside an approved circuit, show that a repeated
source incidence of an included relation belongs to that circuit's certified
origin/observation set. No such full source circuit was claimed here.

## Other exact mutation owners

These corroborate the need for a dependency-complete mutation contract; they
are structural/event-order evidence, not additional minimized source failures.

| Owner | Mutation without its own relation/dependency insertion | Premise/observation affected |
| --- | --- | --- |
| `candidate_context.rs:2028`, `candidate_context_fresh_bundle` | Links a copied attachment bundle to an already admitted child; its body calls no `relation`/`dependency` | `CircuitEvidence::bundle_incidences` and `bundles`; exact source attachment incidence |
| `candidate_scheme.rs:1028` | Actual fresh-use path calls that link **after** `candidate_context_fresh_transport` has admitted the relation/dependency | A hook at the earlier graph insertion precedes complete fresh-use bundle incidence |
| `candidate_context.rs:1546`, `attach` | Appends a new bound-key/relation incidence using an existing ID | `CircuitEvidence::bounds`; retained-input bound/view closure and replay inputs |
| `candidate_context.rs:1862` | Marks a checked relation discharged after filter callbacks finish | `post_check_context` (`:1560`) changes from retained context to Identity without changing `RelationKey` |
| `candidate_context.rs:1539`, `replay_progress` | Journals changed replay cursors independently of graph insertion | Which replay fibers remain pending; any completion assertion that depends on those cursors |
| `candidate_context.rs:1081`, `rollback` | Restores origins, incidence, discharge and replay cursors independently of relation/dependency lengths | Route lifetime and generation restoration; IDs alone do not authenticate restored auxiliary state |

Calling `relation` on **every** seed and bumping an epoch even on a hit would
catch the origin case if invalidation happens before the append and no
certificate query intervenes. That is a different candidate than an
insertion-only epoch. It still needs an argument for the separate bundle,
bound, filter and rollback owners. Source-reachable insertion order is shown
for fresh-use bundles; interleaved certificate querying remains hypothetical.

## Claim class, independence and limitations

Established bounded source characterization: the listed owners mutate retained
evidence beyond graph-record identity, and repeated source ascriptions supply
the origin append on an existing canonical relation. Conditional falsifier:
insertion-only generation is insufficient **when a complete certificate and
its dependent observation include that changing evidence**. The broader
early-snapshot interpretation remains conditional on complete invalidation;
this result does not refute it.

No executable model or oracle was used. The evidence is direct producer and
consumer-accessor inspection, with a preexisting fixture as a locator rather
than executed verification. The hypothetical observation directly projects the
changed source state; it shares the stated relevance/completeness premise with
the certificate and proves no language semantics. Current `retained_input`
always retains `ProducerReadinessUnavailable` and
`DependentObservationsUnavailable`; there is no live certificate consumer to
run or falsify. Pure source membership in the two approved recursive Effect
classes, all filter/recipe/family cases, observation withdrawal, publication,
allocation failure and rollback/retry of new certificate state remain open.

Stopped at the decisive uncovered origin event; no second equivalent model or
enumeration was attempted. No seeds/ranges, model mutations, Cargo, builds,
tests, formatting, Git mutations or child agents. Read-only `rg`, bounded
`sed`/`cat`, `git rev-parse/status/diff/show` and one Python SHA-256 comparison
were used. Checks establish locator and dependency stability only. Peak RAM,
CPU seconds and exact elapsed wall time were not measured; all tool processes
were lightweight and sequential, except the initial bounded independent reads.
The packet supplied no numeric resource budget; no heavy work was inferred.

Recommended next action: the primary should require the certificate query
contract to enumerate and dirty-before-reuse source-origin, attachment/bound
incidence, discharge and dependent-observation mutations, or demonstrate that
each omitted event is irrelevant to that exact certified projection. Then
instantiate the one-origin trace in a complete approved circuit if needed.

## Dependency snapshot and commit packet

SHA-256 of baseline bytes; live bytes matched at the pre-write recheck:

```text
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337 crates/yu-solver/src/candidate_context.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e crates/yu-solver/src/candidate_effect.rs
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0 crates/yu-solver/src/candidate_source.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11 crates/yu-solver/src/candidate_scheme.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
d543106be87d47cb0c06799e6c543cc7b7b414cffbfc224aa2c5bb07d0d83647 crates/yu-solver/src/candidate_context_tests.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1 crates/yu-solver/src/lib.rs
```

- Exact leased/changed path:
  `notes/progress/2026-10-10-certificate-generation-falsifier.md`.
- Baseline: `b92f965e7d8c2035b0456e882673e8cc8852dff9`.
- Changed dependency hashes: none at the recorded recheck.
- Review: unreviewed; producer performed no independent certification. Frozen
  on submission; primary owns recheck/integration.
- Checks already run: source/accessor/caller inspection; baseline/live byte
  equality for the eight named dependencies; HEAD matches the pinned baseline.
- Proposed commit message:
  `research: expose certificate origin mutation outside graph insertion`.
- Shared deltas left to primary/curator: link this bounded origin-coverage
  falsifier in Packet 1's contract discussion; keep readiness, approved-cycle
  source applicability and transactional certification open. No shared task,
  theory, index, authority or question-board file was changed.
