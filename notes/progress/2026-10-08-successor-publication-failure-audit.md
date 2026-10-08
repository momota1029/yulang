# Successor publication and failure audit

Date: 2026-10-08
Pinned baseline: `a38551e9525bf8f079a9ced24f312282c934b46d`, branch `research/simple-sub-intrusion`
Claim class: compiler-referee-reviewed source-level lifecycle characterization
and conditional control-flow derivation. Research only; no successor theorem,
semantic adoption, production approval, performance verdict, or closed gate.
Lease: this file only. Artifact frozen when submitted to the primary.

## Objective, authority and premises

Trace the current F5 owner, SCC finalization/installation, incoming routing and
failure boundaries to isolate the engineering obligations needed when replacing
F5. This continues the resource audit's publication/failure seam; it does not
repeat its complexity analysis or choose a successor representation/export root.

Governing sections: `rules/design-authority.md`, “User-selected product priorities
(2026-09-24)” (accepted-input invariants and atomic publication) and “Natural
compiler behavior and proof-obligation economy”; redesign charter §§1–3, Gate D,
Gate E and §12 (F5 replacement, all-member visibility, deterministic complexity
rejection without partial SCC results); F4 design §§7–10 (lifecycle, sole scheme
authority, provenance and whole-attempt availability failure), within its
Integer/resolved-Name scope; static-session design §§4–5 (ordering and consuming
failure boundary). `rules/performance.md` “Measurement decision” applies: this
read-only audit has no timing-dependent decision. The charter's soundness,
principality and final well-typed-program acceptance priorities remain in force.

The F4 and static-session locators are respectively
`notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` and
`notes/design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md`.

The pending Generalize export-root question `successor-generalize-root-policy`
revision `q1` supplies no approved root choice. Neither option is assumed here.
F4 supplies infrastructure in its scope; it does not prove Function/effect
generalization. F5 Q/R layout, representative facts and closed-scheme formatting
are current implementation observations, not successor equivalence requirements.

The control-flow derivation assumes the inspected safe Rust executes according
to its ordinary ownership/control-flow semantics; the frozen collected plan has
total, unique member/use/root mappings; no hidden callback exports private
session state; and an `Err` from consuming `run` is propagated. It does not
assume F5's constraint rules are source-sound. Allocation abort, stack exhaustion,
process termination, undefined behavior and uninspected unsafe dependencies are
outside this derivation. No deterministic successor resource limit is selected.

## Owners and visibility boundaries

| Owner / exact source locator | Retained responsibility / boundary |
| --- | --- |
| `SccPlan::build`, `crates/yu-solver/src/scc.rs:212`, partition at 423 | Same-component uses enter that component's `internal_uses`; external uses enter the target component's `incoming_uses`. `components_in_dependency_first_order` at 674 supplies frozen order. Full partition correctness is an input premise here. |
| `ConstraintBatch` and `InferenceSession::try_new`, `lib.rs:9402` | Frozen recipes/identities translate once into live rows. `InferenceSession` at 7419 privately owns bounds, levels, term store, diagnostics, routes, scheme slots, finalization capability and scratch. |
| `InferenceSession::run`, `lib.rs:9969` | Consumes the attempt: collected admission → SCC execution → store accounting → consuming `finish`. Every returned availability error exits before `SolvedModule` construction. |
| `execute_scc_plan_inner`, `lib.rs:13135` | Per component: internal routes → all member generalization drafts → normalization → all-drafts barrier → finalize every member into private `self.drafts` → install every member slot → incoming uses. |
| `component_generalization_draft`, `lib.rs:15475` | Reads the exact member's collected root/live row and builds through `F5cGeneralizer::with_memo`; common `frozen_bound_epoch` is component visit number. Semantic generalization correctness is not proved here. |
| `ClosedTypeFinalizationSession::finalize_scheme_inner`, `yu-types/src/lib.rs:2457` | Per member: build scratch, validate, plan, reserve, commit. `CommitRollback` at 2090 truncates appended arena lanes if commit exits before `committed = true`. |
| installation loop, `yu-solver/src/lib.rs:14154` | Validates member/root/dense position through `verified_scheme_definition` at 15713; replaces exactly one empty slot per member. `SchemeInstall` resource sampling follows each replacement and can fail. |
| `route_internal` / `route_internal_inner`, `lib.rs:14253` / 14258 | Connects the target's existing live root row to the use row through `with_route_transaction`. It does not read a finalized scheme or freshen internal uses. |
| `route_incoming` / `route_incoming_inner`, `lib.rs:14942` / 15162 | Reads installed target scheme, instantiates into use-level rows, routes under a mutation journal, and then performs outer accounting/evidence handling. |
| `finish`, `lib.rs:15740`, public construction at 15970 | Builds projections privately, checks resource/accounting state, consumes finalization into the closed arena, clears instantiation scratch and only then returns `SolvedModule`. No public SCC lifecycle query exposes intermediate slots. |

The production `boxed_component!` path is selected under `cfg(not(test))` at
14145. The alternative flat candidate is `cfg(test)`; its implementation is
outside this audit's correspondence claim. In production, all member
finalizations succeed before the first durable scheme-slot replacement. The
barrier event/counter at 13497 marks all normalized drafts available, rather
than public publication. Private schemes can then be installed sequentially.
Incoming routing starts only after the complete installation loop at 14196.

Shadow origin evidence is also staged: member origin lists stay component-local
until installation completes, then extend session-private capture at 14191.
`solve_with_shadow_fresh_capture` at 16032 still ends in consuming `session.run`.
No shadow capture result escapes an unsuccessful consuming solve in this path.

## Failure behavior and exact qualifications

1. **Draft or member finalization error.** `finalize_generalization_draft_raw`
   at 15522 rejects unresolved `Variable`/`Shared` nodes and invalid Q/R ordinals,
   then uses the typed finalizer. Exhaustion maps to `IdentityExhausted`;
   `InvalidDraft` is a compiler panic through `map_finalization_error` at 9775.
   Earlier successfully finalized members can remain in private draft/arena
   state, but installation has not started. There is no component rollback of
   those successful earlier finalizations. Public `run` disposal is sufficient
   for outward atomicity.
2. **Per-member finalizer commit.** The commit guard covers logical arena
   appends before commit success, including unwinding. `finalize_scheme_inner`
   catches then resumes panic; it does not convert a panic into semantic
   success. Capacity can survive failed reservation. Moreover,
   `reconcile_capacity_state` runs *after* `commit()` at 2564: a terminal
   accounting error can occur after arena appends are committed but before a
   scheme handle is returned. The exhausted finalization state cannot finish
   successfully. This is a private terminal-state boundary, not a guarantee
   that every failing call leaves arena lengths unchanged.
3. **Installation or later-component error.** A `SchemeInstall` sample can
   return `Err` after a slot was filled. Previous members/components and routes
   are not unwritten by `execute_scc_plan`; its error wrapper performs only
   test-ledger cleanup. Private partial SCC slots are therefore possible by
   control flow. The enclosing consuming solve returns no module. Reusing this
   failed session would need a new rollback/terminal-state contract.
4. **Inner route error.** `validated_route_use` at 15445 checks exact use-cause
   equality before route mutation. `with_route_transaction` at 8947 commits
   only inner `Ok`; inner `Err` invokes `rollback_route_transaction` at 9064.
   The inspected journal restores touched old rows and levels/marks; truncates
   new rows, routes and errors; removes new typed-pair/reported-error keys and
   the route marker; resets the store fact/provenance/receipt state; rolls back
   term construction; and clears work/diagnostic scratch. Surviving capacity
   and peak/event accounting are intentionally retained. This inventories the
   rollback, but is not a completeness proof that every mutation site journals
   before writing. Accounting during rollback can itself fail after logical
   restoration; whole-attempt disposal still prevents a public partial result.
5. **Outer route error after inner commit.** `route_incoming` obtains its
   transaction result at 14960, then records scratch resources and samples.
   These outer checks can fail after the journal has committed an inner `Ok`.
   They restore some counters/pending scratch requests, not the successful
   route's semantic state. The outer returned error therefore does not imply
   route rollback. `execute_scc_plan` propagates that error, so no public
   module escapes. This is another precise obstacle to treating the private
   route method as a reusable all-or-nothing API.
6. **Finish failure.** Projection allocation precedes closed finalization
   `finish`; both pre/post-finish resource checks precede public construction.
   Failure disposes the attempt even when all SCC slots were populated. Some
   allocations use `Vec::with_capacity`/collection rather than fallible reserve;
   this audit does not establish graceful handling of arbitrary allocator
   failure or a supported depth limit.

`SolveAvailabilityError` at 3845 remains `ArtifactMismatch | CauseMismatch |
ReceiptMismatch | IdentityExhausted`. `CrossKind` in collected admission at
10761 and `IncompatibleValue` through `report_incompatible` at 12618
are local retained diagnostics: successful `SolvedModule` does not imply an
error-free or well-typed input. No SCC Failed/Blocked semantic outcome is added.
Successor inference-complexity rejection must retain the charter §12 distinction
from typing failure; current `IdentityExhausted` does not establish that future
observable contract.

## Conditional derivation and smallest distinguishing traces

Let `I(c)` be the installation loop for component `c`, `X(c)` its incoming loop,
and `P` the only inspected public `SolvedModule` construction. With the premises
above: every entry into `X(c)` follows completion of `I(c)`; every `P` follows
successful SCC execution and finish; an availability error before `P` exits
consuming `run`. Hence no incoming use observes a proper subset of installed
members, and no failed consuming solve returns partial SCC results. This is
control-flow/ownership evidence for **visibility atomicity**. It does not prove
an indivisible SCC write or a resumable failed-session transaction.

The smallest source fixture already present for multiple members is
`my left = right; my right = left`. Its existing test
`f5b_finalization_availability_exhaustion_returns_no_module_or_final_counter_work`
at 18659 injects failure after one successful finalization and asserts one
private draft, no installed schemes and no public result. The optional-shadow
test at 18628 makes the analogous empty-origin assertion. These tests were
read, not run; their injection assumes the given failure point and does not
prove an actual allocator/overflow path.

For the different claim “any error leaves all private member slots empty,” the
minimal distinguishing **conditional control-flow trace** needs two members:
finalize both → replace slot 0 → `SchemeInstall` sample returns exhaustion →
exit with slot 0 populated, slot 1 empty and no incoming use. The sample's
arithmetic-overflow branch is implemented by `ResourceSampleChecked::finish`
at 344; no concrete ordinary-input overflow witness is claimed. This trace
refutes deriving private transactional rollback from the placement of `?`
alone; it is not an executed counterexample to accepted-input safety.

Incoming instantiation separately establishes the current identity mechanism:
`instantiate_and_route_closed_inner` at 14795 creates fresh rows for Q/R at
`use_level`, restores recursive bounds and uses the same substitution for
predicate expansion. Internal routes retain live root sharing. `route_many`
at 14406 constrains every normalized union member before recording one
representative public fact/route. Neither this first-member projection nor the
Q/R inventory proves successor full-relation/evidence transport.

## Successor obligations and limits of evidence

Retain or prove one owner for each member/use/root identity and authoritative
published payload; complete same-SCC live sharing; independent fresh incoming
instances with fixed captures remaining shared; transport of the entire selected
relation, scope, dependencies and symbolic typed-family/effect evidence; and an
all-member visibility barrier before incoming consumers. Public observers must
receive only a validated frozen result with its matching arena/evidence.

Choose a successor failure ownership boundary explicitly. A consuming private
attempt can preserve outward atomicity while containing partially staged state.
An incremental/retry API would additionally need terminal-state enforcement or
complete rollback across finalization, installation, outer accounting, routes
and evidence. Every deterministic limit must reject before unsafe work or
visibility and publish no truncated relation/result. Neither option is selected
by this note; they are consequences of whichever API the approved design uses.

No independent Oracle execution or reference evaluator was used. Source and
test inspection share the same F5 implementation, frozen plan and injected
transition assumptions. They do not independently validate source typing,
acceptance, principality or effect transport. No random seeds/ranges, mutation
experiments, tests, builds or measurements were run. Uninspected scope includes
full SCC planner proof, every journal mutation callsite, lower term-arena undo
internals, callback/dependency unsafe audit, full generalizer correctness,
feature-specific shadow application behavior, test-only flat candidate,
source-to-successor bridge, malformed-input/resource-limit completeness and
allocator/stack failure behavior. There were no failed executable searches.

Recommended next evidence step: after the source Generalize/export rule is
approved, freeze one successor lifecycle specification that names its owning
payload and observer boundary, then independently audit every mutation and
fallible operation against that boundary, including a post-install failure and
a post-inner-route-commit accounting failure. Do not infer closure from F5's
existing second-finalization fixture.

## Checks, dependencies and commit packet

Independent compiler-referee review found no blocking, major, or minor issue.
The review confirms the visibility/rollback distinction within this note's
stated source and API scope; it does not certify successor behavior or full
journal completeness.

Read-only commands: targeted `rg -n` function/branch searches, `sed -n` source
slices, governing-document reads, and `sha256sum` of frozen direct inputs.
No Cargo commands, tests, formatting, Git operations or benchmark processes.
Commands ran as short source-reading processes; no heavyweight CPU/RAM use.
Peak RSS and aggregate wall/CPU time were not measured; no numerical task
budget was provided beyond the explicit no-experiment restriction.

Direct input SHA-256 snapshot (recheck before integration):

```text
236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2  crates/yu-solver/src/lib.rs
a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5  crates/yu-types/src/lib.rs
3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8  crates/yu-solver/src/scc.rs
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
4b4c20ce527c52601313e7e33205b1a8967bb3f89e76206da11976bad74bd7d0  notes/progress/2026-10-08-successor-structural-resource-audit.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
4ca1a5cdde1007bfe37a1dc0e45c77890953a69400bec7067b15cceec58dbf29  rules/performance.md
7ec6ae3b8ea4048d0407388b23665092a121a3720f8658055dfb5e1046a09c25  notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md
d5bc6defbd13ac4f632ab1a4973dfcc77deb87f2f2236f715e31340a73bd4eaf  notes/design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md
```

- Exact leased/changed path: `notes/progress/2026-10-08-successor-publication-failure-audit.md`.
- Baseline SHA: `a38551e9525bf8f079a9ced24f312282c934b46d` as supplied by the
  primary; no Git query performed.
- Dependency hashes changed by this worker: none. A second `sha256sum` capture
  matched every listed input before artifact submission; no dependency drift
  was observed in that snapshot.
- Review status: compiler-referee review clean in the bounded lifecycle scope;
  no gate completion claimed.
- Checks already run: source/contract control-flow inspection and dependency hashes;
  no tests/builds/measurements.
- Proposed commit message: `research: characterize SCC publication and failure boundaries`.
- Shared-record deltas intentionally left for primary/curator: link this audit
  from the current Gate D lifecycle/resource record; retain engineering lifecycle
  obligations as open; record outer post-commit accounting and installation
  errors as successor audit cases. No task/index/authority/theory/question bundle
  was edited.
