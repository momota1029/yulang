# Retained-input indistinguishability

Date: 2026-10-10
Status: unreviewed conditional derivation and bounded source bridge; no readiness,
source soundness, or gate closure claim
Frozen baseline: `55a69231d0f2b16ce9611247775271a73779f0fe`, confirmed by the primary
Exclusive lease: this file only; leaf assignment, no delegation

## Objective and governing scope

Prove what a deterministic retained-evidence projection can distinguish, then
map its premises to the actual private candidate constructors and consumers.
The governing source is
[`contextual-attachment-admission-design`](../design/2026-10-10-contextual-attachment-admission-design.md)
§3 (exact identities and sharing), §4 (source construction and lifecycle),
§5 (complete components and late-edge invalidation), and §6 (bounded internal
gate, later admission exclusions). Attachment-set grouping is the selected
§3.1 decision. Neither this lemma nor the finite check changes those decisions.
Method and promotion boundaries follow `rules/agent-orchestration.md` “Proof
delegation and decomposition” and “Model routing and Astra escalation”,
`rules/research-lab.md` “Evidence quality and stopping unproductive loops”,
`rules/compiler-engineering.md` “Natural compiler behavior and proof-obligation
economy”, and `rules/git-concurrency.md` “Disjoint-file mode”.

## Frozen statement, quantifiers, and exclusions

Fix an original component/root sequence `R`, its source program, source owners,
lexical scopes, binders, endpoint and relation identities, and a readiness
question `Ready_R : S -> Bool` over a specified domain `S` of operational
states. Readiness is an input predicate here, not a newly adopted definition
of when the compiler may publish. Fix a retained-evidence map `E : S -> D`
and a deterministic projection `pi_R : D -> I`. Set
`f_R(s) = pi_R(E(s))`. No additional argument to `pi_R` observes the unfinished
producer frontier. Equality is equality in these fixed domains, without
independently selecting witnesses or renaming original identities.

**Conditional theorem T1.** For every `s,t in S`, if `E(s)=E(t)`, then
`f_R(s)=f_R(t)`, regardless of how their pending producer actions differ.

**Conditional corollary T2.** For every `s,t in S` with `E(s)=E(t)` and
`Ready_R(s) != Ready_R(t)`, there is no deterministic Boolean predicate
`d : I -> Bool` satisfying both
`d(f_R(s))=Ready_R(s)` and `d(f_R(t))=Ready_R(t)`.
If such a pair belongs to the source-reachable observation domain, no exact
readiness decider using only this input is correct throughout that domain.

Different pending actions alone do **not** supply T2's readiness inequality.
Also, one-sided safety `d(f_R(u))=true => Ready_R(u)=true` is insufficient for
the impossibility claim: `d=false` always satisfies it. T2 concerns a sound
and complete decision on both states. An `Incomplete`/unknown result is not
such a decision, and does not establish that the producer is unfinished.

These are abstract conditional claims. Excluded: existence of a
source-reachable distinguishing pair, an executable readiness decision,
authentic certificate minting, complete Call semantics, effect hygiene,
soundness/principality, negative concrete-row admission, and production cutover.

## Constructive derivation

For T1, substitute `E(t)` for `E(s)` in the application of the same function
`pi_R`. Congruence gives `pi_R(E(s))=pi_R(E(t))`.

For T2, name their common projected input `i` and its proposed decision
`b=d(i)`. Since the readiness values differ and are Boolean, one is true and
the other false. If `b=true`, the not-ready state is declared ready; if
`b=false`, the ready state is declared not ready. In either case one of the
required equations fails. This argument supplies an explicit failing state
for either possible decision; it assumes no model search or compiler
transitions. The necessary condition for an exact retained-input decision is
that readiness be constant on each input fiber.

The original broader wording has two minimal obstructions: two different
pending actions may both be unfinished; and an always-defer recognizer is
one-sided safe even for a readiness-different pair. Neither obstruction
weakens T1 or changes the selected compiler contract.

## Exact source bridge

All locators below refer to the frozen source snapshot recorded below.

| Owner / consumer | Established code fact | Bridge limit |
| --- | --- | --- |
| `candidate_context.rs:393`, `State::retained_input` | Arguments are `&self`, ordered `roots`, all effect `views`, and all intrusion `parents`. No `candidate_source::Plan`, remaining-action slice, action cursor, or source executor is an argument. | Signature separation is not a proof of independence on the reachable state space: retained facts could encode frontier information through an invariant. |
| `candidate_context.rs:402–541` | Closure follows relations, contexts, weights, endpoint views, bound registrations, ordered replay operands, and transport witnesses; it validates retained origins and incidences. | Stored bounds and incidences do not establish activation, complete replay, or absence of future producers. |
| `candidate_context.rs:280–331` | `RetainedInput` borrows `State`, roots, views and parents. Accessors preserve retained identities, ordered records and shared context handles. Entire views/parents slices are exposed, including unselected elements. | Equality of only selected graph adjacency is too weak for T1's source premise. The type has no `Eq`; pointer identity is not content equality. |
| `candidate_context.rs:539–542` | Every successful call appends `FilterObligationsUnavailable`, `ProducerReadinessUnavailable`, and `DependentObservationsUnavailable`, and returns `Incomplete`. | This reports absent evidence. It is neither a negative readiness decision nor an unsafe readiness certification. |
| `candidate_source.rs:8–29,144–475` | `Plan` owns source schedules and loose actions. `emit_candidate_source` appends facts/recipes and `Action` records, finally inserts the root schedule. `Lambda` is scheduled at 434; `Candidate` Apply at 386; annotation/ascription actions likewise defer their constructors. | Collected source occurrence/recipe existence is not execution of its action. |
| `candidate_source.rs:537–576` | Loose/root execution temporarily takes/removes actions, visits them sequentially, then restores the same vector even on an error result. Dispatch calls actual admission/annotation/routing/install owners. | A nonempty restored schedule is not a remaining-action frontier. The current loop position is local control state; there is no stored completion cursor in `Plan`. |
| `lib.rs:11121–11215`, `admit_lambda_fact` | Executing a Lambda creates entry/return rows; slot 3 retains its authentic inferred-entry origin and submits the constraint. `candidate_context.rs:762` stores that record at the owner. | This proves a concrete future producer can add retained evidence; it does not produce the equal-evidence, different-readiness pair. |
| `shadow_apply.rs:1300–1415`, `admit_candidate_fact`; `candidate_scheme.rs:1108` | Apply constructs its Function demand/native interface and submits a live constraint; a Link records provenance and calls `constrain_live_value`. | Construction after scheduling can change graph/solver evidence. Native submission alone does not certify complete Call meaning. |
| `lib.rs:11814–11860` | Constraint execution seeds context, enqueues the initial item, drains work, and settles intrusion when the queue empties. | Local worklist quiescence during one action does not mean all later source actions are complete. |
| `candidate_scheme.rs:679–753`, `execute_candidate_graph_plan`; `lib.rs:13831` | The candidate branch executes all member schedules before capturing/publishing their staged graphs. | This control-flow ordering may supply a safe observation boundary without recovering readiness from `RetainedInput`. It is not a retained readiness certificate. |

For the bounded content bridge take `E(s)` to include the complete immutable
`State` contents and lookup relationships, the ordered roots, and complete
views/parents contents, with all IDs, occurrences, binders, owners and scopes
held equal. This stronger premise avoids projecting away attachments, origin
fibers, transports, or exposed unselected slices. Successful calls produce
equal semantic masks, accessor streams and ordered gap lists:

1. Equal lengths create equal zero masks. Roots select equal bits.
2. Each scan reads equal ordered vectors and equal map lookups. Matching
   conditionals select equal bits and set equal validation flags.
3. Masks are monotone: every successful `changed` pass sets at least one of
   the finitely many bits from zero to one. With `N` total mask slots there
   are at most `N` such passes, followed by an unchanged pass.
4. Induction on passes gives identical masks and exit points. Remaining
   validation reads equal payloads. The ordered gap pushes therefore agree.
   The borrowed accessor streams agree extensionally by their equal payloads
   and selectors.

This argument covers the successful semantic content of the actual closure,
including missing-reference/inconsistent-reference gap paths. Allocation
failure is a separate `Err` outcome. It does not prove allocator success,
capacity reproducibility, address equality, timing equality, or equality of
`owned_bytes()` (which exposes vector capacities). A theorem about every raw
Rust-observable predicate needs those physical observations included in `I`
and equality established for them, or the original full deterministic
projection hypothesis supplied independently. This note asserts only the
content bridge for predicates extensional in the specified semantic content.
It does not silently equate raw borrowed objects.

Static search of `crates/yu-solver/src` found `retained_input` calls only in
`candidate_context_tests.rs`; the owning method is allowed dead code for a
later certificate consumer. Those test constructors were inspected but not
run. No present source recognizer making the forbidden decision was found.

## Missing source-reachability premise and next evidence

The missing premise is a pair of **legal source-generated observation states**
at the relevant certificate query boundary, sharing every retained input
observation, with different readiness for the same original `R`.
Showing merely that scheduling is stored elsewhere does not discharge it.
A complete witness must supply both source derivations/control paths, preserve
the original scopes and IDs, identify the precise unperformed action affecting
`R`, and show that one state meets the selected completion/lifecycle condition
while the other does not. The query boundary itself needs an actual owner:
the current retained-input API has no live source consumer. Arbitrarily
modifying a `Plan` beside a cloned context is not such a witness.

There was one direct proof route and one finite consistency check, not two
failed alternative attempts at reachability. No repeated-model route is
proposed. Under the existing obligation-economy audit, premature certification
is A (correctness); trying to infer a hidden executor position from retained
graph shape is potential D (reconstruction debt). The source executor already
knows which action/member is executing and when all schedules return. The
primary should next locate the intended observation boundary and ask its owner
to retain or establish the selected readiness evidence there. Whether that
requires a new record or a construction invariant is not decided by this note.
The classification neither closes a gate nor authorizes an implementation.

## Finite proof check

The following supplied model enumerates all four deterministic projections
from two retained values to two input values and all four Boolean predicates
on those inputs. Its four states independently combine retained value and
readiness frontier. It verifies T1, rejects exact readiness for all 16
projection/predicate combinations, and exhibits the one-sided-safe fallback.
An additional pair checks that distinct pending actions may share readiness.
It models neither source scheduling nor source reachability.

```python
from itertools import product

states = tuple(product(range(2), range(2)))
ready = lambda s: s[1] == 0
projections = tuple(product(range(2), repeat=2))
deciders = tuple(product((False, True), repeat=2))
equalities = decisions = sound_only = 0
for pi in projections:
    f = lambda s: pi[s[0]]
    for s in states:
        for t in states:
            if s[0] == t[0]:
                assert f(s) == f(t)
                equalities += 1
    for d in deciders:
        exact = all(d[f(s)] == ready(s) for s in states)
        sound = all(not d[f(s)] or ready(s) for s in states)
        assert not exact
        sound_only += int(sound)
        decisions += 1
    assert all(not (False, False)[f(s)] or ready(s) for s in states)
pending_a, pending_b = ("edge_a",), ("edge_b",)
assert pending_a != pending_b
assert bool(pending_a) == bool(pending_b)
assert (equalities, decisions, sound_only) == (32, 16, 6)
print("PASS: 32 equal-input comparisons; 16 exact decisions excluded; "
      "6 one-sided-safe combinations; pending difference insufficient")
```

Execution command: extract this file's single Python block in memory and
`exec(compile(block, path, "exec"))` using `PYTHONDONTWRITEBYTECODE=1 python3`
on stdin. No additional file, build, test runner or compiler execution is used.
Result: PASS, 32 equal-input comparisons, all 16 exact decision combinations
excluded, 6 one-sided-safe combinations. All nine recorded dependency hashes
were unchanged at freeze; the leased note had no trailing whitespace. One
Python process used 0.0036 seconds measured check wall time, 0.0228 seconds
process CPU time, and 17,280 KiB peak RSS. No tests, builds, source execution,
Oracle run, benchmark sample, or extra research output ran. These counts prove
only the enumerated supplied model; source reachability remains unverified.

## Frozen dependencies and handoff

SHA-256 of source bytes inspected:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `470a5d45b6a7d6d2faf55de388908fc6b724dac7a14af87a3ff67a227b975ac5` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `290f25d1a5a12c6911623bbf9b267983b8ed3ff2a290b678ca115e448ef907fe` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

Requested normal runtime: `gpt-6.1-sol` / `high`; role file leaves model/effort
unpinned and `.codex/config.toml` supplies those subagent defaults. Effective
runtime model/effort metadata is unavailable to this leaf: observed unknown.
No escalation or subagent launch occurred. The primary remains verification
and integration owner; this leaf performs only the bounded abstract check.
Workflow nonconformance: the leaf used read-only `git rev-parse HEAD` to resolve
the baseline despite the no-Git packet. No Git mutation occurred; the primary
was notified and confirmed the SHA. Subsequent checks use file hashes only.

Commit packet: sole changed path is
`notes/progress/2026-10-10-retained-input-indistinguishability-proof.md`;
baseline is the SHA above; all nine recorded dependency hashes were unchanged
at freeze;
claim status is conditional/unreviewed research, no producer self-certification.
Proposed checkpoint message: `research: derive retained-input indistinguishability condition`.
Proposed shared-record delta for the primary/curator: record T1 and T2 as
conditional, distinguish Incomplete from a readiness decision, and keep the
source-reachable readiness-different pair and producer-authenticated input
gate open. No shared records were edited.
