# Packet 1 source schedule boundary and readiness

Date: 2026-10-10
Status: independently reviewed source control-flow derivation and minimized
readiness obstruction; research only, no Packet 1 closure or implementation
authority
Frozen baseline: `3a0bcb240896669718042dd0ee1cc5c89e9723d5`
Branch: `research/simple-sub-intrusion`
Producer: `/root/packet1_readiness_proof`, single prover leaf; no delegation
Exclusive output lease: this file only

## Objective, authority and method

Trace the actual source schedule constructor, action dispatcher, component
executor, capture consumers and publication owner. Derive only implications
justified by their Rust control flow. Separately assess whether that evidence
establishes ProducerReadiness for an exact circuit-certificate query.

Authority is [contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§4–7: exact retained construction, complete generated components, dependency
and observation invalidation, transactional rollback, and the bounded two-cycle
gate. Its §3.1 preserves the approved exact-occurrence attachment grouping.
The current task anchor is `tasks/current.md:8013–8037` and its latest Packet 1
next action at `:8130`. These records keep readiness and lifecycle-authenticated
inputs open. Prior evidence is
[retained circuit evidence boundary](2026-10-10-retained-circuit-evidence-boundary.md)
and [retained-input indistinguishability](2026-10-10-retained-input-indistinguishability-proof.md).
The former is an inert-evidence sub-slice; the latter is a conditional result,
not a source-reachable readiness-separation theorem.

Method boundaries follow `rules/agent-orchestration.md` “Proof delegation and
decomposition” and “Model routing and Astra escalation”, `rules/research-lab.md`
“Evidence quality and stopping unproductive loops”, `rules/compiler-engineering.md`
“Natural compiler behavior and proof-obligation economy”, and
`rules/git-concurrency.md` “Disjoint-file mode”.

## Frozen literal claim, scopes and exclusions

The assigned candidate claim is preserved literally:

> For one component M in candidate_scheme::execute_candidate_graph_plan with
> candidate_source.active=true, reaching first capture_candidate_graph implies
> execute_candidate_source_root returned Ok for every member root in M; each
> successful call iterated the root's complete fixed Action slice and each
> action returned Ok. An action error exits before capture/publication.

Fix one invocation `I` of `execute_candidate_graph_plan` and one iteration for
the original definition-SCC component identifier `M`. Let
`members_M = [m_0, ..., m_(k-1)]` be the exact ordered vector copied from
`batch.scc_component_members(M)` at `candidate_scheme.rs:690–697`. For each
position `i`, let `r_i = batch.definitions[m_i.ordinal()].root`. Preserve those
original member/root identities, source owners, occurrences, lexical scopes,
binders, attachment identities, provider/witness identities and residual
lineages. No independent witness selection, quotienting or alpha-renaming is
used. The theorem below quantifies every position in this vector; it neither
assumes nor requires distinct roots. If `k=0`, no first member staging capture
exists and the implication's antecedent is false.

For a call of `execute_candidate_source_root(r_i)`, `A_i` denotes the complete
vector removed from `schedules[r_i]` in that particular call. “An action returned
Ok” means the dispatcher successfully finished that action's match arm: every
fallible operation actually invoked in it returned `Ok`. `Action` itself has
no per-action result-returning method. In particular, an `Action::Module`
whose lookup is absent performs no route and can finish successfully.

Hypotheses for the bounded derivation: the inspected source bytes; ordinary
sequential Rust control flow and `Result`/`?` behavior; a non-panicking execution
reaching the named program point; valid indexing on that reached execution;
`candidate_source.active=true` when the component's branch at `:718` is chosen.
Reaching a point already entails that preceding allocations and lookups there
succeeded. No global termination or allocator-success premise is inferred.

Excluded: source schedule semantic completeness, arbitrary graph-observation
readiness, complete generated contextual SCC recognition, exact cycle
certificates, certificate minting, `BothFromRight` authorization, arbitrary
concrete negative-row admission, complete Call meaning, full effect hygiene,
soundness, required principality, production routing and F5/default cutover.

## Literal first-capture obstruction

The first **dynamically reached** capture in `I` need not be the component-member
staging capture at `candidate_scheme.rs:736`. The dispatch path

```text
execute_candidate_graph_plan :721
  -> execute_candidate_source_root :545
  -> execute_candidate_actions :570, Action::Local
  -> route_candidate_local :1125
  -> capture_candidate_graph :1128
```

reaches a capture while the member root call is still executing. Its root
cannot have returned `Ok` yet. `route_candidate_local` looks up the live
`LocalScheme` at `:1118–1120`, begins a route transaction, then captures before
freshening (`:1131`), constraint submission (`:1133`), retained-route insertion
and accounting (`:1134–1147`), and the transaction's return (`:1149–1154`).
Thus even **successful capture return** does not imply this Local action
returns `Ok`; a later operation in the same action can fail. `Action::Install`
does not capture: `:1087–1106` installs the live local root/boundary descriptor.

This path is emitted by real source construction: `candidate_source.rs:263–270`
schedules block initializers/installations before the final expression;
`:282–303` emits `Install` or `LocalAnnotation`; `:356–363` emits `Local` for a
resolved installed local, followed eventually by the root's final
`Annotation`/`Link` (`:452–468`). The existing source case at
`candidate_context_tests.rs:1920–1935`,
`my answer = { my local (x:'a) = x as 'a; local }`, constructs such a schedule
and asserts successful root execution. This test was inspected, not run. The
path is a source-constructor-backed **conditional falsifier**: if that Local
capture is reached during this graph-plan invocation, it contradicts the
literal implication even for a singleton `M`, because its current root is
still on the call stack. This note does not claim an executed full-plan
source counterexample or independently prove every prefix succeeds. There is
no source-owned rule here excluding that capture path from graph-plan execution.

A second nested path is `Action::Module` (`candidate_source.rs:562–566`) through
`route_incoming_inner` (`lib.rs:15890–15897`) to `route_candidate_graph`, which
recaptures a previously published dependency's live root (`candidate_scheme.rs:791–799`).
It observes that dependency during the current member schedule; it does not
establish completion of all current `M` roots.

Consequently the literal dynamic-first implication is **not established**.
The generic phrase “an action error exits before capture/publication” also
cannot mean that no nested capture or local-route observation occurred before
the error. The following theorem expressly fixes the later staging call site.

## Bounded staging-site theorem and complete derivation

**Claim class:** constructive source control-flow derivation at one named
boundary, pending independent review; not an established readiness theorem.

For every invocation `I`, component iteration `M` and ordered member vector
above, if its active branch reaches the first evaluation of the direct
member-staging call `capture_candidate_graph(...)` at
`candidate_scheme.rs:736`, then, for every `0 <= i < k`, the call
`execute_candidate_source_root(r_i)` at `:721` in this same component iteration
has returned `Ok(())`. Each such call dispatched every position in its complete
fixed `A_i`, in order, with every actually invoked fallible suboperation
returning `Ok`. Any action returning `Err` during this member loop prevents
this iteration from reaching any `:736` staging call or any `:749` member-graph
publication. Earlier components and nested observations are outside that last
conclusion.

1. The constructor `emit_candidate_source` owns the schedule
   (`candidate_source.rs:143–148,472–474`). It inserts the constructed action
   vector under the exact definition root. The collection fallback also
   constructs fixed root schedules or loose actions (`lib.rs:1162–1172`).
   This establishes the actual owner, not that the vector encodes every
   semantic requirement of the source program.
2. `execute_candidate_source_root` (`candidate_source.rs:543–547`) removes
   exactly that root's vector. A missing schedule returns `Err` at `:544`.
   Otherwise it borrows the removed vector as `&[Action]` at `:545` and restores
   that same vector at `:546` after the dispatcher returns, including an error
   return. The dispatcher cannot extend this borrowed slice. A stored nonempty
   schedule after return is therefore not evidence of pending actions.
3. Write `A_i=[a_0,...,a_(n-1)]`. In `execute_candidate_actions`
   (`:549–576`), induction on loop position gives: entry to iteration `j`
   entails every position `<j` finished its match arm. Each invoked fallible
   call in every match arm uses `?`. Its first `Err` returns from the dispatcher
   immediately, before iteration `j+1`; the special Link arm applies this to
   both endpoint lookup and admission. No match arm breaks or returns early
   with `Ok`. Thus reaching the sole final `Ok(())` at `:576` entails successful
   completion of all `n` positions. This includes the empty slice vacuously.
   Conversely, normal completion of all positions reaches that `Ok`.
4. By step 2 the root returns the dispatcher's exact `result`, after restoring
   the vector. Therefore a successful root call supplies precisely the action
   iteration fact in step 3. This is success of the Rust availability protocol;
   it is not a new judgment of semantic satisfiability or diagnostic absence.
5. Before this branch, `execute_candidate_graph_plan` copies the original
   member sequence and installs open active roots/uses (`:707–716`). The active
   branch is the separate `for member in &members` loop at `:718–722`.
   Induction on its position gives: before position `i`, every earlier root
   call returned `Ok`; `?` at `:721` exits the graph-plan function on the first
   failing root. Exhausting the loop therefore supplies successful returns
   for **every member position**, including its last one.
6. The staging loop starts only after that complete branch (`:730`). Its first
   capture argument is evaluated at `:736`. Reaching this call implies the
   preceding member loop exhausted, and steps 4–5 yield the required universal
   conclusion. Capture success is not needed for this backward implication.
7. An action error propagates through `:545`, `:547` and the graph-plan `?` at
   `:721`, so this invocation cannot reach its component's staging loop. Once
   staging begins, every staged capture must return `Ok` before publication:
   `:734–737` is a separate loop and `:739–747` performs checked aggregate
   accounting before `:748–750` writes `state.graphs[position] = Some(graph)`.
   The derivation asserts this member-graph publication order, not whole-session
   rollback. Later resource sampling at `:755` can fail after these writes.

The normal consumer bridge is `execute` (`lib.rs:10242–10257`), then
`execute_scc_plan` (`:13831–13840`), which selects this graph executor when
candidate graph state exists. On this normal source-mode path loose actions
finished at `:10249` before SCC execution. That additional history is not a
premise of a direct call to `execute_candidate_graph_plan`. `run_candidate`
(`:10266–10269`) propagates execution failure before producing its final result;
this is not a circuit-certificate publication protocol.

## Why this does not establish Packet 1 ProducerReadiness

An exact certificate query fixes relation roots `R`, their complete generated
contextual component/dependencies and an observation generation. Those are not
the same binder as the definition member sequence `members_M`. Neither the
design nor Packet 1's current task supplies an executable predicate defining
ProducerReadiness over that exact query or a source-owned implication from
the schedule-history fact to it.

| Concern | Source fact available | Remaining bridge |
| --- | --- | --- |
| Source schedule completion | The staging-site theorem covers every action in every member's removed slice. | Bind that history to the exact query's source producer frontier; prove the plan covers all required producers, rather than infer coverage from `Ok`. |
| Typed worklist drain | `constrain_live_item_with_inferred_entry`, `lib.rs:11828–11846`, seeds/enqueues, drains, and settles intrusion before its successful return; `:12101–12105` asserts empty return state. | This is a local constraint-call boundary. It neither proves all generated contextual operations activated nor proves no later action/route can add constraints. A whole-staging queue invariant requires auditing all dispatcher owners. |
| Internal-use readiness | Active roots/uses are installed at `candidate_scheme.rs:707–716`; Module dispatch checks the original use ID and calls `route_candidate_open_use`; `:777–783` validates membership before `route_internal`. | Prove each required internal use is represented and successfully routed. A registry entry and the Module lookup/no-op behavior alone do not supply the universal coverage statement. |
| Later incoming uses | Source mode continues at `candidate_scheme.rs:756`; incoming routes occur in later Module actions. A use recaptures the live dependency at `:798`. | No permanent no-more-producers conclusion follows from this earlier component boundary. The design explicitly permits dependency-extending late edges with invalidation. |
| Complete generated SCC/component | `batch.scc_component_members`, `lib.rs:1582–1589`, returns definition-plan members. `settle_candidate_intrusion`, `candidate_intrusion.rs:358–375`, builds row-dependency SCCs for recorded parent/copy equality. | Neither is the approved complete contextual PUSH/POP-PUSH circuit recognizer. Intrusion `generation` (`:530`) tracks real equality merge changes, not completeness of certificate dependencies. |
| Dependent-observation completeness | Design §5, `:164–173`, requires the full set and withdrawal before reuse. | No exact observation enumeration/generation binding is supplied by action iteration or capture. No circuit-certificate dirty/withdraw/recertify protocol is proved here. |

The retained-input API makes the missing evidence explicit:
`candidate_context.rs:393–396` takes retained State, relation roots, views and
parents; it has no schedule completion or producer-frontier argument.
Every successful return adds `ProducerReadinessUnavailable` and
`DependentObservationsUnavailable` (`:540–542`), alongside filter gaps.
`Complete` is unused (`:275–278`). Search found no non-test retained-input
consumer. `Incomplete` is neither proof of an unfinished producer nor a
negative readiness decision. Rich retained records alone do not prove activation,
complete replay, or complete observation ownership.

**Precise missing premise:** a source-owned contract for one exact query
`(R, generated dependency component, generation)` identifying its observation
boundary and every producer/observation that must be covered, together with
an implication from actual executor/solver completion evidence to that contract
and its late-change invalidation/rollback rule. The staging theorem supplies
only one conjunct of such a future bridge. This note leaves readiness
underspecified; it does not define a weaker predicate and adopt it as semantics.

## Proof-obligation-economy audit and proposal

The prior conditional indistinguishability result did not establish a
source-reachable readiness-different pair. This investigation derives a
different concrete schedule-history fact but leaves the exact readiness
contract untouched. Another projection/model variant would not resolve that
premise. Under the existing audit, preventing premature certificate reuse or
publication is A (correctness). Recovering an executor's discarded completion
position from retained graph shape is D (reconstruction debt). Neither
classification closes or retires Packet 1.

**Proposal only:** if the intended exact query belongs at the member-staging
boundary, retain a sealed, private witness of **source schedules completed**
there. Its construction owner is `execute_candidate_graph_plan` immediately
after successful exhaustion of `:719–722`; its producer evidence is the actual
root executor `candidate_source.rs:543–547`. Tie it to this invocation, the
exact ordered member/root identities, and the exact executed schedule versions.
Use it at a single designated query boundary before `:730–736`, preferably
with a lifetime restricted to that unchanged snapshot. The consumer must
reject a different member set/schedule snapshot. Such a witness is not an
entry-operation certificate or a full ProducerReadiness token.

The historical fact that those schedules returned successfully remains true
after a later relation change. A consumer's claim about **current** query
coverage would not. Its invalidation responsibility must therefore be explicit:
schedule replacement belongs to the Plan construction/execution owner
(`candidate_source.rs:472–474,543–546` and fallback `lib.rs:1162–1172`);
dependency changes belong to the central retained relation/dependency owner
(`candidate_context::State::relation :1418`, `State::dependency :1445`) and its
bound/replay/transport callers. A persistent query witness would need dirtying
before those dependency changes can reuse covered observations. The route
transaction owner `lib.rs:9155–9176` must journal that witness generation and
its invalidation/observation changes with the route, as design §§4–5 requires.
Existing parent-copy `dirty`/`generation` is not a substitute. A short-lived
schedule witness removes only executor-position reconstruction; it cannot
manufacture missing component, filter, transport or observation coverage.

No compiler API shape or readiness semantics is selected by this proposal.
The next action is for the primary to assign the exact query/frontier contract
at its source owner, then review the staging derivation independently.

## Independent review

A fresh `compiler_referee` review found no major or minor issue. It confirmed
the staging-site implication from separate execution/staging loops and error
propagation; confirmed the Local nested-capture path is only a conditional
falsifier, not an executed full-plan counterexample; and agreed that successful
source schedules establish neither complete generated-component coverage nor
dependent-observation completeness. The reviewer did not certify full
ProducerReadiness or Packet 1 closure.

## Frozen dependencies

SHA-256 of inspected source bytes, all equal to the pinned baseline:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `d543106be87d47cb0c06799e6c543cc7b7b414cffbfc224aa2c5bb07d0d83647` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-retained-circuit-evidence-boundary.md` | `61bb53c7c67b0adf49da5472c7fe2fcc2cbc3cbe5cf43a4527620f5195d600b6` |
| `notes/progress/2026-10-10-retained-input-indistinguishability-proof.md` | `175370d4d736b1f289ac356bf68302043c769560b55ad5e2a48bf9651008a1a4` |
| `tasks/current.md` | `bf9156f245a88529bdea1618bcc10f34aaf2ca424f6e1b9865f8cce9e05ac9e6` |

## Checks, resources, runtime and handoff

Checks: bounded `rg`, `nl`/`sed` source reads and SHA-256 hashing; one Python
baseline-byte comparison using read-only `git show <baseline>:<path>` verified
all ten dependencies; final revalidation checks that table, local links,
newline and trailing whitespace on the sole output. These are snapshot and
artifact-integrity checks, not compiler execution or proof certification.
No tests were added or run, no Cargo/build/Oracle process or benchmark sample
ran, and no executable source falsifier was run. No Git mutation occurred.

The primary retains shared verification and integration ownership. No numerical
per-leaf CPU/RAM/wall limit was specified in the packet; this leaf used bounded
reads (at most three concurrent small shell readers) and single-process Python
integrity checks, with zero heavyweight processes, no child workers and no
extra artifact/cache outputs. Whole-turn CPU/RSS/wall time was not sampled;
the final integrity check's measured resources are returned in the handoff.
Stop condition: complete staging-site derivation plus precise unresolved
readiness premise achieved; writing stops before independent review.

Actual task identity: `/root/packet1_readiness_proof`; assigned role: `prover`.
Normal requested/configured routing is `gpt-6.1-sol` / `high`;
`.codex/agents/prover.toml` omits model/effort pins and `.codex/config.toml`
supplies those defaults. Effective runtime model/effort metadata is unavailable
to this leaf: observed **unknown**, not inferred from configuration. No Astra
override, escalation, hot reload, nested dispatch or independent certification
is claimed.

Unverified scope: literal first-dynamic-capture source execution, schedule
coverage of all required source producers/internal uses, staging-wide worklist
invariant, exact query readiness, complete contextual SCC recognition,
observation lifecycle, source soundness/principality and later gates.

Commit packet: exact leased path
`notes/progress/2026-10-10-packet1-source-readiness-proof.md`; baseline
`3a0bcb240896669718042dd0ee1cc5c89e9723d5`; changed dependency hashes: none.
Claim/review status: unreviewed bounded derivation, conditional falsifier and
proposal; no readiness theorem or gate closure. Checks already run are the
static/snapshot integrity checks above. Proposed one-line checkpoint message:
`research: derive component source schedule completion boundary`.
Shared-record delta left for the primary/curator: distinguish first dynamic
capture from first member-staging capture; record the latter's completed
schedule-history implication with its exact site, keep ProducerReadiness and
query/frontier/observation coverage open, and assign the exact source-owned
contract before further equivalent readiness reconstruction. No shared record
was edited.
