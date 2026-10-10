# Conditional certificate generation and route rollback

Date: 2026-10-10
Status: unreviewed conditional mathematical derivation; research only
Frozen baseline: `b92f965e7d8c2035b0456e882673e8cc8852dff9`
Producer: `/root/conditional_snapshot_proof`, one prover leaf, no delegation
Exclusive output lease: this file only

## Objective and authority

Prove certificate applicability through reuse, relevant mutation and route
rollback by induction on a specified transition system. This proves a
conditional lifecycle statement, not that compiler constructors implement the
transitions. It does not prove certificate recognizer correctness or the
semantic correctness of the values computed using a certificate.

Direct authority is
[contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§4, especially task admission, replay, capture/freshening and rollback, and §5,
especially complete generated SCC coverage, late-edge withdrawal,
recertification, private deferral and atomic restoration. The frozen source
context is
[certificate gap map](2026-10-10-context-cycle-certificate-gap-map.md) and
[Packet 1 schedule boundary](2026-10-10-packet1-source-readiness-proof.md).
These two notes are evidence/context and cannot strengthen or weaken the
design. Their historical baselines are distinct from this note's baseline;
this derivation consumes their recorded contents, not a new source audit.

The assigned assumptions are preserved: an exact certificate at generation
`g`; invalidation before any affected reuse following a premise-changing
mutation; tagged, withdrawable dependents; and atomic rollback. Two details
must be made explicit. Tagging alone supplies no reuse guard. Restoring only
generation, graph, observations and publication supplies no guarantee about
omitted certificate status, recognizer inputs or memos. The theorem below
states the guard and the full restoration premise. A separate consequence
states exactly what follows from the four named rollback projections alone.

No language semantics, compiler transition, source restriction, prerequisite,
or gate status is adopted. Complete Call meaning, effect hygiene, soundness and
required principality remain excluded obligations, rather than consequences.

## Frozen objects, binders and state

Fix any identity universe `U` and any family `Q` of exact certificate queries.
For each `q in Q`, its anchor contains the original relation-root identities,
component kind and endpoints, use/annotation instance identity, lexical scopes
and original binders needed to identify that query. A query for another scope,
use or root is a different query. When relevant, attachment occurrence/member
identity, resolved operand, provider, witness, residual constructor lineage,
gamma coordinate, actual parent/copy provenance, ContextExpr child identity
and operation order are exact labeled data. No quotient by endpoint equality,
nominal family, source spelling, alpha-equivalence or independent marginal
witness choice is used. These labels belong to the actual supplied records;
this note does not invent an evaluator for them.

A generated state has a dependency graph `D` and recognizer input records `X`.
For an anchored query `q`, define `F_q(X,D)` to be its **complete current
recognizer footprint**: the complete currently generated contextual SCC and
its required dependency closure, identity seeds, recursive operators,
attachments, filter registrations, ordered/shared operation inputs, and every
other premise read by that recognizer. SCC membership is computed from the
current generated graph, not fixed to a definition-plan member list. An edge
that merges a component or brings in a new dependency changes this footprint.
An input that affects recognition is in the footprint even when it is outside
the old component or has not yet been replayed. Equality of footprints means
equality of all these labeled records and their incidence, not graph
isomorphism or equality of an endpoint projection. This is a definition of
the conditional premise, not a claim that retained state exposes it.

Write `Exact(q,F,c)` for the supplied certificate judgment: certificate `c`
exactly recognizes the whole footprint `F` as one of the two approved circuit
classes, with all recognizer premises and exact identity/scope data. Its
truth is an assumption of this theorem; neither a finite graph shape check nor
the count relations `p=0,n>=0` and `p>=0,n>=0` are proved here.

At an observation boundary, the state is

```text
S = (X, D, G, C, O, M, P, L, T).
```

`G[q]` is a generation binding. `C[q]` is `Dirty`, `Deferred`, absent, or
`Valid(g,q,F,c)`. `O`, `M`, `P` are observation, memo and publication stores.
`L` records complete certificate dependence, including dependence through
other results. `T` is the route stack containing entry snapshots. A result
record includes its exact consumer query/scope, payload and dependency tags
`(q,g)` for **every** certificate on which it depends. A record depending on
several certificates must satisfy the guard for each; no marginal certificate
or witness selection is licensed. Stores and `L` include every reachable
cached handle and every currently observable certificate-dependent
publication, not only one chosen map.
`L` is the certificate lifecycle record's full dependent-observation set:
creating a new dependent registers it atomically. If that registration also
changes a recognizer premise, it requires `Change`; otherwise it extends
withdrawal ownership without changing the recognized snapshot.

Generation binding here means the identity of a certification snapshot. A
numeric generation alone is insufficient if it can denote a different
snapshot while an old handle remains usable. Increments/invalidation must
prevent that aliasing. Exact rollback may restore a previous binding because
it also restores its snapshot and removes all usable aborted-route handles.
This states the required meaning of a generation tag; it selects no counter
representation or compiler API.

Define the applicability guard for an individual dependency as

```text
Guard(S,q,g) iff
  G[q] = g and C[q] = Valid(g,q,F,c)
  with F = F_q(X,D) and Exact(q,F,c).
```

The operational guard need not recompute `Exact` on every reuse: induction
will justify those last two clauses from a valid binding and the mutation
protocol. A consumer must check the current valid binding, exact query/scope
and matching tag, rather than generation equality alone. A currently readable
result is certificate justified when all its declared tags satisfy `Guard`
and its exact requested consumer query/scope matches its creation record.
This conclusion means its certificate premises are still applicable. It
does not assert that an arbitrary payload is correct merely because it was
tagged. A theorem about payload correctness additionally needs a proved
observation/evaluation rule and faithful provenance of that computation.

## Hypotheses and admissible transitions

Quantification is over every finite trace, and hence every finite prefix of
an infinite trace, from a state satisfying the invariant below. Every mutation
and every observation boundary is covered by the following assumptions.
There is no termination, finite context-count, source-schedule quiescence,
allocation-success or global source-reachability hypothesis.

**H1: exact minting.** A valid binding can be installed only for the exact
current footprint, under `Exact(q,F_q(X,D),c)`. Recognition and installation
use one unchanged snapshot, or revalidate that exact snapshot before
installation. Recognizer failure installs no valid binding.

**H2: complete invalidation.** Every event capable of changing any premise of
an installed certificate invalidates its binding before any affected dependent
can be observed, memoized, omitted/replayed using that result, or published.
This includes a new edge outside the previous dependency index that enlarges
the footprint, a changed filter or scope/provenance input, and an SCC merge.
The affected set is the complete set of installed bindings whose premises
can change, not merely the entries discoverable in an incomplete old index.
A claimed unaffected binding must have exactly the same footprint. Generation
changes/invalidation cannot alias a still usable old handle to a new snapshot.

**H3: complete dependent ownership.** Every dependent result has accurate,
complete tags, and its transitive consumers are registered in `L`. Withdrawal
removes or blocks all affected observations, memos, result handles and
publications before the next dependent observation. Being potentially
withdrawable without actually being withdrawn or blocked is insufficient.
Recomputed results are created against the recertified current snapshot.
All dependent observations required by a publication are recomputed before
that publication, preserving their recorded joint dependence and sharing.

**H4: guarded consumption.** Every result creation or reuse, and every
certificate-dependent publication, requires the current valid binding for
each tag, matching exact query/scope and generation. Public visibility counts
as observation: a publication cannot stay observable while its tag is dirty.
Atomicity means observers cannot see the interval between state mutation and
withdrawal as if it were a valid state. Operations may be sequential or
linearizable to these boundaries; an unvalidated concurrent read is excluded.

**H5: full route restoration, for conclusion (3).** Route entry snapshots
preserve the entire validity footprint: all `X,D,G,C,O,M,P,L` that the route
can change, together with all usable handles and relevant identity/binding
state. Abort atomically restores those values and discards the aborted
route's handles, publications and dependent continuations. Unrelated state
may remain only if it is outside that footprint. No irreversible external
effect is represented as a withdrawable publication. This is the whole-route
reading of design §4; the four projections in the assigned rollback tuple
alone do not imply H5.

The transitions below expose the necessary guards; they do not purport to be
actual Yulang source constructors.

| Transition | State effect and observation condition |
| --- | --- |
| `Certify(q)` | At one current snapshot, accept only by H1; set `C[q]=Valid(g,q,F_q(X,D),c)` for the current nonaliased binding. Failure leaves it dirty/deferred, without certificate-dependent visibility. |
| `Create/Reuse/Publish(r)` | Enforce H4 for every exact tag and consumer query/scope. Creation records complete dependence in `L`; publication is one guarded result store. |
| `Change(e)` | Before changing any footprint that `e` can affect, invalidate all affected valid bindings, withdraw/block their complete dependent closure by H2–H3, and then apply the exact `X,D` mutation. Advance the binding or leave it unusably invalidated. There is no dependent observation between these stages. |
| `Recertify` | Apply `Certify` to the changed complete snapshot. Successful recertification permits new/recomputed guarded results. Unsupported recertification keeps the new exact edge and records deferred private publication; it does not restore old results, erase the edge, approximate, or reject the source. |
| `Unrelated(e)` | Change only state with unchanged footprints and unchanged validity/visibility of the results it leaves live. Otherwise this is a `Change`, not an unrelated event. |
| `Withdraw(r)` | Remove/block a dependent result and its registered transitive dependents. No new result becomes usable. |
| `BeginRoute` | Push an exact entry snapshot required by H5. |
| `CommitRoute` | Drop the top snapshot and keep the current state; it adds no unguarded visibility. A dirty/deferred component may remain private. |
| `AbortRoute` | Atomically reinstate the top entry validity footprint by H5 and drop the route frame. Aborted-route dependent handles cannot escape into the restored state. |

`Change` may conservatively invalidate more bindings than actually change;
this weakens reuse availability, not recognizer exactness. Any event not
covered by these transitions must be shown to preserve the same invariant
before the theorem can cover it. The universe of premise-changing events,
dependency coverage and guarded boundaries are hypotheses, not conclusions
of a transition checker.

## Induction invariant and derivation

For every observation-boundary state `S`, let `I(S)` assert:

1. Every installed `Valid(g,q,F,c)` has `G[q]=g`,
   `F=F_q(X,D)` and `Exact(q,F,c)` with exact identity/scope labels.
2. Every usable dependent result/publication has complete recorded support,
   and every tag satisfies `Guard`; dirty/deferred/absent bindings support no
   usable dependent result.
3. Every open route frame has an exact saved entry validity footprint that
   satisfied (1)–(2), and its restoration discards all aborted-route handles.
   Saved snapshots are immutable, including recognizer inputs and payload
   records; a pointer to a later-mutated record is not an exact snapshot.

The initial state may have no certificates and no certificate-dependent
usable results, satisfying (1)–(2) vacuously. Alternatively any exact already
certified initial state satisfying these clauses is allowed. No particular
compiler initialization is assumed.

**Induction step.** Assume `I(S)` and consider one admissible transition.

- `Certify` installs precisely the current footprint and exact judgment by
  H1, so (1) holds for that binding. It changes no existing support to a
  different snapshot; old usable handles cannot alias the binding. New
  results still require a guarded creation, so (2) holds.
- `Create/Reuse/Publish` changes no recognizer premise. Every support tag
  passes the exact valid-binding guard by H4; (1) justifies its current
  footprint and `Exact` clauses. H3 records all dependence of a created
  result. Thus (2) holds, including results with multiple tags.
- `Change` disables all bindings capable of being affected and blocks their
  full dependent closure before the mutation becomes observable. No valid
  affected binding or usable affected result remains, so their clauses in
  (1)–(2) are vacuous. Every remaining valid binding has an identical footprint
  by H2; the preceding invariant carries its exactness forward. Remaining
  usable results have no affected support tag by H3. These facts reestablish
  (1)–(2). H5 preserves route entry snapshots independently of mutable state.
- `Recertify` is the `Certify` case followed, on success, by guarded creation
  of recomputed results. On unsupported recognition no valid binding is
  installed; the new edge remains, but no old dependent visibility is
  enabled. The same invariant holds without a termination assumption.
- `Unrelated` preserves footprints and validity by its explicit premise;
  `Withdraw` only reduces usable results. Both preserve (1)–(2).
- `BeginRoute` copies a state satisfying (1)–(2), giving (3). `CommitRoute`
  removes one frame without changing current validity. `AbortRoute` restores
  the exact saved entry state, so (1)–(2) hold by that frame's saved invariant.
  The remaining outer frames are unchanged; H5 discards abort-created usable
  handles and ensures (3). This also covers properly nested route aborts.

All transition cases preserve `I`. Induction on trace length proves it at
every covered observation boundary. No source transition coverage follows
from this mathematical induction.

## Conditional snapshot theorem

For every identity universe `U`, exact query family `Q`, initial invariant
state and trace satisfying H1–H4, and for every query `q`, generation binding
`g`, result and trace position:

**(1) Unchanged-generation reuse.** If a result with exact tag `(q,g)` is
reused under the guard while `g` remains the current valid binding, then
`Exact(q,F_q(X,D),c)` holds for its supporting certificate, with the same
complete labeled footprint as that certification snapshot. This follows
from invariant (1) and the guarded-consumption case. Unchanged generation
equality by itself, without valid status and the query/scope guard, is not
the antecedent. Payload correctness remains a separate evaluator obligation.

**(2) Later relevant mutation.** If a later mutation can change that
certificate's premises, then before its first dependent observation H2–H3
have invalidated `(q,g)` and withdrawn/blocked every result depending on it.
Guarded reuse is impossible in the dirty/deferred interval. It becomes
possible for the changed state only after H1 exact recertification and H3
recomputation against the new valid binding. If recognition remains
unsupported, publication remains private/deferred. Exact rollback to an
earlier snapshot is a separate restoration case, not a recertification of
the changed state. An unrelated mutation needs no invalidation when its
footprint equality premise is actually established.

**(3) Exact route restoration, additionally under H5.** For every covered
route with entry state `S_entry`, atomically aborting it yields equality of
its entire validity footprint with `S_entry`, preserving original identities,
scopes, certificate binding and dependency incidence. Consequently, for each
restored pre-route result, its guard and visibility after abort equal their
pre-route values. Aborted-route results are unusable. A later supported retry
starts with only the restored certificate generation available, and may use
it only through its original exact query/scope guard. A retry can still
perform a new relevant mutation and trigger conclusion (2). The theorem
does not promise that the retry or any recognizer terminates.

Conclusion (3) follows by equality of the saved/restored footprint, rather
than by assuming that restoring an integer recreates its certificate. If
H5 is omitted and only `(G,D,O,P)` is restored, equality of precisely those
four projections follows. Exact pre-route validity does **not** follow:
`C`, `X`, `M` and reachable handles can still differ.

## Minimized limits of the weaker hypotheses

These are abstract omission witnesses; none claims source reachability.

- **Tagging without a guard.** Start with an exact valid certificate at `g`,
  create any tagged but unrelated payload, and let a consumer accept it merely
  because its integer tag equals `g`. No mutation is needed. Tags and
  withdrawability do not supply its certificate provenance, exact consumer
  query/scope or payload correctness. H4 and complete support are indispensable
  to the applicability conclusion; value correctness needs another theorem.
- **Restoring four projections only.** Start with
  `C[q]=Valid(g,q,F,c)` and a visible observation/publication. A route dirties
  `C[q]`, withdraws the dependents and later fails. Restore exactly pre-route
  `G,D,O,P` but leave `C[q]=Dirty`. A correct guard now rejects the restored
  result, so pre-route validity has not been restored. Alternatively retain a
  route-created filter in `X` while restoring `D` and `G`; the old footprint
  no longer holds. Restoring memos and all reachable dependent handles is
  likewise necessary to exclude surviving abort-created aliases.
- **Old dependency index only.** An exact initial SCC certificate can be
  invalidated by a newly entering edge from an endpoint missing from the old
  reverse index. If that owner classifies the edge as unrelated, H2 fails.
  The snapshot theorem cannot prove index completeness by quantifying only
  already indexed edges.

The precise additional rollback premise is therefore equality of the complete
certificate validity footprint, including certificate status/content,
recognizer records, memo and observation dependence, and usable handles.
Design §4 explicitly journals context nodes, recipes, registrations, watchers,
origins, memos, bounds, certificate state, dependent observations and
publication together. §5 explicitly restores the pre-route certificate and
dependency state. This supports the full-route interpretation; it is not
evidence that the current journal implements it.

## Section 5 and the source/operational boundary

Section 5 requires a certificate of the **complete generated SCC component**
at its certification snapshot. It explicitly allows a later new edge to
enter the dependency set, requiring dirtying and withdrawal before dependent
reuse, then exact recertification. It therefore requires complete current
snapshot coverage plus future relevant-edge invalidation. Permanent
source-schedule quiescence, absence of later incoming uses, or a global
no-more-producers boundary is not required by that text.

Certification must still read one coherent snapshot, and every mutation that
can affect its premises must be caught. The lack of a global quiescence
requirement does not prove a local observation boundary safe. A partial store
that omits already generated operators, unactivated required work or dependent
observations is not the complete snapshot premise. A source-schedule completion
witness alone neither supplies this premise nor disproves it.

The allowed frozen notes identify these actual owning paths and consumers;
source files were not independently reread under this leaf's restricted read
packet:

| Obligation in this proof | Owner/consumer recorded in the frozen source context | Unestablished bridge |
| --- | --- | --- |
| Generated producers and observation boundaries | `emit_candidate_source`; `execute_candidate_source_root`; `execute_candidate_actions`; `execute_candidate_graph_plan` | Successful fixed-slice execution does not imply all exact query producers/observations are covered. Nested Local capture can occur before the member schedule finishes. |
| Exact `X,D` ownership and affected-query invalidation | `candidate_context::State::relation`, `State::dependency`, and bound/replay/transport callers | Their retained relation/dependency records are not a proved complete certificate footprint or future-edge invalidation index. |
| SCC/epoch distinction | `candidate_intrusion::settle_candidate_intrusion`, `Dependencies::components`, intrusion `generation` | Recorded parent/copy equality SCCs and equality generations are not the complete contextual two-circuit recognizer or its generation binding. |
| Guarded dependents | `TypedPairMemo`, relation-completion stores, `pair_is_current`, candidate graph capture/freshening/publication | No generation-bound complete certificate observation/memo/publication guard is established. |
| Route restoration | `RouteMutationJournal`, `candidate_intrusion::Undo`, route transaction at the recorded `lib.rs:9155–9176` | Existing journal ownership does not establish H5 for absent circuit certificate state, withdrawals or graph publication. |

The gap map explicitly reports absent authentic circuit recognizers and
certificate lifecycle. Packet 1 derives a limited member-staging schedule
history implication while leaving the exact query/frontier and dependent
observation contract open. This proof assumes those missing bridges instead
of inferring them from successful schedules, retained constraints, capture,
or equality generation.

This is one assigned derivation, not a third equivalent reconstruction attempt.
The existing proof-obligation-economy audit still applies: lifecycle safety is
A (correctness), and recovering discarded execution/frontier evidence can be
D (reconstruction debt). The next source obligation is the owning
construction/consumption bridge for H1–H5, not another reclassification or
transition model that assumes them. No shared obligation is retired or solved.

## Frozen dependencies and checks

SHA-256 of exact baseline bytes:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-context-cycle-certificate-gap-map.md` | `6fddfe0452b291c24728784502c30a4175bed36ee1c907e1309db85924c0444b` |
| `notes/progress/2026-10-10-packet1-source-readiness-proof.md` | `2538be85722b1a8d0efd711dd6fa8930eaba7ed140848cc0bf838e8b481a434a` |

Static checks: exact `git show <baseline>:<path>` reads of these dependencies;
one bounded Python SHA-256/live-byte comparison found all three equal to the
baseline; skill, role/config and required rule reads. Final integrity checking
revalidates the dependency table and leased artifact whitespace/newline/local
links. These are document/snapshot checks, not executable proofs or source
conformance checks. No compiler source files were read outside the assigned
context, no tests/builds/probes/benchmarks were run, and no Git mutation occurred.

Resource use: one leaf, no children, no compute experiment or heavyweight
process; bounded shell readers and one-process static integrity checks only.
At most five small independent reader commands were concurrent in one initial
batch. No CPU/RAM or whole-turn wall-time measurement was requested or sampled.
The primary owns verification/integration; no additional verification owner
or shared output/cache was created.

Runtime: native assigned role `prover`, task identity
`/root/conditional_snapshot_proof`. Configured/required normal routing is
`gpt-6.1-sol` / `high`; the inspected role has no model/effort pins. The primary
confirmed launch arguments requesting `gpt-6.1-sol` / `high`. The spawn result
exposed the task identity but no effective runtime metadata; observed
model/effort are **unknown**. No Astra, override effectiveness, hot
reload, nested dispatch or independent certification is claimed.

## Handoff and commit packet

Writing stops on delivery. The derivation is unreviewed; its producer cannot
certify it. Unverified scope: H1–H5 satisfaction by actual source constructors
and consumers, full recognizer exactness, observation payload correctness,
current generated SCC completeness and readiness, complete Call/effect hygiene,
soundness, required principality, termination and gate/default-route closure.

One next action: primary assigns fresh independent review of this frozen
conditional theorem, preserving the explicit guard and full rollback premise.
The source bridge remains a separate owning-constructor obligation.

Commit packet:

- Exact leased path:
  `notes/progress/2026-10-10-certificate-generation-conditional-proof.md`.
- Baseline: `b92f965e7d8c2035b0456e882673e8cc8852dff9`.
- Changed direct dependency hashes: none; the three baseline hashes above
  match their live bytes at the recorded check. Primary revalidates before
  integration if dependencies move.
- Claim/review status: unreviewed conditional mathematical derivation;
  no implementation satisfaction, source theorem, readiness or gate closure.
- Checks already run: static reads and baseline hashing/comparison; final
  artifact-integrity check reported in the leaf handoff.
- Proposed one-line checkpoint message:
  `research: derive conditional certificate snapshot lifecycle`.
- Shared-record deltas deferred to primary/curator: record the conditional
  applicability theorem separately from source satisfaction; record the
  explicit exact query/generation guard and complete rollback footprint;
  interpret §5 as current generated snapshot plus future-edge invalidation;
  keep Packet 1/frontier coverage, recognizer exactness, observation ownership
  and approved implementation gates open. No shared record was edited.
