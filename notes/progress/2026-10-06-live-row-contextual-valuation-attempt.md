# Contextual valuation preservation for the exact recursive incoming row

Date: 2026-10-06
Status: frozen, unreviewed, research-only conditional derivation
Baseline: `81ceae2804d66142245384db298b8dfb3d0813a8`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: static owner-path correspondence and a constructive valuation argument
Implementation authority: none

## Objective and authority boundary

Attempt the production transition part of the one-row bridge for either
member of `my f x = g; my g y = f`. Preserve the complete caller valuation
while installing `F²(ρ)≤ρ`, `ρ≤Top`, and `F²(ρ)≤cu`. The occurrence row `cu`
already exists. Its value is a coordinate of the caller assignment, and its
lower/upper/direct-row inventory remains part of the relation.

Governing sources are the redesign charter §§1–4; concrete compatibility
boundary §§1 and 3; F5 comparison material §§9, 22, 23 and 32; the member
scheme bridge, H1–H4 and “Source audit”; the production reduction, “Exact
named scheme”, “Symbolic effect elimination”, “Success, diagnostics, and
availability”, and “Smallest residual H4 premise”; the candidate model,
“Valuations”, “Caller and session constraints”, and “Candidate transport”;
and the falsification note's “Shared targets and transitive replay”. The
three research/design/concurrency rules were read in full. `tasks/current.md`
lines 479–506 and `tasks/research-lab.md` supplied routing context;
`notes/design/INDEX.md` supplied locators, not mathematical premises.

The incoming-target-scope audit was an earlier explorer report, not a separate
file. The primary confirmed that the member bridge supplies its cited summary;
the ownership was checked directly at `yu-solver/src/lib.rs:1120` and `:14527`.
Accepted decisions remain fixed: F5 is comparison material; candidate RecGroup
is not selected Yulang meaning; successful general concrete comparisons do
not compose into this preorder. No question bundle or new language decision
is consumed. The carrier and target envelope below remain candidate premises.

## Claim classes and exact premises

**Static characterization:** the inspected owners retain the inequality and
replay directions in the table below, assuming valid handles/session ownership
and successful availability operations. These are source reads, not executed
tests or a production-denotation theorem.

**Conditional mathematical result:** for a completed finite pure trace with
the following premises, the resulting row inventory plus a memo-owned mismatch
marker has exactly the same valuations as the initial inventory conjoined
with the submitted inequalities. This includes reflection and preserves the
same assignment at every preexisting caller coordinate.

P1. Use precisely the reviewed candidate's structural regular-tree carrier
`D`, with Bottom, Top, Int, and total `Fun`. Both handles of every value row
evaluate to its single value `ν(v)`. The complete Function variance law,
greatestness of Top, leastness of Bottom, and its four incompatible-head
inversion facts are supplied by that candidate. They are not inferred from
production successes. Terms evaluate at row handles without expanding bounds.

P2. The candidate target envelope consists of finite, correctly polarized pure
constructor terms over live value rows, Bottom/Top/Int and pure Functions.
Constructor syntax is acyclic; cycles through stored row bounds/direct rows
are unrestricted. Every Function has the two fixed pure effect leaves. The
caller may have arbitrary finite value lower/upper inventories, direct-row
edges and sharing, with any levels. This is a conditional envelope, not a
selected source support limit. General effects, concrete adaptation, Records,
union/intersection routing, rigid/existential source admissibility and later
generalization are outside this extensional theorem.

P3. The entry state is quiescent and its existing typed memo has a completed
certificate: every admitted value pair is entailed by its complete row
inventory and mismatch marker. No incomplete or externally injected pair is
accepted as a certificate. This premise is inductively reproducible from the
empty memo by the completion argument below within P1–P2; it is not asserted
for all production callers, which can use omitted forms.

P4. The exact named finalized scheme and fresh substitution are as audited in
the reduction. The operation finishes every queued task and all owner calls
successfully, without rollback, abandonment or an interleaved mutation.
No row/term identity is retargeted or deleted during the trace. Availability
failure is a separate observation; no result is asserted for a failed trace.

**Source bridge still conditional:** source judgments must realize precisely
this shared assignment, the initial caller relation, admitted fresh witnesses,
and pure term interpretation. Source level/permission admissibility must be
preserved by extrusion as stated below. The derivation does not supply these
premises, select the candidate envelope, or equate the marker with reported
diagnostic freedom, final acceptance, principality or runtime semantics.

## Inventory and completion certificate

For state S define `B_S(ν)` as the conjunction, over **all** caller and fresh
rows, of:

```text
eval(l,ν) ≤ ν(v)   for each exact non-variable lower l stored on v;
ν(v) ≤ eval(u,ν)   for each exact non-variable upper u stored on v;
ν(v) ≤ ν(w)       for every stored direct v→w edge.
```

The direct lower and upper adjacency copies encode the same edge. Repetition
does not change the conjunction. Nested occurrences in another row's bounds
are evaluated under this very same `ν`. A caller constraint is never reduced
to a separately satisfiable interval.

Let `M_S` be true iff no admitted value pair owns a direct mismatch witness.
It is a Boolean property of `TypedPairMemo::Value.direct_witness`, not the
count of public `errors()` and not `DiagnosticCompletion::Complete(None)`.
Put `R_S(ν)=B_S(ν)∧M_S`. This marker retains the logical false obligation of
an admitted incompatible concrete pair even when that pair stores no row
bound. Old caller markers remain in `R_S`.

At a completed state a pair has the following semantic certificate:

* A row/row pair stores its directed edge.
* A non-variable/row or row/non-variable pair stores its exact inequality,
  except a terminal Bottom/Top pair, whose inequality is always true.
* Int/Int and Bottom-lower/Top-upper pairs are true by P1.
* A mismatched atom/head pair makes `M_S` false, exactly as P1 inversion
  requires. If `M_S` is false, `R_S` entails every pair vacuously.
* A Function/Function pair has admitted its argument and result value
  children, plus the two fixed, true effect children. Its inequality is
  equivalent to those two value-child inequalities by P1.

The last clause has a well-founded proof: assign each finite constructor
term its syntax height, assigning height zero to a row handle. Each Function
child pair has strictly smaller sum of endpoint heights. Induction therefore
proves the certificate for every Function pair from the other four cases.
It does not follow a row's stored bounds when measuring height. Consequently
`F²(ρ)≤ρ` and arbitrarily cyclic row replay do not make this induction cyclic.

For a duplicate Function pair the required children were enqueued on its first
admission and have been processed by P4, or were already completed at entry
by P3. `constrain_live` marks before decomposition, but the certificate is
claimed only at successful completion. No assumption that a memo cycle denotes
the greatest fixed point is used. A raw, mid-operation memo hit supplies no
such certificate. This is a stronger completion argument than treating every
memoized inequality as an extra assumed semantic axiom.

## Exact transition correspondence and preservation

Locations refer to the frozen `crates/yu-solver/src/lib.rs` dependency.

| Owner | Observed transition | Candidate justification |
|---|---|---|
| `value_endpoint`, :10599 | Component/live-variable handles become the same row ordinal in either polarity | One coordinate `ν(v)`; identity mapping is observed, its denotation is P1 |
| `constrain_live`, :11059 | Duplicate skips; mismatch stores direct witness; Bottom/Top terminates; Function emits reversed arguments and covariant results | Completed certificate, false head inversion, extrema laws, complete Function law |
| `apply_value_task`, :12071, row/row | Store direct lower/upper adjacency; transmit exact lowers of lower row and exact uppers of upper row | `l≤v≤w` gives `l≤w`; `v≤w≤u` gives `v≤u` |
| Same owner, non-variable/row | Store `l≤v`; replay all current exact uppers and direct upper rows | `l≤v≤u` gives `l≤u`; `l≤v≤w` gives `l≤w` |
| Same owner, row/non-variable | Store `v≤u`; replay all current exact lowers and direct lower rows | `l≤v≤u` gives `l≤u`; `w≤v≤u` gives `w≤u` |
| `extrude`, :10670 | Descend through a row's stored bounds and adjacencies only after its generation/level guard passes; skip an already-marked or already-aged row (`level <= target_level`) before that traversal; traverse encountered Function fields | No inequality or row identity changes; level changes remain irrelevant to extensional evaluation; source permission preservation remains unproved |
| `instantiate_and_route_closed_inner`, :14527 | Restore lower, then upper, then exact predicate below occurrence row | Three root inequalities; one shared fresh coordinate |
| `route`, :15008 | Admit provenance fact, constrain key, retain routed-use provenance | Additional ownership information; no replacement of the occurrence coordinate |

For one completed `constrain_live(q)`, write S0/S1 for its entry/exit states.
Under P1–P4,

```text
R_S1(ν)  iff  R_S0(ν) ∧ eval(q.lower,ν)≤eval(q.upper,ν).       (C)
```

Forward preservation: fix **one** `ν` satisfying the right side. Every task
submitted to the queue is true under it. The root is true by assumption;
Function children are true by equivalence; a replay child is true by one of
the transitivity chains in the table, using its stored parent inequality and
the newly submitted inequality. All stored bounds therefore remain true.
The same `ν` satisfies every old caller bound and every new bound. No direct
mismatch can be admitted, since its P1 inequality is false. Extensional
evaluation is unchanged by level lowering. Thus `R_S1(ν)` holds. Duplicate
skipping changes none of these statements.

Reflection: fix `ν` satisfying `R_S1`. Bounds and direct mismatch witnesses
are retained, so it satisfies `R_S0`. If q was already memoized, P3 gives its
inequality. Otherwise the completed certificate gives its inequality:
row cases are stored exactly, terminal cases are true or contradict `M_S1`,
and Function cases use the height induction. All generated/replayed tasks
finish by P4. Hence the right side holds. Reflection needs no independent
choice for an occurrence of `ρ`, and needs no row-bound acyclicity.

The argument applies at completed owner-operation boundaries. During a pop,
its obligation must also be retained as an in-flight obligation until storage,
decomposition or terminal certification completes. An observation made between
memo admission and child enqueueing is expressly outside (C).

Finite queue exhaustion is consistent with this envelope: for a fixed finite
endpoint universe, each typed pair is admitted once; each successful admission
adds finitely many memberships and queues finitely many children. The value
task/extrusion owners allocate no new endpoint identity. The scheme's one row
and finite terms are created before their respective constraints. This is a
structural finiteness argument, not a CPU/RAM bound, diagnostic-completion
proof or guarantee that all reservations succeed.

## Compose the actual incoming route without changing the caller

Collection at :1120 looks up the occurrence's already allocated value
component. `route_incoming_inner` at :14877 uses that component term; it does
not allocate a replacement consuming row. Fresh allocation at :9550 appends
one empty value row for this R binder. Substitution and positive recursive
parts at :14264 preserve the repeated binder ordinal; P4 fixes the audited
scheme with no Q rows. Let its coordinate be `d=ν(ρ)` and put
`L=P₀(Top−,P₀(Top−,ρ+))`, so `eval(L,ν)=F²(d)`.

Apply (C) to bound lower restoration, bound upper restoration, and predicate
routing, in the actual order. Fresh allocation leaves the old valuation
untouched and adds one unrestricted candidate coordinate. For every fixed
assignment σ of **all** preexisting caller rows,

```text
{ d∈D : R_final(σ[ρ:=d]) }
 = { d∈D : R_initial(σ)
              ∧ F²(d)≤d ∧ d≤Top ∧ F²(d)≤σ(cu) }.            (I)
```

Any additional fixed carrier-only caller predicate `K(σ)` can be conjoined
to both sides pointwise. If a prior outer constraint uses another caller row,
that row keeps its original σ coordinate. There is no existential rechoice
of σ, no erasure of its direct edges or nested lower/upper terms, and no
replacement of `L≤cu` by a `ρ→cu` edge. The final inventory can contain new
bounds involving ρ and old rows because of replay; (C) proves they are exactly
redundant or decomposed consequences in the contextual relation.

For example, an existing upper `cu≤N₀(A0+,N₀(A1+,v−))` first replays `L`
against that upper, then emits `ρ+≤v−`. That row pair stores `ρ→v`, can age
both rows and propagate bounds in both directions. From the original clauses
this edge is entailed by the full Function law, since both argument tasks
target Top. Conversely it retains the same original comparison after
decomposition. It is a genuine new caller/local connection; the proof retains
it rather than asserting that freshness isolates the new row from callers.

Existential hiding of d can be performed **after** (I). The carrier projection
`Ω≤σ(cu)` can then be cited conditionally from the reviewed candidate. This
note's result is (I), not a new calculation of that isolated projection.

## Extrusion, source permissions and diagnostic ownership remain explicit

The static extrusion read shows changes to levels, marks, generation and
scratch, with journaling before row-level changes. Traversal descends through
a row only when its generation/level guard passes. An already-marked row or
an already-aged row (`level <= target_level`) is skipped before its bounds
and adjacencies are traversed; unrestricted reachability closure is not
claimed. Extrusion allocates no new carrier row and alters no exact bound or
direct edge. Level changes remain irrelevant to the declared extensional
evaluation, so (C) remains valid for that candidate interpretation. Source
permission preservation is still unproved.

Let `A_alloc(σ,d)` mean permitted realization immediately after fresh
allocation at the use level, and `A_final(σ,d)` mean permitted realization
under the final levels/permissions. The precise missing extension is

```text
R_initial(σ) ∧ F²(d)≤d ∧ d≤Top ∧ F²(d)≤σ(cu)
  implies [A_alloc(σ,d) iff A_final(σ,d)].                   (L)
```

With (L), intersecting (I) with admissibility yields a conditional source
permission preservation result. Without it, (I) remains extensional. The
charter's accepted generation-time guard for every derived existential
comparison and variable-only levels is not reinterpreted as a freely erasable
metadata rule. The exact incoming scheme/source envelope must establish (L)
or an explicitly justified narrower condition. This is the precise blocker
for transporting the candidate valuations through source scope semantics.

Diagnostic ownership is likewise retained. `constrain_live` records value
Function child edges and replay edges under their inducing parent pair;
`complete_diagnostic_delta` at :11474 completes a separate graph; and
`replay_witness` at :12048 reports the completed root witness under the
occurrence/cause passed to that invocation. Bound restoration and predicate
routing create the occurrence/cause described in :14600 and :15008. A replay
task does not invent a new source occurrence. The public error deduplication
in `report_incompatible` is occurrence plus error kind.

The marker M deliberately concerns admitted direct mismatch ownership.
Nothing above proves the diagnostic SCC's completed witness selection,
that every inconsistent row inventory produces a direct mismatch, or that
absence of a root-reported error equals satisfiability. In particular, (I)
can characterize an empty inventory fiber without proving an algorithmic
diagnostic decision procedure. `Ok` and successful route accounting are not
acceptance booleans. The reduction's documented rollback and later-accounting
failure boundary remains unchanged. Failed/rolled-back/published sessions and
diagnostic reserve failure require separate proofs.

## Independence, coverage, failure conditions and next proof

The proof uses independently specified candidate order laws together with
narrowly observed production transitions. It is a source-to-transition
conditional correspondence, not an independent source-semantics oracle.
Both sides share P1's interpretation of row identity, polarity and pure
Function. A checker supplied P1 or (L) would verify consequences of those
premises, not establish them as source rules. No executable oracle/checker,
seed/range, mutation execution, test, build or search was used.

Coverage is symbolic over every finite pure caller inventory in P2 and every
assignment σ, including all value direct edges, both bound sides, nested row
occurrences, repeated polarities, arbitrary row cycles and the exact three
incoming root tasks. It is not bounded enumeration and claims no timing or
finite carrier-size characterization. The existing separate-polarity and
hidden-caller countermodels are cited dependencies only; neither is repeated.

Named failure conditions are: missing caller inventory; two polarity values;
an incomplete/stale/injected memo certificate; cyclic constructor syntax;
a non-pure/effect/adaptation endpoint; deletion or retargeting of a row;
interleaving; observing a partial transition; availability failure; and an
unproved level/permission change. Production source realization, actual
target-class selection, diagnostic completeness, principal inference, general
SCC source adequacy, runtime observations and publication remain unverified.

Recommended next action: independently review (C)/(I) and the completed-memo
height argument, then derive (L) and source realization for the exact admitted
caller class from its governing judgments. Further carrier probes cannot
establish those source premises.

## Frozen dependencies, commands and resources

Commands used: bounded `rg`, `cat`, and `sed` source/authority reads;
`sha256sum` of the dependencies below; a final read-only dependency equality
and leased-note text integrity check. Initial combined captures were truncated;
the governing sections used in the derivation were reread narrowly. Read-only
`git rev-parse HEAD` and `git branch --show-current` confirmed the supplied
baseline/branch; this was a departure from the packet's “no Git” command
constraint, with no Git mutation or state change. No probes, tests, builds,
formatters, children, shared records or other leased files were touched.

Budget consumed: static reasoning, lightweight source/hash reads, one output
path. No numerical CPU/RAM/wall-time cap was supplied. At most three source
read shell processes ran together in the initial batches; later reads were
single-process. CPU time, peak RAM and total wall time were not instrumented.
No incomplete computation or uncovered enumeration shard exists; the omitted
proof scope is stated above. Dependencies below were equal at final freeze.

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  notes/design/2026-10-03-concrete-compatibility-boundary.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e  notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md
f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779  notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md
9f557efeb5587898ea7530eb0087b4528c19313cd5174239f89aaa2965a34ecc  notes/progress/2026-10-06-rec-name-return-one-row-candidate-model.md
e6cc8ab29166ac3f68c070963087e2d34f9ee16aa800ef2cca0fc77e2c1bd480  notes/progress/2026-10-06-rec-name-return-one-row-falsification.md
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

## Commit packet

* Exact leased path: `notes/progress/2026-10-06-live-row-contextual-valuation-attempt.md`.
* Baseline SHA: `81ceae2804d66142245384db298b8dfb3d0813a8`.
* Changed dependency hashes: none observed; all eleven frozen inputs above
  were rechecked. Primary revalidation owns any later branch movement.
* Claim/review status: frozen unreviewed research-only conditional
  completed-transition derivation; no source-denotation or production theorem
  closure and no implementation authority. Producer rereading is not
  independent review.
* Checks already run: narrow owner/governing-section reads, dependency SHA-256
  equality, leased-note newline/whitespace/conflict-marker integrity. No
  executable semantic verification.
* Proposed one-line research-checkpoint commit message:
  `research: derive conditional contextual live-row valuation preservation`.
* Shared-record deltas intentionally left for primary/curator: record the
  conditional completed-transition certificate and exact contextual fiber;
  retain source/polarity realization, level-permission law (L), target-class
  selection, diagnostic completeness and availability/publication as open.
  No task/index/authority/theory/question-board file was edited.

Writing stops at this frozen handoff; review repairs need an explicit delta lease.
