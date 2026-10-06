# CALL_TYPE: local continuation typing versus pending Bind closure

Date: 2026-10-08
Baseline: `fd6434993f02d85221642ab2c4047eb63798f9ca`
Status: frozen research; compiler-referee reviewed, no findings; no semantic or implementation authority
Claim class: sorted algebraic nonimplication for the raw equations; conditional finite-tree lemma
Exclusive lease: this note only

## Objective and governing premises

Test the proposed shortcut that typing a callee's raw continuation, or a
receiver's local Force, suffices to type the enclosing pending observation.
Keep the saved suffix and all original coordinates. The governing sources are
[DAG](../theory/successor-proof-obligations.md) `CALL_TYPE` and `SEM_JOINT`,
[typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6–9,
[source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1–2.2, 3.2–3.5, 5.3, and
[call views](../design/2026-10-05-inferred-function-call-views.md) §§1–5.
The core is Draft; concrete source-contract clauses remain Draft within a
reviewed conditional package. Call views are Authoritative within their
specified formation/protection scope, without supplying completed typing rules.

Preserve the primary's selected actual role/entry, inert whole argument,
receipt-before-entry, designated one-layer consumption, current-state resume,
directional upper-output protection, and one original `X`, binder tree and
`xi=(nu,K,D)`. Provisional views do not change actual roles. Comparison success
cannot supply a provider contract, admission, source association or ownership.

The [computation-entry attempt](2026-10-08-call-type-computation-entry-attempt.md)
already distinguishes `kf >>= S_f` from `ka >>= R_r` and identifies the missing
typed Bind consequence. This note does not repeat its operational table. Its
additional discriminator is a sorted witness satisfying a complete local
finite-tree predicate while failing that predicate after the saved suffix.
The earlier [one-output erasure](2026-10-07-call-type-local-law-falsification.md)
changed an unconnected descriptor atom. Here descriptor sets are fixed in
advance, and the pending failure follows by evaluating the entire continuation.
Neither method constructs the required complete independent interpretation.

## Exact claim boundary

There is no supplied exhaustive `SEM_JOINT` clause family against which this
note can certify a complete interpretation. In particular, membership of an
actual callable at the callee's ordinary Function descriptor may already
require complete invocation preservation. This note does **not** refute the
shortcut under that stronger, fully justified meaning of local typing. A raw
continuation's source endpoint label alone is not that meaning.

The established algebraic result below is only:

```text
raw Return/Request/Bind equations + independently defined local algebraic typing
    do not entail typing after an otherwise fixed saved suffix.
```

“Independently defined” means independent of the raw source image and of `Q`
in this algebra. It does not mean independently justified as Yulang semantics.
The model is not a same-SEM_JOINT counterexample, admitted-source witness,
ordinary Function interpretation, or a falsification of `CALL_TYPE`.

## Sorted algebra and complete coordinates

Fix one formal ambient coordinate
`omega=(X, original binder tree, xi, h, w)` once. Its internal source/provider,
owner, operation-instance, response-endpoint, receiver, profile and path fields
remain uninterpreted and unchanged. No existential coordinate is hidden.
They are retained fields, not proofs of their source predicates.

Use distinct sorts `Value`, `Config`, `Response`, `Request`, `Suffix`,
`Continuation` and `Computation`. A computation is a finite effect tree:

```text
Return(value, config, omega, trace)
Request(request, config, continuation, omega, trace).
```

A continuation takes `(response,current_config)` to a computation. A suffix
takes `(value,current_config)` to a computation. Typed stage incidences and
ordered delimiters are recorded in `trace`; Bind preserves them and appends
the saved suffix's stages when reached. The equations are precisely the two
source-contracts §3.2 equations, with these retained coordinates displayed:

```text
Return(a,C,omega,tau) >>= S = S(a,C;omega,tau)
Request(q,C,k,omega,tau) >>= S
  = Request(q,C,(rho,C') -> k(rho,C') >>= S,omega,tau).
```

The output side of each equation contains the same `omega`. The request's
original witness and operation/response identity persist on resumption. No
callee-prefix event is reassigned to the receiver. The raw algebra adds no
source rule for receipt, protection, expiry or a result conversion.

For each value descriptor set `B`, define a candidate finite-tree predicate
`T_B` independently of these equations:

```text
T_B(Return(a,C,omega,tau)) iff a in B and W_B(C,omega,tau)
T_B(Request(q,C,k,omega,tau)) iff
    L_B(q,C,omega,tau) and
    forall (rho,C') in Adm(q,C,omega,tau): T_B(k(rho,C')).
```

`B`, world predicate `W_B`, request predicate `L_B` and response domain `Adm`
are fixed semantic inputs of this candidate algebra. Thus “typed pending”
here checks its complete raw continuation, rather than just the request
head. There are no latent values or recursive references in this witness;
this definition supplies no interpretation of their source obligations.

For this candidate predicate the Request/Bind equation gives the exact test:

```text
T_V(Request(q,C,k) >>= S) iff
    L_V(q,C,omega,tau) and
    forall (rho,C') in Adm(q,C,omega,tau): T_V(k(rho,C') >>= S).
```

All suppressed coordinates remain those displayed above. Knowing
`T_U(k(rho,C'))` is insufficient to establish its right-hand side: its terminal
values/worlds have been checked at `U`, before the remaining `S` executes.

## One minimized pending witness

Choose `Value={u,v}`, `Config={C}`, `Response={rho}`, one request `q`, and
`U={u}`, `V={v}`. World and request predicates are true on every trace reached
by this witness; `Adm` is the singleton `{(rho,C)}`. These are candidate
algebraic assumptions, not certified source/world admission clauses.

Fix a raw continuation and a saved suffix:

```text
k(rho,C) = Return(u,C,omega,tau_resume)
S(u,C;omega,tau_resume) = Return(u,C,omega,tau_resume ++ sigma)
J = Request(q,C,k,omega,tau_request).
```

`S` returns the same value and current state; it performs no value conversion.
The nonempty `sigma` retains the entire ordered outstanding invocation suffix
as opaque stage records. It can record argument delay/receipt/entry/body/
consumer/return identities when attached to `S_f`; this model certifies none
of their ordinary typing premises. Its fixed trace is never dropped to make
membership succeed or fail. No actual source implementation of `S_f` or `R_r`
is asserted by this interpretation of the raw signature.

Direct calculation gives:

```text
T_U(k(rho,C)) = true
T_U(J) = true
J >>= S = Request(q,C,(rho,C) -> Return(u,C,omega,tau_resume ++ sigma),
                 omega,tau_request)
T_V(J >>= S) = false, since u not in V.
```

The composed pending observation retains its full continuation. Resuming it
with the sole independently specified algebraic response yields the displayed
complete Return, also failing `T_V`. Membership is not erased by fiat at the
pending tuple: its failure is forced by the fixed descriptor set and complete
resumption result. The request predicate, world predicate, admitted response,
all metadata, suffix, value and current state are unchanged.

This is minimal in request count (one is required to expose the pending
case), nonempty response count (one is required to witness continuation
failure), and state count (one suffices). Two values make both distinct input
and target descriptor sets nonempty. Allowing an empty target would reduce
the value count but would give a less discriminating example. No minimality
claim is made about full Yulang source graphs or original semantic carriers.

## What a closure proof would additionally need

In this finite-tree algebra, suppose every request reachable in the local
computation is legal at `V` under the same admitted-response domain, and
suppose the fixed suffix satisfies

```text
for every reachable local Return(a,C,omega,tau) satisfying T_U:
    T_V(S(a,C;omega,tau)).
```

Then structural induction proves `T_U(J) => T_V(J >>= S)`: the Return case
uses this suffix premise, and each Request branch uses the same response
witness and applies the induction to its child. This is a conditional theorem
about the specified acyclic algebra. It neither derives its predicate clauses
nor covers recursive/divergent or latent-provider semantics.

At the real callee seam, `U` is the callee completion port and `S=S_f` contains
the complete invocation. At the body-consumer seam, `U` is that local consumer's
completion port and `S=R_r` is the actual outstanding invocation shell. These
are instantiations of the *proof obligation*, not two certified source models.
The one witness above only refutes omitting the suffix premise in an abstract
rule. It does not assert that the real `R_r` can violate its ordinary result
contract, or that the real typed Function `F` admits this interpretation.

If an ordinary independent Function/consumer clause already establishes the
suffix premise, it excludes this witness and conditionally discharges this
cut. That clause and its application at the unchanged original witness are
precisely the evidence to supply. Source-contracts §2.2's descriptor filter,
§3.5's assumed local typing, and §5.3's congruence with a fixed continuation
cannot derive it from local typing alone. Equal raw transitions supply no
result-port conversion or world-preservation theorem.

## Independence, omissions and stop condition

No Oracle, executable checker or source validation was used. The reference
for the calculation is the candidate predicate definition; the raw reductions
are shared supplied equations. This is therefore an algebraic nonimplication,
not independent validation of the transition rules. A checker encoding these
same definitions would add consistency evidence only.

There is one analytical witness, no random seed, enumeration range, executable
mutation or measured performance sample. Its named shortcut is deletion of
the saved-suffix preservation premise. The witness uses unchanged value/state,
true request/world clauses and a fixed nonempty target to isolate that deletion.
It fails as a source counterexample as soon as ordinary provider membership,
consumer typing or output inclusion is required and independently established.

Unverified: complete descriptor/carrier/world/admission clauses; actual original
operand inhabitance; handler/protection/expiry satisfaction; all possible
response domains and repeated resumptions; divergence and recursive or latent
returned providers; source licensing/association; Option 2 extras; whole-source
adequacy, principality and production correspondence. No repository-wide
absence theorem follows from the bounded inspected sources.

The earlier two attempts and this raw algebra leave the same complete ordinary
semantics premise untouched. The lane stops rather than enlarging the example
or treating another toy probe as gate progress. Recommended next action:
extract or construct the ordinary pending Bind/suffix preservation clause
inside `DESC_CLAUSES`/`SEM_JOINT`, then instantiate it at `kf >>= S_f` and
`ka >>= R_r` with their original admitted-response/world operands.

## Commands, resource use and dependency snapshot

Checks run: bounded `cat`, `sed`, `rg` source reads; read-only
`git rev-parse HEAD` matching the pinned baseline; leased-path absence check;
Python read-only `git show BASE:path` byte/hash comparison of the eight direct
inputs below. All matched the pinned commit. Initial aggregate source captures
were truncated; governing excerpts were reread narrowly. Searches covered the
assigned locators only. No semantic execution, tests, builds, formatter, Git
mutation, child delegation or production/shared-file write ran.

Budget: at most 15 minutes; text-only calculation, zero heavyweight processes
and zero executable probes. A preliminary independent-read batch used up to
four lightweight source processes; subsequent reads/hash checks were serial.
CPU and peak memory were not instrumented. Wall time is returned in the
handoff only if measured; no performance claim is made. Final artifact
integrity and dependency recheck are returned in the freeze handoff.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `notes/theory/successor-proof-obligations.json` | `e866faaf68a813b95c80dcf46904a1e1f8dfbc5906b3ca019cd8e565eca9ffae` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/progress/2026-10-08-call-type-computation-entry-attempt.md` | `0c87d266bdc76b061c5c9e09351723c7c1af4da8f3fca41abc1a4aa184c75dc9` |
| `notes/progress/2026-10-07-call-type-local-law-falsification.md` | `9e521a9543d0f523572b8f7e2f838b1ff63063385a239d651e85287e9f89f33f` |
| `notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md` | `564deef056a8609fb570d7a4a17c33f0ee14d3d49c6eb7f87c1b1d91c3f0fa43` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-call-type-pending-closure-falsification.md`.
- Baseline SHA: `fd6434993f02d85221642ab2c4047eb63798f9ca`.
- Dependency hash changes: none in the eight baseline comparisons; final freeze recheck in handoff.
- Review status: frozen unreviewed producer artifact; no independent-review or gate-closure claim.
- Checks already run: governing/prior-note reads, baseline equality, path absence, eight dependency byte/hash comparisons; final narrow integrity check in handoff. No executable semantic checks.
- Proposed one-line commit message: `research: separate local continuation typing from pending Bind closure`.
- Shared-record deltas left for primary/curator: optionally link this reduced-premise witness and the explicit suffix-preservation premise; retain `CALL_TYPE`, `DESC_CLAUSES`, `ADMISSION_CLAUSES` and `SEM_JOINT` open. No task, index, authority, theory, manifest, lockfile, other worker's file or question-board bundle changed.

## Independent review

The compiler-referee found no blocking, major or minor issues. The sorted
one-request witness preserves the fixed tuple, response, state and suffix and
correctly distinguishes raw-algebra nonimplication from a `SEM_JOINT` or
admitted-source counterexample. The conditional finite-tree induction retains
its explicit suffix-preservation and request-legality premises. Exhaustive
semantic realization, source admission, recursive/latent providers and
production correspondence remain unverified.
