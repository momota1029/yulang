# Zero-word closed filters: conditional registration and discharge derivation

Date: 2026-10-10
Status: conditional derivation; independent spec-auditor review found no
BLOCKING, major, or minor finding; research-only, no production certification
Baseline: `7f8c7aed4cfa057c04c3b9eee943152ced610fa0`
Oracle reference: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Producer: one prover-equivalent fallback worker; no custom `prover` execution claimed
Scope: finite Identity/closed zero-word PrefixLeft/ordered Replay contexts, one canonical EffectRow receiver, ordinary current/future concrete lower checks
Authority: [contextual attachment design](../design/2026-10-10-contextual-attachment-admission-design.md) §§3–4 and [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md) §§1–5

This note derives a local replacement lemma from explicit retaining-bound
premises. It does not establish that source construction supplies those
premises or that the active implementation satisfies them. The existing
[closed-filter payload checkpoint](2026-10-10-closed-annotation-filter-payload.md)
records a representation change; its status is not a theorem. The older
[source correspondence audit](2026-10-10-contextual-effect-source-correspondence.md)
is used for its exact Oracle locators, not its historical callback result or
historical successor-gap statements.

## Statement and frozen hypotheses

Let U be the universe of resolved, nullary concrete effect identities admitted
by this fragment. Equality in U is resolved identity equality, not spelling.
Symbolic variables are not members of U. For each source-owned LocalWeight
identity w, fix an immutable allowed set A_w subset U and its exact source view
view_w, boundary, owner, position and source derivation. Multiplicity in a
stored member list is irrelevant to set membership but does not authorize
dropping source operand or boundary evidence.

The context grammar is exactly:

```text
C ::= Identity
    | PrefixLeft(w, Identity)
    | Replay(C_lower, C_upper)
```

The Replay children are ordered and can share node identities. A finite list
notation Replay(C_1,...,C_n) means a supplied ordered bracketing of binary
Replay; n=0 denotes Identity and n=1 denotes that child. This notation does
not add another production constructor. The represented graph is finite and
acyclic. Each w has empty left operation word and empty right POP word. There
are no operation-bearing contexts, Function transforms or other constructors.

Define B(C), the ordered sequence of boundary *occurrences*, by:

```text
B(Identity)                 = []
B(PrefixLeft(w, Identity))  = [w]
B(Replay(L,R))              = B(L) concatenated with B(R)
```

An occurrence includes its path and exact retained relation/source derivation;
writing only w above abbreviates that occurrence. Let D(C) be the distinct
weight identities in B(C), ordered by first occurrence. Define intersection of
an empty boundary sequence to be U. The filter interpretation is the existing
zero-word specialization:

```text
F(Identity)                = U
F(PrefixLeft(w, Identity)) = A_w
F(Replay(L,R))             = F(L) intersect F(R)
```

Fix one actual canonical EffectRow receiver r, and assume:

1. **Closed exact view.** For every w in D(C), view_w is closed: it has no
   symbolic tail. Ordinary comparison of concrete atom a against the exact
   `Allowance(view_w)` accepts precisely when a belongs to A_w. The view and
   payload agree on allowed members, boundary, owner and position, and remain
   immutable. Mixed-tail views are excluded: an unlisted atom may otherwise
   flow to a tail, contradicting this membership hypothesis.
2. **Same receiver and propagation.** Each installed bound is the ordinary
   `EffectRow(r) <: Allowance(view_w)` on that canonical r. Every present or
   future applicable concrete lower reaches that same receiver's ordinary
   bound/worklist replay. No lower, alias path or direct insertion silently
   bypasses it. An unresolved variable is permitted to stay unresolved; each
   concrete atom later reaching it and then r is covered when it arrives.
3. **Retained coverage.** Registering the ordinary upper bound checks or
   schedules checks against every current concrete lower of r. The retained
   bound checks or schedules checks against every future concrete lower of r.
   Every scheduled applicable check is eventually processed, or publication
   waits while it is pending. Comparison uses hypothesis 1; memoization and
   equality omission preserve these checks. Installing another derivation of
   an already registered bound preserves its evidence and makes existing
   conflicts reachable from that derivation.
4. **Boundary and derivation retention.** Every distinct w has an independent
   exact boundary registration. Equal sets do not merge distinct source
   boundaries. Every occurrence in B(C) retains its exact source/relation
   derivation and ordered Replay parents, including occurrences of an already
   registered w and shared children. Sharing can reuse an executable bound or
   immutable node, but cannot delete a parent incidence or diagnostic origin.
5. **Atomic lifetime.** Discharge happens only after all registrations and their
   current-lower checks are performed or irrevocably scheduled under
   hypothesis 3. Their bounds, pending work, dependencies and derivations
   survive for the entire lifetime of the discharged relation. Rollback either
   retains the complete route or restores its undischargeable state; it never
   leaves Identity paired with missing obligations. For this statement r is
   fixed. Transport to another representative requires a separate proof that
   hypotheses 2–5 are re-established there before use.

Additional ordinary constraints on r are held the same in both compared
states. The comparison concerns the contribution of C to concrete-atom
allowability, its boundary violation witnesses and retained derivation
incidences. It does not assert identical queue scheduling, first diagnostic
selection, timing, global solving success or termination.

**Conditional theorem.** For every finite C in this grammar satisfying the
hypotheses, and every finite or infinite arrival trace of concrete atoms at r:

- F(C) is the intersection of the leaf boundary sets in B(C).
- Retaining filter C on r and installing the exact ordinary Allowance for each
  w in D(C) impose the same accept/reject predicate on every present and future
  concrete atom, after its applicable checks have been processed. All finite
  prefixes satisfy the corresponding coverage invariant before processing.
- Replacing C's executable filter by Identity preserves these observations
  while every boundary registration, pending obligation and exact source
  derivation remains retained. This is a conditional discharge license, not a
  source reachability or implementation correspondence theorem.

## Constructive context induction

We prove together that the interpreted left/right operation words are empty,
and that F(C) equals the intersection indexed by B(C).

For Identity both words are empty and B is empty; F=U is the empty
intersection. For PrefixLeft(w,Identity), concatenating its empty word with
Identity's word leaves empty words, and its filter is A_w intersect U=A_w,
the singleton intersection. For Replay(L,R), the inductive hypotheses give
empty words on both children. Ordered replay concatenates empty left words
and empty right words; directed mix has no operation to move or cancel.
The retained filter is F(L) intersect F(R). By the hypotheses this equals
the intersection indexed by B(L) concatenated with B(R), exactly B(Replay(L,R)).
The construction terminates by finite height. A finite shared DAG can be
unfolded to this finite occurrence tree for the proof without implementing
that unfolding. Alternatively, the same induction follows a topological order
and retains all ordered parent edges. It uses no operation-count quotient.

For any a in U this immediately constructs the equivalence:

```text
a in F(C)
  iff for every boundary occurrence b in B(C), a in A_weight(b)
  iff for every distinct w in D(C), a in A_w.
```

The last equivalence follows because occurrences of one immutable w have the
same predicate. It does not identify their derivations. The violation witness
is a boundary w with a not in A_w; the occurrence-level witness additionally
selects any exact retained occurrence derivation for that w.

## Constructive registration and arrival induction

Process D(C) in its first-occurrence order. Maintain two finite sets J and T:
J contains registered weight identities, and T contains the concrete lowers
that have reached r. For every pair (w,a) in J times T, retain either a
performed check with result `a in A_w`, or an outstanding check that must be
processed before publication can rely on its result. Also retain the exact
bound/origin dependencies and all B(C) occurrence incidences for J.

Initially J is empty and this coverage invariant is vacuous. Installing w
adds its exact upper Allowance bound on r. Hypothesis 3 supplies checks for
all a currently in T, completing the new column of J times T; existing columns
remain covered. If a new concrete lower arrives instead, the retained bounds
schedule/check it against all w in J, completing the new row of the product.
Adding an occurrence of an already registered w leaves that product unchanged
but extends the derivation incidences and existing-conflict reachability as
required by hypotheses 3–4. These are constructive induction steps for any
interleaving of registrations and lower arrivals.

When J=D(C), processing all applicable checks for a yields the conjunction
over D(C) of `a in A_w`. The context induction identifies this conjunction
with `a in F(C)`. Hence current-lower checks and retained future-lower checks
jointly preserve precisely the filter predicate. Infinite traces require no
infinite induction step: each event lies in a finite prefix, and eventual
processing/publication discipline supplies the stated observation for that
event. This result does not imply a whole infinite worklist terminates.

Replacing the executable filter by Identity changes its local test to `a in U`,
which contributes True. The unchanged retained ordinary upper bounds still
contribute exactly `a in F(C)` by the preceding induction. Existing ordinary
constraints remain conjuncts on both sides. Hypotheses 4–5 retain each boundary
violation witness and its exact source derivations, so removing the redundant
executable filter does not remove those obligations or explanations.

## Empty sets, sharing, equal sets and Replay order

If B(C) is empty, D(C) is empty and the predicate is True for every concrete
atom; no registration is needed. If some A_w is empty, the conjunction is
False for every concrete atom. A receiver with no concrete lower can still
carry that empty Allowance successfully; its first later concrete lower must
fail that boundary check. Bottom or an unresolved variable is not a concrete
atom and is not rejected by treating it as one.

Repeated occurrences of the same w, including `Replay(X,X)` for a shared X,
repeat an idempotent predicate. One exact executable bound for that w can cover
all those occurrences, provided every parent/occurrence derivation remains
reachable. Different weights with equal A_w are separate source obligations;
each gets its own exact registration and origins even though their predicates
coincide. Equality of receiver rows also cannot mint a new boundary identity.

Replay order and bracketing are retained in B(C) and the derivation graph.
Intersection happens to be commutative and associative in this restricted
empty-word fragment; only its *Boolean membership result* is order independent.
That fact does not license sorting children, replacing the Replay node,
merging parent derivations or extending this lemma to nonempty operations.
First failure or diagnostic presentation order is not proved equivalent here.

An aggregate intersection can aid a membership calculation. It cannot replace
the required separate registrations/provenance. For example, two distinct
boundaries with the same set have the same aggregate after either boundary is
deleted, yet one source obligation and its diagnostic origin have disappeared.
For unequal sets, an intersection only says that an atom fails at least one
boundary; it does not retain which original Allowance and source derivation
failed. An implementation may share computation only while preserving every
exact boundary registration and its dependencies.

The phrase "only while retained" expresses the governing discharge invariant
and this proof's license. It is not a mathematical claim that every missing
redundant registration changes Boolean membership: equal sets and U-valued
filters show otherwise. Without hypotheses 4–5 the richer boundary/source
contract is no longer justified even in those redundant cases. Deleting all
checks after discharging an empty boundary supplies a direct Boolean failure:
a later atom passes Identity although the original empty filter rejects it.

## Exact source bridge supplied and still missing

The Oracle constructors/consumers inspected at the frozen reference give the
retaining-filter rule directly:

- `constraints/mod.rs:3566–3612` preserves the supplied order for left prefix
  and Replay; `constraints/directed_weight.rs:290–295` composes their filters
  by intersection. Empty-word specialization therefore supplies the context
  induction's operations without an extra semantics.
- `constraints/machine/bounds.rs:3174–3210` checks/registers before erasing the
  left filter. `:3213–3255` registers on the actual variable and checks existing
  lowers; `:3285–3303` checks future lower insertions. `:3257–3283` retains
  provenance derivations even when a filter set is already registered.
  `:3305–3360` follows variables and concrete/row/union shapes rather than
  declaring a variable empty. These are source evidence for the ordinary
  retention premise, not a proof that the successor has reproduced it.

At the successor baseline, `candidate_effect.rs:753–817` shows the relevant
closed Allowance comparison: `allowed.contains(effect)` accepts; an absent
tail otherwise creates a mismatch. A present tail forwards an unlisted atom,
which is why hypothesis 1 explicitly excludes mixed-tail views.
`candidate_extrusion.rs:726–754` selects the negative upper bound on the
canonical receiver for row-to-Allowance; `candidate_insert_bound_impl`
retains the upper endpoint and bound origins, and `candidate_replay_bound`
at `:645–690` enqueues every current opposite bound. Future lower insertion
uses the same opposite-bound replay. These are precise owners for validating
hypotheses 2–3, including indirect variables and worklist reachability.
They do not alone prove that every actual insertion path schedules every
required check.

The baseline `candidate_context_execute` at `candidate_context.rs:1710–1770`
executes only a direct PrefixLeft(w,Identity), and its bound/origin/replay path
is the earlier single-filter checkpoint. It refuses other context constructors.
Thus the multi-leaf registration bridge is deliberately unproved at this
baseline. In particular, a future worker must establish, on its frozen delta,
that all distinct closed w in the exact Replay graph register on the same
canonical receiver, all current/future lowers are reached by ordinary replay,
and every source/relation incidence survives discharge and rollback. This
worker's ongoing source delta is not an input to the present derivation.

The remaining minimal operational premise is hypotheses 2–5 for the worker's
actual registration/retention transitions; source ownership and closed-view
identity under hypothesis 1 must also be inspected at their producers. No
additional mathematical premise is needed for the finite context induction.
The note constructs no source program, admission recognizer or certificate.

## Dependencies, verification and handoff

All semantic/source reads above use pinned Git objects. SHA-256 dependencies:

| Baseline path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/progress/2026-10-10-contextual-effect-source-correspondence.md` | `8a0fe8fe0e49b7a781f87f020e1b39e2418fbbaee9fb17082fa9b91bdc30e87c` |
| `notes/progress/2026-10-10-closed-annotation-filter-payload.md` | `2f00e9e0190c296068939c14a6d45c433d38d450ec1686c69533ba4820cef808` |
| `crates/yu-solver/src/candidate_context.rs` | `efb9814b5eb3b604b48d63420adcf2de1ff4a39bf0296495b75fc50dac1bdf55` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |

| Oracle path | SHA-256 |
| --- | --- |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |

Verification is limited to constructive paper induction, pinned source reads,
dependency hashing, and leased-file whitespace/link/locator inspection. No
tests, builds, execution probes, Oracle execution, measurements, subdelegation
or Git mutation. Measurement count: zero samples and zero benchmark processes.
Only this note is written. Independent spec-auditor review accepted the stated
conditional derivation and confirmed source/runtime correspondence remains
open. The producer does not promote theorem status or certify the active
candidate implementation.

Excluded: mixed-tail Allowances, nonempty operations, Function transforms,
`BothFromRight`, residual/gamma construction, recursive certificates, concrete
negative formal admission, whole-source correspondence, transport/equality
lifecycle outside the stated invariant, complete Call, full hygiene,
soundness/principality and public cutover.

Commit packet: this note only, baseline as above; proposed message
`research: derive conditional zero-word filter discharge`; independent review
pending. Shared `tasks/current.md`, design/theory status and research queue
synchronization are deferred to the primary. Next action: freeze the active
worker's delta and assign a fresh compiler referee to the conditional
derivation and its exact registration/retention correspondence.
