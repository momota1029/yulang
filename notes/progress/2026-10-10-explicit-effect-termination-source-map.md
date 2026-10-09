# Explicit effect attachment: contextual-cycle source audit

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `b54e03d97687d0baa39dfb5b25d13094b556ab54`
Authority: selected annotation policy and user-supplied callback example in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
Claim class: pinned-source audit plus conditional model counterexample
Mode: M2 design/source conformance; no compiler writes or execution probes
Status: successor admission quotient and recursive source-cycle correspondence open

## The concrete target

The user supplied:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

with expected scheme:

```text
(int -> ['b, io] 'c) -> ['b] 'c
```

This is the scheme recorded in the Authoritative hygiene integration note.
The earlier direct user message in the continuing thread wrote an additional
`int ->` before the result effect. A later “ソレはミス” did not identify which
statement it corrected. Until clarified, this record preserves the original
source example and the unresolved disagreement; neither displayed scheme is
silently substituted for the other as the final owning regression target.

The annotation-scoped interpretation and limit are recorded in the governing
authority §6. This is a concrete hygiene target: `io` is available to the caller
as part of the callback's effect row, the body-local handler removes only that
attached `io`, and independent `'b` effect flow remains. It is not an assertion
that the current successor parses/accepts the expression or has completed Call
semantics.

At baseline `b54e03d97`, HIR already resolves nullary concrete effect IDs and
retains nested formal effect rows. The private candidate has covariant support /
allowance consumers, but `candidate_source::preflight_formal` and
`candidate_effect::candidate_formal_pair` reject every explicit formal effect
row; `candidate_signature_effect` also rejects concrete rows at composed
contravariant positions. No source-level negative filter exists yet.

The separate [finite model](2026-10-10-explicit-effect-attachment-finite-model.md)
compares contextual event propagation and relational reachability on 72 supplied
input valuations and 85 polarity paths. It detects seven shortcut mutations,
including row-global removal, lost future checks and loss of copied boundary
identity. Its source incidences are supplied assumptions; it is unreviewed
research characterization, not compiler correspondence or a hygiene theorem.

## Revised weighted-cycle finding

The conditional context algebra admits an infinite closure if every exact
normalized context is eagerly memoized. Two edges suffice:

```text
r <: s under POP_i
s <: r under identity
```

Their joins generate contextual self-edges and then repeatedly larger pop
counts in the extrapolated model. This correctly falsifies termination of that
unrestricted closure algorithm. It does **not** show that the frozen Oracle
worklist diverges or that its selected semantics need a numeric cap.

Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` contains the exact owning
API case `crates/infer/src/constraints/tests/case_01.rs:950–986`, named
`var_var_replay_keeps_pop_only_alias_cycle_finite`. Source inspection (the test
was not executed) establishes these distinct owners:

- `machine/entry.rs:1101–1105` drops any same-TypeVar `Pos::Var(x) <: Neg::Var(x)`
  constraint before it becomes replay fuel, regardless of attached weight.
- `machine/bounds.rs:3456–3473,3626–3676` composes exact replay weights and runs
  canonical admission before enqueueing. The self-edges from the two-edge case
  are therefore classified trivial.
- Exact weight composition preserves repeated pops (`case_01.rs:251–269`).
  For nonself aliases, separate lower/upper bound subsumption keys
  (`bounds.rs:4274–4317,7204–7233`) project positive count magnitudes to their
  support shape after checking/erasing insertion filters. They constrain bound
  admission without rewriting exact replay weights.
- `row_effect.rs:128–170` has additional weighted row-tail/same-row guards;
  structural row matching also avoids a reverse tail cycle at
  `machine/propagate.rs:783–815`.

Thus termination is not explained by treating repeated `POP_i` as semantically
idempotent. Oracle has actual self-edge and bound-admission owners absent from
the finite transition extrapolation. The inspected case establishes only its
own transition, not a general source-to-machine proof, full inference
termination, or successor equivalence. Source reachability of the exact initial
graph remains unestablished.

## Required successor correspondence before the production constructor

Do not copy either Oracle shortcut directly into successor bound insertion yet.
The successor uses one-sided level-selected bounds and parent/copy SCC equality;
its exact contextual owner relations differ. A future implementation must show:

1. A contextual self-constraint can be omitted only after its actual filter,
   future-lower registration, residual/output and attachment obligations are
   accounted for, including equality introduced by intrusion.
2. Any support-based subsumption preserves all suppressed-bound consequences:
   insertion checks, future lowers, opposite-bound replay, nested Function
   variance, concrete residual consumption and attachment origins. Exact counts
   remain on any retained replay context; a support key is only an admission
   quotient.
3. Extrusion, freshening and intrusion reindex every boundary/attachment
   reference, retain distinct boundaries on merged rows, replay invalidated
   constraints and restore all new state on failure.
4. The user callback target retains `io` at the caller boundary, removes only
   the body-local attached `io`, and leaves `'b` flow visible. The same-family
   independent route, returned latent Function, future lower, fresh-use and
   rollback controls remain in the focused owning matrix.

A finite IDs count alone does not bound contextual multiplicities. The Oracle
source case suggests faithful finite termination guards, but their successor
invariants are unproved. No user-level semantic decision or arbitrary fixed
resource cap is implied. This remains an algorithm/source-correspondence gap;
implement only after an exact successor owner derivation, not by suppressing
self-edges or count growth to make the model terminate.

## Successor admission quotient and recursive source route

A follow-up owner audit compared a finite support-shaped admission candidate
against exact replay. The candidate key records bound kind/owner/side/endpoint,
the attachment IDs and whether each has a positive or negative count, plus
source dependencies. It is finite for fixed endpoints and attachment
instances, but it is **not** a replay congruence by itself:

```text
PUSH_i ; POP_i   = identity
PUSH_i ; POP_i²  = residual POP_i
```

`POP_i` and `POP_i²` have the same presence signature, while an opposite
`PUSH_i` bound distinguishes their exact replay. This is an algebraic
obstruction to using that signature alone, not an executable source
counterexample. Any covered-bound admission must retain an explicit entailment
dependency proving that the retained representative preserves insertion
checks, future lowers, opposite replay, Function variance/entry transfer,
residual projection, origins, remapping, SCC invalidation and rollback. No such
certificate exists in the current successor owners.

The present successor cannot yet produce a source-owned POP cycle because the
source constructor is absent: explicit formal effect rows remain rejected at
`candidate_source::preflight_formal` and `candidate_effect::candidate_formal_pair`,
and contextual operations are absent from `TypedPairKey` and retained bounds.
This refusal is not a proof that the future constructor will avoid cycles.
The ordinary recursive back route already exists; the paired-formal regression
at `lib.rs:32267` uses:

```yulang
my recur (f:() -> int) = { my unused = recur f; f () }
```

Its source-owned flow is published result effect `W` to recursive invocation
`I`, recursive application `A`, block effect `B`, then enclosing returned
effect `R`. If an attachment constructor publishes `R <: W` under `POP_i`,
the existing route closes a contextual cycle. Owners include live recursive
component roots (`candidate_scheme.rs:615–620,683–690`, `lib.rs:14861–14880`),
Function return-effect comparison (`lib.rs:11926–11930`), invocation/application
(`shadow_apply.rs:1423–1435`), initializer/block flow
(`candidate_source.rs:238–244`), and body/returned-effect flow
(`lib.rs:11135–11172`).

This remains conditional: the POP-bearing publication premise is not currently
constructed, and the source fixture cannot execute that path today. Levels
select retained-bound ownership but do not prohibit these inequalities; a
level argument alone does not establish acyclicity. For an acyclic placement
graph, path composition bounds each POP count by finite path length. That
conditional fact does not extend to recursive exposure or equality introduced
by intrusion. The next derivation must establish whether authentic output
construction places the POP-bearing result on recursive exposures, or prove a
different ownership relation that prevents that edge while retaining latent
output and future-lower behavior.

## Verification and next action

Primary rechecked the conditional finite model with its exact embedded command:
72 valuations, 85 polarity paths and seven named shortcut witnesses pass. One
Python process; no Cargo/build/test or timing benchmark ran.

The Oracle cycle test and its admission/bound owners were inspected from pinned
git objects; no Oracle test was executed. A read-only source-owner map confirms
the HIR/candidate refusal points. No source-to-successor cycle derivation,
weighted production implementation, whole Call verification, soundness or
principality proof ran.

A read-only successor audit additionally established the ordinary recursive
back route and its conditional POP-cycle falsifier; a separate architect audit
showed that per-attachment count-presence admission loses exact replay
distinctions. These are source-owner/algebraic findings only. No source POP
producer exists yet, no finite quotient is proved, and no code, compiler tests,
or measurements ran.

Next: decide whether authentic annotation construction puts the POP-bearing
result edge on recursive exposures; if so, derive a finite ownership/admission
relation preserving all live effects before enabling contextual production.
Then implement the annotation boundary/filter consumer and add the callback
target as an end-to-end source regression. The exact accepted callback result
spelling is pending clarification of the user's later “ソレはミス” correction;
do not infer that it removes the displayed `int ->` result segment.
