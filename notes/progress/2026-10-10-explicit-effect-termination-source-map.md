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
Frozen Oracle does have a source-owned producer, including the recursive
returned-Function path recorded below. The successor's refusal is not a proof
that its future constructor will avoid those paths.
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

## Callback invocation versus tuple annotation predicates

A follow-up Oracle source trace used the concrete recursive shape
`my loop (f: int -> [io] 'c) = { my unused = loop f; f 1 }`. It confirms that
calling `f 1` activates the annotation's grant `i` and puts its `POP_i` on the
public output wrapper of the containing lambda. The annotation's positive
return effect sends `PUSH_i` into the callback result path. However, the
already-formed recursive `loop f` skeleton still has identity context on its
`O <: C_rec` return-effect child: the `f 1` predicate is not applied to that
child while the body is assembled. The public wrapper is attached after the
recursive skeleton boundary.

This rules out that particular source path as a witness for a right-POP edge
on the recursive parent. It does not prove that every source shape lacks such
an edge. In particular, it does not cover tuple parameter annotations, whose
child predicates are retained before the body is lowered.

Pinned Oracle source establishes this pre-body producer for
`type io; my loop(x: ((int -> [io] 'c), int)) = loop x`: the nested Function
annotation's `POP_i/{io}` is returned through `AnnType::Tuple`, retained by
the lambda parameter boundary, and inserted on both Value and Effect
skeleton-output bridges before body lowering. Its exact owner path is
`annotation/constraints.rs:335–349,363–389,424–470` and
`lowering/expr/lambda.rs:756–767,1186–1237,1571–1578`. Top-level Function
annotations clear this predicate; Tuple annotations do not.

A returned-Function shape exposes the POP to a nontrivial contravariant child:

```yulang
type io
my loop(x: ((int -> [io] 'c), int)) = \z -> (loop x) x
```

After the body lambda is formed, the recursive result is first used as a
Function, and Function comparison under the retained left POP swaps it to a
right POP on `P <: Z`, where `P` is the tuple-annotated `x` formal and `Z` is
the distinct anonymous `z` formal. The POP does not arise on the immediate
recursive effect child; it arises on this returned Function's contravariant
Value child. The source trace and locators are detailed in
[`contextual-effect-source-correspondence.md`](2026-10-10-contextual-effect-source-correspondence.md).

This proves a source-construction route to a right-POP contextual Value bound,
not an accepted-program or global-termination result. It does not yet prove
that tuple decomposition and Function replay return to the same eligible bound
slot, generate unbounded POP counts, or realize the powers-of-two grammar
witness. In the first inspected source shape, `z` is unused: its upper endpoint
never gets a tuple demand, so `P <: Z` remains a Value alias and does not
decompose into the nested callback Function's effect ports.

A real tuple-pattern consumer does add that demand:

```yulang
type io
my loop(x: ((int -> [io] 'c), int)) =
  \(f, _) -> { f 1; (loop x) x }
```

The lambda pattern creates `Tuple(F+,M+) <: Z` and `Z <: Tuple(F-,M-)`;
tuple descent preserves the right `POP_i` on `P <: Z`, so the annotated
callback Function reaches `F` under that context. The `f 1` use supplies its
negative Function demand. Its return-effect `PUSH_i[{io}]` cancels the incoming
right `POP_i`, while its return-value `NonSubtract(...,POP_i/filter{io})`
combines with that right POP to produce right `POP_i²` after filter checks.
The callback result is discarded, however; this edge does not return to the
same nested Function comparison. The recursive block also forms separate
output-alias cycles, but its recursive call uses `x`, and the resulting
same-variable child is omitted by Oracle admission. Exact locators and port
equations are in
[`contextual-effect-source-correspondence.md`](2026-10-10-contextual-effect-source-correspondence.md).

This establishes an actual source-construction route through tuple descent to
an effect cancellation and an unmatched `POP_i²` result-value context. It
still does not establish repeated growth at that callback Function slot,
accepted/public output for the source, or global termination. Other consumers
of the callback result, projection-generated Tuple uppers, extrusion and
generalization remain to be traced. The successor currently rejects the
explicit formal effect row and does not support this Tuple annotation route;
that is not evidence that it is safe to omit from Oracle correspondence or
future source support.

The callback result target is settled as
`(int -> ['b, io] 'c) -> ['b] 'c`; the extra `int ->` in the earlier
conversational version was a mistake. It remains unverified in the successor.

Next: trace uses that consume the callback result as a Function (and tuple
projection or extrusion paths) to determine whether its unmatched `POP_i²`
context can return to the same callback Function slot. In parallel, derive
the contextual admission/observation relation for the source-emitted
operations; do not add a POP producer until port ownership and termination
behavior are established. Then implement the source-owned filter consumer and
the exact callback scheme regression.
