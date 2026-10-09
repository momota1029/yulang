# Mixed contextual subtraction: a source cycle and an exact terminating observer

Date: 2026-10-10
Status: mathematical theorem, repaired source correspondence and research implementation independently reviewed within their stated scopes; whole-source and production gates open
Branch: `research/simple-sub-intrusion`
Starting remote: `e2f29d0a30f81616b4963cb1b2a42d9a798af2b3`
Mathematical checkpoint: `3b32ed3afa49c7d4105da46ba7783524c9fdb35b`
Integration base: `92f07a067ae241061afec2b8877c449fefabcc66`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: the continuing user task and the selected annotation hygiene policy
Scope: one attachment ID, cyclic debt derivations, finite mixed observations;
no new source rule, production solver, semantic count cap, or cutover

The continuation fetched and inspected concurrent upstream source-owner audits
`70d529702` and `3bb355b56d5399b297bad2faa50940c3817f88b1`, then fast-forwarded
before publishing the mathematical checkpoint. Those prior audits are retained
upstream work. Their changes did not modify the compiler or the exact operation
definitions used by this theorem.

A final fetch also incorporated `a637ba28` and its merge `92f07a06`, which add
the [paired annotation PUSH bridge](2026-10-10-paired-annotation-push-bridge.md).
That upstream source note was read and its stated limits retained. No compiler,
governing count operation, proof equation or research implementation changed.
Its historical uncertainty about an earlier conversational correction is not
resolved here: the current user request explicitly states the expected scheme,
so shared records now use that written target while keeping it unexecuted.

## Concrete result

The previous one-sided result now extends to arbitrary **debt-only cyclic
derivations** with directed replay, swap, both-from-right, and explicit sharing.
Every fixed finite continuation may contain PUSHes and all those mixed
operations. Its active count and pending/side-presence observations at every
node are decidable exactly by finite saturation. Cyclic doubling is included;
the exact numerical language need not be regular or context-free.

The complete definitions, independent reference semantics and proofs are in
[the reviewed observation theorem](2026-10-10-mixed-replay-observer-construction.md).
Its reviewed checkpoint is `3b32ed3afa49c7d4105da46ba7783524c9fdb35b`.
The separate [algebraic attack](2026-10-10-mixed-replay-algebra-attack.md)
proves the required strict threshold and records bounded literal/count checks.

An actual annotated recursive callback also supplies a debt-only circuit that
returns to the **same Function lower/comparison slot**, with natural counts
`1,5,9,...`. This goes beyond the previous discarded-result source trace.
The [source certificate](2026-10-10-mixed-replay-source-cycle.md) gives the
constructor, consumers, primitive aliases, filters and admission owners.
It is not a parsed/executed Oracle fixture or an accepted-program claim.

The implementation is
[`research_mixed_debt_observer.py`](../../tools/research_mixed_debt_observer.py).
It stores the original immutable grammar, computes an actual finite least fixed
point for each observation, and retains the distinction between independent
children and one shared chosen child. It is a research implementation; no
successor compiler module or public inference route was changed.

## 1. What is finite, and why the finite answer is exact

For one ID use raw weights `W=(p,n,r)`: left leading POP count, left active
PUSH count, and right POP count. The recursive debt region has `n=0`.
Within that region, the source operations only add nonnegative debts,
move/copy coordinates, or branch on zero versus positive. In particular:

```text
swap(p,r) = (r,p)
both(p,r) = (r,r)
replay((p,r),(q,s)) = (p+q,0)          if r+s=0
                      (0,p+q+r+s)    otherwise.
```

For a finite bracketed continuation C, let B be the total number of PUSH
occurrences in its expanded finite expression, counting each syntactic use.
Define `q_B(p,r)=(min(p,B+1),min(r,B+1))`. This map commutes with every
debt-region operation. The exact grammar therefore has a finite image with
at most `(B+2)^2` states per nonterminal. Each successful saturation update
adds one previously absent state. Induction on finite derivations proves both
soundness and completeness, including independent choices and explicit sharing.

The observation proof does not pretend the representative is the exact debt.
At a continuation node v, let b_v be its subtree PUSH mass and K_v=B-b_v.
The exact and representative executions have equal n, while their p values
agree or both exceed K_v, and their r values agree or both exceed K_v+n.
The last term reserves PUSHes already present in a raw mixed weight. At replay,
sibling budgets make every cancellation comparison agree; swap and both discard
PUSHes rather than creating them. This proves the invariant at every node.
Thus active counts, left/right entry existence, pending debt, identity, and
the specified local filter/residual observations agree exactly.

`B+1` is derived from the actual query, not chosen as an accepted-input limit.
The original grammar remains intact. A future query with more PUSHes is solved
again from that grammar. Using a previous finite image as permanent replay
authority would be unsound. `B` alone is also insufficient: PUSH^B exactly
cancels right POP^B but leaves pending debt for right POP^(B+1).

This resolves the old powers-of-two obstruction for these observations:
`T -> R1 | replay(I,both(T))` is handled without enumerating its unbounded
derivation depth or claiming a regular exact output language. It does not
resolve a recursive grammar that itself introduces unbounded PUSH mass.

## 2. Authentic source connection and corrected four-port mapping

The fixed source certificate is:

```yulang
type io
my loop(x: (('c -> [io] 'c), int)) =
  \(f, _) -> {
    my unused = (loop x) x;
    (loop x) (f f, 0)
  }
```

The tuple annotation carries a source-owned POP predicate before body lowering.
The first call supplies the annotated positive Function A+ to the tuple-local
callback F under right POP. The second call passes the result R of `f f`
back as the callback component. C is the annotation's shared Value variable.
The primitive retained circuit is:

```text
A+ <: F @ R1
F  <: C @ L1
C  <: R @ R2
R  <: F @ R1.
```

Starting from `A+ <: F @ Rq`, those three aliases produce
`A+ <: C @ R(q+1)`, `A+ <: R @ R(q+3)`, and
`A+ <: F @ R(q+4)`. The distinct concrete Function lower keys are not
eligible for the inspected Var-only alias support suppression. This proves
inclusion of the progression `q=1+4k` in the natural-count derivations. It
does not assert that the entire source has only those contexts, that Oracle's
finite-width runtime diverges, or that every optional runtime configuration
has an identical insertion schedule.

The corresponding three-nonterminal debt grammar is:

```text
SF -> R1 | replay(SR,R1)
SC -> replay(SF,L1)
SR -> replay(SC,R2).
```

Each source Function child is a finite continuation of its SF input:

| Port at context Rq | Actual operation and observation |
| --- | --- |
| Value argument | Swap to Lq on `F <: C`. |
| Argument Effect | Swap to Lq on `Earg <: Row([],Top)`. |
| Return Effect | Prefix the matching PUSH_i, then mix: identity at q=1, right debt q-1 thereafter. |
| Return Value | Prefix the source POP_i/filter, check/register it before erasure, then mix to right debt q+1. |

The argument-Effect correction is essential. An annotation's absent argument
effect uses `pure_effect_bounds()`, whose negative endpoint is `Neg::Row([],Top)`.
The special propagation branch tests the distinct constructor `Neg::Bot`.
Consequently this annotated callback **does not** select both-from-right.
The first source draft claimed otherwise; independent review refuted that
claim from the constructor and branch condition. The Value recurrence survives
the correction. Synthetic cyclic-copying checks remain algebra tests, not a
claim that this source selects that branch.

The exact circuit and all its four immediate local count observers fit the
proved interface. The source note supplies the inspected constructor-to-algebra
instance; the new theorem decides this circuit and those observations. Oracle
parsing, successful lowering/generalization and accepted-program behavior were
not established. In particular, the local `my unused` binding drains work before
the returned Function is connected. The constructor-order argument does not
prove that all such earlier gates succeed. No assertion follows that every
cyclic region or complete residual output of the source fits this interface.

### Refuted shortcuts and repaired factual claims

1. A uniform marker B instead of B+1 loses a genuine observation. For B>=1,
   right debts `R_B` and `R_(B+1)` have the same B-clipped state. Replaying
   `PUSH^B` on the left yields identity for the former and `R_1` for the latter.
   A subsequent swap exposes a left entry only for the latter. This is the
   strict-threshold counterexample, not a claim of source reachability for an
   arbitrary future PUSH owner.
2. A permanent support/presence key is not an exact future-replay congruence.
   The B=1 instance already distinguishes `R_1` from `R_2`. The new finite image
   is justified only for the chosen query and its debt subgrammar. It is not
   authority for deleting a source bound, contextual self-edge, registered
   filter or residual key permanently.
3. The annotation's absent argument effect is not `Neg::Bot`; it is
   `Neg::Row([],Top)`. Thus the claimed actual copying child was false. The
   corrected Value circuit survives and the two ordinary argument ports swap.
4. Family erasure or filter rejection does not erase a context's active count
   or its entry. At n=2, subtracting the sole family head leaves count 2 and a
   left entry; at n=1, a rejecting empty allowance reports a violation while
   retaining count 1. The first research implementation violated this contract
   and was repaired before publication.
5. Variable-name identity is not binding-occurrence identity even in a test
   reference. With `A=L_1` and `B=R_2`, the expression
   `let t=A in replay(t, let t=B in t)` denotes `R_3`. A single name-keyed
   witness choice can instead give `L_2` or `R_4`. The actual grammar evaluator
   was already lexically scoped; the reference helper now keys witnesses by
   syntax occurrence as well.

The previously reviewed nonassociativity and general support counterexamples
remain unchanged. No reassociation, self-edge omission or Oracle alias-guard
port is used by the new implementation.

## 3. Executable contract and review repairs

The grammar implementation retains exact immutable productions; finite state
sets are temporary query results. It supports debt constants, replay, swap,
both-from-right, POP prefix/suffix, independent nonterminal occurrences, and
explicit `let`/`bound` shared choices. The observer preserves bracketed finite
arithmetic, reuses each named hole consistently, and exposes observations at
stable syntax-occurrence paths as well as the root.

The local terminal helper reports four distinct fields:

```text
active_count     = n
left_entry       = (p>0 or n>0)
residual_family  = S minus H
filter_violation = n>0 and residual_family is not a subset of the allowed set.
```

No count is erased when the family becomes empty or a filter fails. The initial
implementation incorrectly erased count and entry in both cases, and one new
test encoded that error. Independent semantic review found it; pre-write spec
review confirmed the corrected expectations against the existing theorem.
The repair keeps contribution-family content, count presence, and failure
separate. This is not a weakening of an existing compiler test contract.

### Independent review and verification

There were three independent review lanes in the first coherent round:
mathematics, source correspondence and research code. The mathematical lane
found no blocking/major defect. The source lane's B1 and the implementation
lane's accepted repairs were adjudicated, repaired as a batch, and checked in
a second round containing a pre-write terminal-spec review and fresh source
and code closure reviewers. No producer certified its own output. The
pre-write specification pass checked the stated mathematical contract; the
separate mathematical/source reviewers inspected pinned source objects.

| Review target | Frozen reviewed SHA-256 | Outcome and scope |
| --- | --- | --- |
| Main observer theorem | `e00a6db54fa05f5edbb75c7c87d1177e39a67b7de3851527874cc3f4ff3c0549` | No blocking/major defect in debt congruence, finite least-set saturation, raw-state invariant, sharing or query reconstruction. Published proof/status at `3b32ed3a`. |
| Repaired source certificate | `055a404814fd02c873e11d252921a7b873eae838c45200c6fd4ed111d858a1d7` | B1 closed; primitive concrete-lower recurrence supported. No program parsing, execution or acceptance certification. Primary later corrected two minor source pointers and made the scheduling caveat explicit. |
| Repaired research implementation | `763ecbb015e904d554a0ad62d57f47e2edf0897f61197404e0a6bff081e54c2d` | Accepted terminal, unclipped-continuation and correlation/interface repairs closed. No blocking/major defect in the stated algorithm. One minor token-reference issue was repaired afterward by the primary. |

The last source/code edits are not mislabelled as the independently reviewed
bytes. The code delta after review touches only reference witness addressing,
its six regression assertions and documentation; saturation, `values`, query
evaluation and the terminal helper are unchanged. The primary checked the
counterexample, lexical restoration and sibling binders directly. Additional
review was not opened for that minor reference-only delta.

The final repository check was:

```sh
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B tools/research_mixed_debt_observer.py'
```

It returned exit 0 with **147 assertions**, **440 literal observer evaluations**
and **11 exact finite-DAG values**. There is no numeric iteration limit in
`saturate`. The process timeout and memory bound constrain this test execution,
not the mathematical algorithm or accepted source language.

Final implementation SHA-256:
`c6f3d36462469494dcdaa5fd6e22029bcea0f5d48a258e5eb55bc41a65dfaf6c`.
Final source-note SHA-256:
`6e39179625abb47cf6fc7cb3eb6338ea53b83033c8d046f128c697463a483aca`.
The final integration also checked Python syntax, all 15 newly introduced
relative links, staged/worktree equality for the eight intended paths, absence
of conflict markers and whitespace errors. No unrelated path was staged.

Before the minor reference delta, the fresh code reviewer ran one separately
bounded process: the then-current 141 assertions/440 evaluations, 216 terminal
contract combinations, and 400 reproducibly generated shared-hole continuations
checked against token interpretation at every node, including root projection.
The actual lexical grammar evaluator was checked as well. That pass used no
Oracle/compiler execution. Its all-node reference shared only the inspected
syntax child enumeration, not count arithmetic or the finite saturation.

The source repair's separate arithmetic transcription passed eight circuit
iterations and 24 distinct concrete Value-slot keys, with next callback context
`R_33` and no actual copying child. The mathematical producer and auxiliary
algebra checks are recorded in their own notes; their counts are not merged
into the final executable's regression total. Every finite check remains
consistency/counterexample evidence rather than a general proof.

| Requested regression or invariant | Evidence in this checkpoint | Limit |
| --- | --- | --- |
| Correct callback scheme and independent symbolic `'b` | Target retained; local finite family subtraction preserves unrelated heads | No successor source execution or symbolic-tail scheme regression. |
| Forbidden concrete contribution | Exact fixed-family local violation/count/entry controls | Not an end-to-end compiler diagnostic or full positive-shape checker. |
| Late lower | Original grammar retained; later larger-PUSH query recomputed correctly | No live source filter-registration transition or future insertion test. |
| Self and nonself cycle | Recursive grammar, unproductive self recursion, primitive three-nonterminal circuit and cyclic doubling | Grammar semantics; only the specified source circuit has a source correspondence audit. |
| Function polarity and correlation | Corrected swap/swap/return observers; shared versus independent choices; per-node raw observations | Complete Function membership and nested cyclic PUSH feedback remain open. |
| Parent/copy SCC intrusion | No new claim | Actual contextual merging and repropagation remain unimplemented. |
| Polymorphic fresh use | No new claim | Binding-occurrence correlation is not source freshening or fresh attachment authority. |
| Failure and rollback | Violation bit and immutable old/new grammar snapshots | Snapshot persistence is not a solver transaction or journal restoration proof. |

No Cargo build, compiler test, Oracle run, benchmark or cutover was performed.

## 4. Integration boundaries and the next single bottleneck

No production source-owned attachment was enabled and no second production
solver was introduced. The requested result remains unexecuted:

```text
(int -> ['b, io] 'c) -> ['b] 'c
```

The minimum future production transition is now concrete for the proved region:
retain source-owned primitive derivations and their actual bracketing; compute
query-specific finite coverage from the retained grammar; register and consume
filters at their real owner; reconstruct coverage from the same grammar when a
future opposite bound supplies a different finite continuation. Row equality
must not identify attachment IDs. A grammar snapshot can be rebuilt after a
finite graph edit, but that observation is not a journal or intrusion proof.

The remaining single mathematical bottleneck is a cyclic derivation region in
which **PUSH-bearing input can return to the same contextual component**.
The current proof cannot assign a finite continuation PUSH mass to that region.
Either derive its exact observation algorithm, or derive from actual source
construction that a relevant component separates into a debt grammar and finite
consumers. No such separation is assumed for the whole solver. The fixed owner
audit and the new source certificate constrain that next source investigation;
they do not prohibit natural source inputs.

The incoming paired-annotation bridge gives a concrete next source route:
same-ID PUSH evidence can travel from `t` through a symbolic row tail `e` to
`h`. Separate allocation alone therefore cannot prove permanent owner
separation. The upstream note leaves actual ordered admission open, including
the first potential suppression at `e/E` before a candidate reaches `h/E`.
This theorem does not assume those graph-level candidates are admitted, and
does not classify the whole bridge as a debt-only recursive region. That
ordered route is the minimum source test for the returning-PUSH bottleneck.

Typing equality and annotation authority remain different relations. An
extrusion copy or SCC representative must not acquire permission from an
unrelated attachment merely by row equality. The one-ID theorem does not yet
supply the production owner/scope/ID transport for that condition. Likewise an
allowance is only a check parameter: `local_terminal` never turns it into a
contribution or subtraction permission. Its explicit subtraction set is an
input from a real consumer, not inferred from the allowed family.

Exact residual-weight gamma allocation, complete support projection,
parameterized effect families, multiple attachment correlations, production
extrusion/intrusion, freshening and rollback remain explicit integration work.
The immutable model snapshot test is not a runtime rollback test. Existing
conditional hygiene/owner/lifetime/transport results keep their exact premises.
No canonical proof DAG status, language authority, or `yulang3` routing changes.
