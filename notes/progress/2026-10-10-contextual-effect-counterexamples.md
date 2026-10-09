# Contextual effect subtraction: adversarial algebra and source boundary

Date: 2026-10-10
Baseline: `b69bb905983881506cdbb294805f2bdeacf77be9`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: independently reviewed algebraic results within the declared scope; no source/production gate closure
Method: pinned-source inspection, exact algebra witnesses, one small checker
Scope: arbitrary contextual operations versus source-generated constraints

## Result and claim boundary

The finite attachment alphabet does not give a finite exact context quotient in
the **unbounded natural-count algebra** if every future Oracle weight operation
and active-stack check is allowed. Arbitrary contextual self-edge deletion and
support-representative replay fail that same unrestricted contract. These are
precise counterexamples to universal algebra claims, **not** counterexamples to
the frozen Oracle on a demonstrated source program.

An additional obstruction is that normalized `compose_for_replay` is not
associative on arbitrary directed contexts. A generic weighted graph algorithm
cannot treat that operation as semiring multiplication without another law or
a richer representation that preserves grouping. This also is an algebra
witness, not a claim of source-reachable inference failure.

Conversely, row identity and attachment identity really can separate in the
source constructors: shared named tails and cached closed rows can select the
same row while separate row-stack construction allocates fresh subtraction IDs.
That construction evidence is stronger than an arbitrary supplied graph, but
does not establish any complete end-to-end source result.

Governing policy is
[annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4,6. The callback result and its independence requirement remain selected
meaning. The
[termination audit](2026-10-10-explicit-effect-termination-source-map.md),
[attachment model](2026-10-10-explicit-effect-attachment-finite-model.md), and
[filter insertion contract](2026-10-10-formal-filter-transition-contract.md)
are inputs, with their conditional/source-reachability limits retained.

## 1. Exact source operations used

All Oracle paths below are relative to `crates/infer/src/` at the pinned commit.
No Oracle code or tests were executed.

| Source locator | Actual operation |
| --- | --- |
| `constraints/directed_weight.rs:137–176,399–405` | For one ID, compose `(p,n)` and `(q,m)` as `(p,n-q+m)` when `q<=n`, otherwise `(p+q-n,m)`. |
| `constraints/directed_weight.rs:16–42` | Directed mix appends right pops to the left word, retains an active residual on the left, and moves a pure residual to the right. It leaves single-sided input unchanged. |
| `constraints/directed_weight.rs:407–418` | Families associated with one ID must agree; equal families do not equate distinct IDs. |
| `constraints/mod.rs:3566–3571` | Ordinary variance swap maps right pops to left pops and leading left pops to right pops. It discards left pushes and the left filter. |
| `constraints/mod.rs:3577–3588,3598–3637` | Prefix/suffix normalization and replay use ordered compositions; replay normalizes by mix. |
| `constraints/machine/propagate.rs:11–38` | `Pos::Stack` and `Pos::NonSubtract` both prepend their weight to the left context. `NonSubtract` is an operation-bearing wrapper. |
| `constraints/machine/propagate.rs:39–63` | A negative Stack checks its filter on the positive shape before derived enqueue, erases that wrapper filter, and appends upper-side pop information. |
| `constraints/machine/bounds.rs:3174–3210,3213–3255,3285–3360` | Check/register insertion filters before storing erased weights; check current/future lowers and active stacks; a positive Function has no filter traversal into ports. |
| `constraints/row_effect.rs:834–848,875–932` | Active concrete E is rejected by a filter allowing only distinct concrete F. |

Use one attachment `i` with immutable family `{E}` and let
`W=(p,n,r;F)` abbreviate its left leading pops, left pushes, right pops, and
left filter. Let `e=(0,0,0;All)`, `P=(0,1,0;All)`,
`D=(1,0,0;All)`, and `R=(0,0,1;All)`. Write `a ⋆ b` for source-exact
replay followed by mix. Repetition such as `P^k` means the primitive count
context `(0,k,0;All)`, not an assertion about any source program.

The algebraic proofs use natural counts. Actual Oracle fields are `u32`:
leading-pop composition and right-pop accumulation use saturating additions,
while push accumulation includes ordinary arithmetic. The no-finite-congruence
theorem therefore does **not** literally assert an infinite state set inside
the finite-width Rust machine. Nor does finite-width storage explain a practical
stopping bound or authorize count saturation as a semantics theorem. All checker
counts are at most 33, far below that boundary.

## 2. Minimal support-replay counterexample

The alias-cycle admission key records the sign of each nonzero count:
`constraints/machine/bounds.rs:7204–7250` retains ID, family, a Boolean
leading-pop flag, a Boolean push flag, and supported right IDs. Its matching
owners at `:4274–4317` apply only to variable endpoints; a left filter excludes
the key until insertion consumes it. Exact retained bounds keep their counts.

Two contexts suffice:

```text
key(P) = key(P^2)
P   ⋆ R = e
P^2 ⋆ R = P
```

Thus equal support keys do not preserve exact future replay. Checking active
families against `{F}` passes the first result and rejects the second. Counts
one and two, one ID, and one cancelling pop are minimal positive-count values
for this distinction. This falsifies replacing a contextual set by an arbitrary
single support representative while claiming equality of all replay results.

It does **not** prove an Oracle bug. The frozen machine chooses admission
subsumption rather than promising that every suppressed weight is contextually
equal to its survivor. A proof of that algorithm must show that suppression
preserves the selected observations on source-generated traces, perhaps because
all relevant consequences already have another derivation. It cannot establish
that claim by asserting `key(a)=key(b)` implies `a⋆c=b⋆c`.

The stack-check observation is source-inspected and genuine. Its placement here
is an **arbitrary operation-context test**, not a claim that an actual upper
bound would wait until after cancellation to install its filter. Oracle checks
insertion filters before replay; moving that check after replay is a separate
invalid shortcut. Complete effect-output projection is not modeled.

## 3. No finite exact quotient for all future operation contexts

Consider `D^k=(k,0,0;All)` for every positive natural number `k`.
For any `n<m`, choose the future operation suffix

```text
T_n(w) = active_filter_check(replay(swap(w), P^(n+1)), {F}).
```

Here a suffix is a fixed sequence of operations applied to the current context:
ordinary variance reversal, replay with a fixed later context, then the existing
active-stack check. It is not merely a right suffix of a left-word monoid.

Swap yields `swap(D^k)=R^k`. Replay with `P^(n+1)` has an active residual
exactly when `k<n+1`. Therefore:

```text
swap(D^n) ⋆ P^(n+1) = P                    -- one active E push
swap(D^m) ⋆ P^(n+1) = e                    -- when m=n+1
swap(D^m) ⋆ P^(n+1) = R^(m-n-1)            -- when m>n+1
```

The first check rejects E against `{F}`; the others have no active stack and
pass. This distinguishes every pair of distinct `D^k`. Any equivalence relation
that preserves all these future observations has infinitely many classes. By
the pigeonhole principle, no finite quotient is exact for this unrestricted
domain. In particular, replacing every positive pop count by one loses an
operation-observable distinction, even when initial pop-only support agrees.

A simpler two-sided word-context argument prefixes `P^n` before `D^n` versus
`D^m`: exact cancellation gives identity versus residual pops. The operational
suffix proof above additionally turns the difference into a concrete check,
rather than relying solely on exact-weight equality as the observer.

**Necessary restriction for a positive finite context quotient:** bound or structurally
restrict which same-ID matching pushes may occur in future operations, or prove
observational dominance of discarded contexts on the actual source envelope.
Fresh-ID construction alone does not prove such a bound: replay may traverse
one original operation more than once. No source proof of the necessary
restriction was found in this assignment. The theorem does not force a user
numeric limit; it identifies the false unrestricted premise.

## 4. Nonassociativity blocks unqualified flat-path multiplication

For the three already normalized primitive contexts `a=D`, `b=R`, `c=P`:

```text
a ⋆ b = R^2
(a ⋆ b) ⋆ c = R
b ⋆ c = e
a ⋆ (b ⋆ c) = D
```

So `⋆` is not associative. This is a direct specialization of the pinned mix
code, including its single-sided guard. It is not caused by filters,
multiple IDs, wildcard rules, numeric saturation or row equality.

The different results are operation-observable:

```text
R ⋆ P = e
D ⋆ P = (1,1,0;All)
```

Only the latter retains an active E push. A filter excluding E distinguishes
them. Thus one cannot excuse the grouping change merely by forgetting which
side owns a pure pop.

This does not establish that an ordinary source constraint graph generates all
three contexts in these groupings. It does establish that an all-context
weighted-automaton proposal using normalized replay as semiring multiplication
needs a new premise. Possibilities include a source-restricted associativity
law, a transformation representation with proven composition semantics, or an
operation-expression graph that retains the exact replay/variance tree. Merely
writing a regular expression for flat edge labels does not discharge it.

## 5. Contextual self-edge omission needs discharged obligations

The smallest retained-filter witness for the uniform insertion contract is:

```text
1. x <: x under (POP_i, filter={E}, right=empty)
2. later concrete F <: x under identity
```

Under the supplied insertion transition, step 1 registers `{E}` on x, even
though its endpoints agree. Step 2 must reject F. Deleting step 1 before that
registration loses the violation. One contextual self-use and one later lower
are sufficient; no counted cycle or second attachment is needed.

Frozen Oracle `constraints/machine/entry.rs:1097–1107` explicitly returns
trivial for same-TypeVar endpoints **before** bound insertion, regardless of
context. Thus this graph is a counterexample to an unrestricted uniform
transition contract plus unconditional self-drop, not a counterexample to the
machine's explicitly guarded operational contract.

Source reachability is the decisive missing premise. In particular, negative
Stack normalization (`propagate.rs:39–63`) may already perform the relevant
shape/filter registration before a derived same-row task is dropped. Conversely,
`NonSubtract` prepends its weight rather than proving a universal prior-filter
discharge. Neither observation proves that all source-generated contextual
self-tasks have their future/output obligations discharged. This assignment
does not claim either global safety or a source-reachable failure.

The pinned API test `constraints/tests/case_01.rs:950–986`,
`var_var_replay_keeps_pop_only_alias_cycle_finite`, constructs two variables with
one pop edge and one identity reverse edge. Its counterpart at `:990–1026`
uses a push edge. These are API-constructed constraints; they are not language
source examples. Inspection confirms owning guards, not source reachability or
execution. The successor cannot inherit that guard solely because its SCC
operation makes two row representatives equal.

## 6. Row equality cannot identify attachment authority

One-row, two-route conditional witness:

```text
the same E contribution at row r
  route through its authentic negative attachment i -> consumed
  independent ordinary route -> E survives at output
```

Changing row r into a global E-removal authority deletes the surviving route.
The [attachment model](2026-10-10-explicit-effect-attachment-finite-model.md)
already supplies this graph; no duplicate exhaustive model is needed here.
Exact weight algebra adds the smaller coordinate distinction:
`P_i[E]` cancels `D_i` and does not cancel `D_j` for `i!=j`, even if both
families and row coordinates agree.

There is actual constructor evidence that row-sharing is compatible with fresh
authority identities. In Oracle `lowering/signature_effect.rs:319–333`, a
Function boundary uses the same `signature_var(tail)` for a shared symbolic tail;
for closed explicit rows it can reuse `state.closed_effect_rows[key]`.
Yet `effect_row_stack` at `:382–421` calls `fresh_subtract_id()` for each
nonempty concrete construction, including an already cached row. The
`register_stack_facts` loop at `:434–440` stores facts indexed by that row and
each actual stack ID. This is a concrete source-constructor reason to retain
both identity dimensions. Row caching is not an attachment-ID cache.

This establishes **formation compatibility**, not a complete source trace with
two live opposite-polarity routes. No parser run, raw-source callback execution,
generalization/freshening proof or output-support computation was performed.
The source API operations do not license inventing syntax or an artificial
source rule to generate the other algebra counterexamples.

## 7. Corrected finite representation: precise remaining consumer cut

The natural escape from enumerating exact contexts is to retain finite original
constraints plus symbolic cyclic derivations, preserving attachment coordinates
and exact operation trees. For a fixed finite endpoint/shape/ID universe and a
fixed finite set of inference-rule schemas, a shared equation system can use
nonterminals for endpoint relations, primitive weighted leaves, binary replay,
variance swap, and wrapper operations. A cyclic rule denotes arbitrarily many
finite derivations instead of adding one fact per evaluated count. This is a
representation observation; no alternate source semantics is selected.

Three conditions are necessary before that observation becomes a terminating
solver preserving meaning:

1. **Finite production generation.** Rule construction must depend on finite
   source/shape coordinates rather than first enumerating count-valued contexts.
   Freshening, extrusion and intrusion must preserve or deliberately rebuild
   the finite schema and all original authority references.
2. **Exact effective consumers.** Insertion checks, future filters, variance,
   residual/output projection and diagnostics must decide their predicates over
   denoted derivations without enumerating an infinite family of weights.
   A finite cyclic syntax alone does not prove termination of these queries.
3. **Correct observation and admission semantics.** The target denotation must
   specify which derivations are retained/observed. An unrestricted closure is
   different from Oracle's self/alias admission system. Existential violation,
   union support, provenance and suppressed-path discharge require separate
   correspondence. Nonassociative replay grouping must remain explicit unless
   a restricted law has been proved.

This assignment supplies obstructions and consumer obligations, not the complete
symbolic construction or a decision procedure for arbitrary weighted grammars.
It does not claim regularity of all normalized-context languages, effective
whole effect projection, all-view completeness, source soundness or principality.

## Verification, omissions and commit packet

Exact command, one lightweight process:

```sh
timeout 10s python3 -B tools/research_contextual_effect_counterexamples.py
```

Result:

```text
PASS 729 literal/count comparisons; 528 POP-pair distinguishers; support replay, nonassociativity, self-filter, distinct-authority witnesses
```

The checker compares independently implemented literal reduction and count
replay for the 27 one-ID contexts with each count in `0..2`, then tests the
minimal vectors and all POP pairs `1<=n<m<=33`. This finite check illustrates
the universal suffix proof; it is not its proof by exhaustion. The self-filter
and row-authority vectors are supplied local transitions, not a compiler
simulation. No Cargo/build/compiler test, benchmark, Git mutation or subagent
was used. No broader search was run or silently truncated.

Exclusive frozen paths:
`notes/progress/2026-10-10-contextual-effect-counterexamples.md` and
`tools/research_contextual_effect_counterexamples.py`.
Direct dependencies are the three progress notes and hygiene policy named
above at baseline `b69bb905983881506cdbb294805f2bdeacf77be9`; pinned Oracle
reads use its immutable commit. No intentional dependency changes.
Proposed commit message:
`research: distinguish exact contextual effect counts and symbolic grouping`.
Shared-record changes are deferred to the primary: preserve the open
source-reachability and exact-consumer gate, record that support admission is
not a universal congruence, and do not close termination merely from finite
IDs, symbolic syntax or the Oracle API cycle tests.

## Independent review

The independent `algebra_review` compiler-referee pass checked the arithmetic,
unbounded natural-count quantifiers, observable nonassociativity, the difference
between uniform self-filter insertion and Oracle admission, and the actual
shared-row/fresh-ID constructors against the pinned source. It reported no
blocking, major or minor finding in that scope and reran the bounded checker
successfully. This certifies the stated mathematical obstructions, not a
source-reachable Oracle failure or successor termination. The primary clarified
that the finite-result restriction above concerns a **context quotient**; a
finite symbolic representation or a terminating algorithm need not be one.
