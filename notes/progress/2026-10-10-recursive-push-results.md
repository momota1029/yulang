# Recursive PUSH: direct source example, exact decision and remaining mixed gate

Date: 2026-10-10
Status: scoped mathematical, source and executable reviews complete; general mixed recursion and production gates open
Branch: `research/simple-sub-intrusion`
Initial remote baseline: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`
Pinned Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: the user's request to solve returning recursive PUSH directly or
derive a debt-only source separation; no language policy change

## 1. What this checkpoint resolves

The earlier mixed-debt theorem required all recursive grammar values to have
zero active PUSH count. The new main theorem removes that premise for the
entire left-word recursive grammar class. Leading POP and active PUSH counts
can both be positive and both grow without bound. Independent recursive
binary replay is permitted, not just a regular path or a fixed unfolding.
Every fixed finite mixed observer has a terminating, exact decision algorithm.

There is also an actual source construction with a concrete lower and
recurrent PUSH. Consecutive paired `as` annotations on the same provider create
distinct-endpoint PUSH/identity aliases. An Act operation supplies a concrete
Row, which is not subject to the Oracle's Var-only cycle suppression. A nested
version has POP and PUSH loops and realizes every left pair `(p,n)` at its
shared Effect endpoint. Its complete pre-generalization recursive component
belongs to the newly decided class. Source closure here is derived from the
particular complete constructor graph, not assumed from attachment allocation.

This directly resolves recursive PUSH for a real source component. It does
not give an algorithm for every recursively mixed four-port component, or
enable explicit attachments in the successor. That larger gate stays open.

The separate algebra theorem additionally decides three recursive families:
mixed PUSH/right-POP cancellation orbits, two-coordinate affine growth, and
shared-child active-PUSH doubling. These are mathematical families with full
proofs, not restrictions on what source programs may mean.

## 2. Definitions and independent reference denotation

The model uses one authentic attachment ID `i`, natural counts and a fixed
active family `S`. A raw weight `W=(p,n,r)` denotes a left word
`POP_i^p PUSH_i^n` and a right word `POP_i^r`. Counts are not saturated at an
implementation integer width. Different annotation IDs are not identified by
any equation on type variables.

Left composition is

```
(p,n) * (q,m) = (p + max(q-n,0), m + max(n-q,0)).
```

Replay first composes left words and adds right debts; it then performs the
actual directed mix. If either side is empty it preserves the other side.
Otherwise it appends right POPs to the left word, retaining a surviving PUSH
on the left or moving the pure residual debt to the right. In the participating
case the result is `(p,n-r,0)` when `n>r`, and `(0,0,p+r-n)` otherwise.

The finite observer also permits the actual operators

```
swap(p,n,r) = (r,0,p)
both(p,n,r) = (r,0,r)
prefix(a,b,W) = (a+max(p-b,0), n+max(b-p,0), r)
suffix(c,W) = (p,n,r+c).
```

Raw prefixes/suffixes are not implicitly mixed. Syntax and check locations
are retained: general replay is nonassociative. For example, with `P=(0,1,0)`,
`L=(1,0,0)` and `R=(0,0,1)`, `replay(replay(P,R),L)=L`, but
`replay(P,replay(R,L))=R`.

A finite left-word grammar has finitely many nonterminals and productions
built from left-only constants, fixed left prefixes and replay. Its reference
denotation is the set of exact values of all finite derivation trees. Separate
child occurrences independently choose derivations. The class has no recursive
same-child binding. A finite observer can bind and reuse an entire chosen
grammar value; different hole names choose independently.

The reference definition is given before the decision algorithm. It does not
discard failing derivations, cap counts, or equate support with an exact word.
Queries may compare exact counts at any finite observer nodes, test identity,
pending side, left-entry presence, and fixed-family local legality/residual
predicates at their actual positions. The full proofs and finite decoration
conditions are in [the construction](2026-10-10-recursive-push-observer-construction.md)
and [the algebra theorem](2026-10-10-recursive-push-algebra-attack.md).

## 3. Main theorem: recursive full pairs admit exact mixed observation

**Theorem.** For every finite grammar just defined and every fixed finite
mixed observer with finitely many shared/independent selections, existence of
any specified Presburger-definable count observation is decidable. Fixed finite
family/filter decorations may be carried exactly. Universal absence of a
specified violation is decidable as the complement of that existential query.
No bound on recursive PUSH mass, leading debt or derivation depth is required.

The proof has four concrete parts.

### 3.1 Literal-word grammar

Let `U` be PUSH and `D` be POP. The rule `UD -> epsilon` terminates and has no
overlapping redexes; disjoint deletions commute. Its unique normal forms are
`D^p U^n`. Concatenation followed by this normalization gives exactly the
left composition above. Thus the left-only algebra is associative, despite
mixed replay being nonassociative.

Replace left-only constants by their normal-form words, prefix by literal
prefixing and recursive replay by concatenation. This is an effective finite
context-free grammar. Induction on finite derivation trees proves exact
equality between its normalized words and the original recursive values.
The translation preserves the pair, not merely its difference. In particular
`T -> I | prefix(D,replay(T,U))` has exactly `(k,k,0)` for `k>=0`.

### 3.2 Exact global-minimum certificate

For a word `w` let `h(j)` be the balance of U minus D in its first `j` symbols.
Its normal form satisfies

```
p = -min_j h(j),       n = h(|w|)+p.
```

During a left-to-right reading, unmatched POPs increase precisely when a new
prefix deficit is reached; the final balance is `n-p`. This proves both
equations.

Use three natural counters `(d,a,b)` and one grammar-generation stack. Guess
`p` by incrementing `d` and `a` together. Generate a grammar word, processing
U/D as +1/-1 on `a` before a nondeterministically chosen split, and on initially
zero `b` after it. All updates have ordinary nonnegativity enabling. Freeze
`a` after the split and require it to equal zero at the final point target.

In any reaching run, nonnegativity before the split gives `h(t)>=-p`, frozen
zero gives `h(j)=-p`, and nonnegativity afterwards gives `h(t)>=h(j)`. Hence
the split is a global minimum and `(d,b)` is exactly `(p,n)`. Conversely,
choose any actual global minimum of any grammar word; it supplies such a run.
Omitting final frozen zero would be unsound: word U with guessed debt 1 and
split before U would falsely report `(1,1)`.

For finitely many independently selected inputs, run these generators in
sequence using one stack and separate counter triples. A shared input is
generated once and its variables are reused in every observer occurrence.
This preserves cross-observation correlation.

### 3.3 Exact target of the finite observer

Every primitive operation has a graph given by finitely many linear cases;
for example `z=max(x-y,0)` is `(x>=y and z+y=x) or (x<y and z=0)`.
Conjoin the graph of every actual observer node with the observation. After
existentially eliminating its internal variables, accepted input pairs form
an effective Presburger set `Q`, hence an effective finite union of linear
sets `v0 + sum_j k_j*v_j` with nonnegative vector periods.

The grammar's residual set itself need not be semilinear. Only this fixed
observer target is converted to that representation.

For each linear component, subtract its base from the retained `(d,b)` vector,
then nondeterministically subtract its periods, and require all counters to be
zero at the target with empty stack. Frozen `a` counters are untouched. If the
entry vector has the displayed decomposition, every intermediate remainder
is a sum of unconsumed nonnegative periods, so no subtraction underflows.
Conversely, final zero proves exactly that decomposition.

### 3.4 Termination and equivalence

The construction is one finite pushdown vector addition system with states
(PVASS), at finite counter dimension. It uses no interior zero-test guard.
The published theorem by Guttenberg, Keskin and Meyer, **PVASS Reachability Is
Decidable**, LICS 2026, Article 53,
[DOI 10.4230/LIPIcs.LICS.2026.53](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.53),
supplies a terminating point-reachability decision algorithm.

A reaching run supplies a grammar derivation, an exact pair for each selection
and a true observer target, proving soundness. Conversely, a satisfying
reference derivation supplies global-minimum splits, the exact finite observer
trace and a semilinear target decomposition, proving completeness. Every
translation is effective and finite; composition with that published decision
algorithm proves termination, rather than merely asserting that a grammar has
finitely many symbols.

The cited general algorithm has Hyper-Ackermann complexity. This is a decision
theorem, not a practical production implementation. The source components below
have much simpler exact sets and use the elementary finite-state algorithm in
section 5 instead. The publication is an external proved dependency, not a new
unproved source hypothesis.

For a violation at some arbitrarily repeated recursive production node, each
fixed local template can be queried separately after finite productivity and
usefulness analysis. Every child tuple can be inserted into a useful production
occurrence because children are independent and the required siblings are
productive. This proves bad-node existence, and universal absence of bad nodes.
It does not impose guard-enabled derivations or jointly constrain a root with
an arbitrary descendant.

## 4. Source construction supplies the theorem's premise

The complete source derivation and owner locations are in
[the source note](2026-10-10-recursive-push-source-invariant.md). Its minimal
first source is

```yulang
act io:
  pub ping: () -> ()

my witness = ((\x -> io::ping ()) as (int -> [io; 't] ())) as (int -> [; 'e] ())
```

Both `as` annotations constrain the same actual Value `V`. The first allocates
an annotation-owned fresh Effect `r` and attachment `i`, and connects `r` to
written tail `t` by identity. The second uses the direct symbolic tail `e`
and allocates no attachment. Paired Function comparisons produce
`r --PUSH_i--> e` and `e --identity--> r`. These are distinct-endpoint edges;
the proof does not retain an Oracle-omitted Var self-edge.

The operation producer independently supplies `C=Pos::Row([io])`. Actual
provider/negative annotation comparison sends it to `r/e`. For every natural
`k`, replay along the two primitives takes a retained `C <: r @ PUSH_i^k`
to `C <: e @ PUSH_i^(k+1)` and back to `r` at that count. Var-only alias
subsumption, Var-only self omission and Var-only frontier evidence skipping
cannot remove these Row-to-Var consequences. A Row is not a terminal whose
weight is erased. All involved filters admit `io`; there is no residual
negative-head consumer on this component. Induction supplies unbounded PUSH.

The nested source in the source note shares `e` between the outer and inner
return Effect of the second annotation. The first annotation has its own
inner symbolic tail `h`. Its return-Value `NonSubtract` supplies the actual
additional `h --POP_i--> e` edge; the reverse edge is identity. At `e`, first
take the POP loop `p` times and then the PUSH loop `n` times. Starting from its
concrete identity seed, this gives every `(p,n,0)` in `N^2`. Every exact value
is also a natural left pair, so the set at this slot is exactly `N^2`.

This refutes both a universal debt-only invariant and a forced signed-counter
model. In particular `(1,1,0)` is source-produced and distinguishable from
identity by active count, pending debt and left-entry presence.

For these two programs the source note enumerates every incoming Function
port before generalization. Weighted argument-Value children terminate at
nullary `int`; annotation argument-Effect children are Bot; actual-provider
pure passthrough occurs at identity; the concrete nullary effect has no
Value payload; recursive Effect owners have Var uppers. No right debt or
changing family returns to the component. Hence the **whole** recursively
reachable component is left-only, rather than merely a selected subgraph.

Neither source was compiled in this environment. This is an owning-code
construction/admission proof; an ordered compiler trace would be additional
verification. It is not a successful public type, evaluation result or theorem
about post-generalization uses. Ordinary finite Act operation scheme uses are
included in the constructor audit; callback use-time freshening is absent.

### Refuted claims, with their exact scope

| Claim | Counterexample and failed step |
| --- | --- |
| All actual annotation-generated recursive components are debt-only | The first `as` source has a real Row seed and distinct-owner PUSH/identity cycle. New concrete PUSH counts bypass every relevant Var-only omission. |
| The full left pair may be replaced by signed depth `n-p` | The nested source produces `(1,1,0)`, which has the same signed depth as identity but different active, pending and entry observations. |
| Every recursive PUSH supplying set is semilinear | The explicitly shared grammar `T -> A_h(x0) | let t=T in replay(t,t)` has exact values `A_h(x0*2^k)`. Its active-count gaps grow without bound; an infinite one-dimensional semilinear set has bounded eventual gaps. This is a grammar counterexample, not a claimed source realization of shared doubling. |
| Ordinary one-counter input/output reachability retains the exact full pair | Identity alone and identity together with `(1,1,0)` both induce `{(a,a) | a>=0}`, while their exact count observations differ. The global-minimum certificate repairs that information loss. |

The separate zero-test-guarded counter-machine reduction in the algebra note
does not refute decidability of the actual unguarded problem. A source/global
failure is not permission to prune a recursive derivation with a new guard.

## 5. Elementary finite-state algorithm for the solved source sets

For the push ray use `W=(0,k,0)` with `k` natural. For the nested component use
two independent naturals `W=(p,n,0)`. The additional proved cancellation and
growth families have finite unions of affine descriptions. For shared doubling
use `W=(h,h+x0*t,0)` together with `Pow2(t)`; binary encodings with exactly one
set bit describe that nonsemilinear set.

Symbolically evaluating a fixed observer yields a finite union of guarded
affine traces in the input parameters. Each `max` and actual mix creates only
finitely many linear branches. One variable selection belongs to each shared
hole; independent holes have separate parameters. Conjoin the requested
finite Boolean count observation, distributing into finite disjunctive form.
It suffices to decide a conjunction of integer affine equations, affine
inequalities and power-of-two predicates on natural parameters.

Here is an explicit finite-state decision for one conjunction. For an affine
expression `s(x)=c+sum_i a_i*x_i`, start an integer carry at `c`. Read a common
binary column of all parameters, least significant bits first. Update

```
q' = floor((q + sum_i a_i*bit_i)/2).
```

For the equation `s=0`, reject any column with an odd numerator and accept at
the end exactly when `q=0`. For `s>=0`, retain both parities and accept when
`q>=0`. Indeed after `l` columns the latter carry is
`floor((c+sum_i a_i*(x_i mod 2^l))/2^l)`. If these columns encode the complete
numbers, the sign test is exactly the sign of `s`. The equation's retained
parity conditions additionally require every removed low bit to be zero.
The same recurrence works for negative coefficients/constants with floor,
not truncation toward zero.

Let `M=max(abs(c),sum_i abs(a_i))`. If `q` lies in `[-M,M]`, the next numerator
lies in `[-2M,2M]`, so its floored half also lies in `[-M,M]`. Thus each affine
atom has finitely many carry states. Each `Pow2` track needs only the number
of observed one-bits, saturated into states zero, one and more-than-one. Take
the finite product and search its reachable states under the finite digit
alphabet. Accepting any finite word is equivalent to a satisfying natural
parameter tuple. Empty/all-zero padded words encode zero; arbitrary common
zero padding permits every finite tuple.

The product has at most `3^h * product_j(2M_j+1)` non-rejecting states for `h`
power tracks and the affine atoms, before harmless finite control factors.
This is an input-derived state bound, **not a cap on source counts**. Accepted
words can encode arbitrarily large values. Exhaustive reachability of this
finite state graph terminates, and the digit invariant proves exact soundness
and completeness. Witness digits reconstruct the actual parameter tuple and
the original observer is then evaluated on that tuple.

The research implementation is
[`tools/research_recursive_push_observer.py`](../../tools/research_recursive_push_observer.py).
It supplies this direct finite observer algorithm, not the general PVASS
algorithm. No successor admission rule delegates to it.

## 6. Review and executable evidence

Mathematical referee `recursive_push_math_referee` found no blocking, major or
correctness-related minor defect in the frozen construction and algebra notes.
The review inspected pinned Oracle operation definitions and the official
PVASS publication for applicability; it did not audit the paper's entire proof.
The reviewer independently checked the global-minimum certificate, semilinear
target subtraction, sharing, local-template embedding, exact orbit boundaries
and binary-automata closure. It ran no Python or compiler process.

Reviewed mathematical snapshots:

```
69dfc39c031f7dc72808163c743135bd4f69153501e04439b9d341f3fa53a07b  recursive-push-observer-construction
b0aae57140d9c4f00cf90b991c4ae52342dcc6b2d94ef148cabd36485d2bb8dd  recursive-push-algebra-attack
```

Source referee `recursive_push_source_referee` found no blocking or major
defect in the two exact pre-generalization source components. The review
checked the owning parser/annotation/reference/lambda/call paths, concrete Row
admission, complete incoming four-port cases, filters, and in-place Oracle
extrusion. It ran no compiler or Python process. Two minor corrections were
accepted and checked by the primary: include eager Act-reference signature
generation and finite operation-demand Functions in the inventory, and
distinguish pending-count saturation from ordinary active-count addition.
The reviewed source snapshot was
`8ba04d71b715079253f25129b121a7e53cf79efc5fc4c2cb014e94b12c5cdd84`;
the corrected source note is
`fb7793967fd9e5aa1610c4b1bca5686247c1744c04bff149c107afb36e343790`.

Executable referee `recursive_push_code_referee` found no blocking, major or
correctness-related minor defect in the documented finite-observer algorithm.
Its review includes section 5's signed carry invariant, exact symbolic mix
guards, orbit phases, all-node traces, sharing and materialized witnesses.
The reviewed and published executable SHA-256 is
`67ed7cb979d38827645f6e939977ea0ae7c62e2843c9fca9a216f10282f3cb12`.
The predicate callable is required to return finite DNF on the supplied trace;
arbitrary or nonterminating Python predicates are outside that API contract.

The producer-frozen mathematical notes and executable retain their original
handoff status text. This integration record supplies their subsequent
independent review disposition at the exact hashes above.

### Narrow executable checks

| Owner/process | Concrete evidence | Result and resource boundary |
| --- | --- | --- |
| Exact-pair construction probe | 8,191 literal words, 98,305 minimum-marker positions, 101 full-pair cycle values; signed collapse and omitted frozen-zero mutations killed | PASS; one process, 30 s / 256 MiB limit, 6,656 KiB maximum RSS |
| Algebra producer pilot and full run | Full run: 115,200 cancellation-orbit comparisons, 230,400 raw-token comparisons, 23,040 growth cases, 240 doubling cases, 100 guarded update calculations, 8,192 binary-automaton checks | PASS; two sequential processes, each 30 s / 256 MiB; full run 11,992 KiB maximum RSS |
| Source arithmetic transcription | 16 concrete PUSH keys, the `(1,1)` path, 25 full pairs | PASS; one process, 30 s / 256 MiB; no source parser/compiler execution |
| Executable producer main | 8,685 assertions, 630 exact decisions, 297 literal observers, 7,680 orbit comparisons | PASS; 0.131 s internally measured wall, 14,336 KiB maximum RSS |
| Executable producer final probe | 4,939 assertions, 1,750 exact decisions, 125 complete correlated finite traces, 975 literal trace nodes, 1,800 signed carry/Pow2 cases | PASS; 2.643 s internally measured wall, 13,148 KiB maximum RSS |
| Independent executable referee | 80,478 assertions: 77,760 literal orbit comparisons; 2,250 forced signed-kernel inputs; 448 unique/complete symbolic trace cases; 20 Pow2/empty cases | PASS; 0.7183 s reported wall, 12,476 KiB maximum RSS |

Both executable producer processes and the one independent referee process
had a 30-second wall limit and 256 MiB address-space limit. A predicate-index
validation check was added between the producer's two runs and exercised in
the second; no executable edit followed that final producer run. The referee
reviewed and probed that final snapshot without using the producer's main or
PASS as evidence. Its initial requested scratch working directory was absent,
so one command failed before a Python process started; the subsequent sole
probe ran successfully from the existing parent directory. No test result was
derived from a timeout or interrupted run.

Reproducible repository entry point:

```sh
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B tools/research_recursive_push_observer.py'
```

The tool checks exact counts around `10^30` and `2^20` membership without
unfolding that many cycles. It also covers shared-versus-independent choices,
raw checks before cancellation, local filter placement, empty supplying sets,
finite unions, invalid descriptors, and zero/boundary cancellation phases.
Finite probes are implementation-consistency evidence; sections 3 and 5 give
the mathematical termination and equivalence arguments. The literal evaluator
shares the supplied operation semantics, but uses tokens instead of the
candidate count formulas. These are not compiler regression counts or a proof
of independent source effect semantics.

This session had no `cargo`, `rustc` or retained Oracle harness. No new source
fixture, target callback scheme, successor test suite or production cutover
was executed. No production file, manifest, lockfile or expected public output
was changed.

### Published coherent checkpoints

| Commit | Content |
| --- | --- |
| `c78346a80462d0a42dfc3f3490bb82b90f76f614` | Full-left recursive CFG/PVASS theorem |
| `7b4f3e68895c911c550252a10754cb3262bb057b` | Exact mixed cancellation, growth and shared doubling families |
| `e941268b860196cf5ff074739db86dc80d994429` | Reviewed actual source PUSH/full-pair construction and closure |
| `79e02343bfdbe33bf2e7ca6ccff9f8f6f8eff1bc` | Independently reviewed finite-state research observer |

All are on `research/simple-sub-intrusion`. Incoming documentation-only
research updates through `566310fa` were inspected and preserved; their
successor self-filter question remains separate from this distinct-owner,
concrete-seeded source recurrence. One source ref-update attempt encountered
a connector error while the remote advanced; the primary fetched, inspected
the new range, rebuilt the source checkpoint on that head and updated with an
expected-head lease. No force update or unrelated history rewrite was used.

## 7. Preserved exclusions and the next actual bottleneck

The unsolved general case has recursively returning **mixed** contexts:
right debt, swap/both and possibly repeated selection of one recursive child
can occur inside the same PUSH-bearing dependency component. Mixed replay
cannot be flattened to concatenation, and same-child copying cannot be replaced
by independent grammar occurrences. A finite grammar alone is no decision
procedure for this class. The simple solved orbit/doubling families do not
prove closure under arbitrary combinations of their operations.

The next single research task is to obtain an exact observation algorithm for
that returning mixed Effect component. The source note retains an exploratory
body-effect-tail route returning right debt into a PUSH owner; it is not an
admitted source counterexample or a premise of the proved source results.

The current results do not establish source gamma/residual endpoint finiteness,
all-ID/family correlations, arbitrary nested future Functions, SCC intrusion,
use-time freshening or failure rollback for weighted successor state. Existing
conditional hygiene, authority, transport and lifetime proofs keep their exact
premises. Type-variable equality supplies no new annotation permission.
Concrete allowance remains separate from contribution and subtraction grant.

No production source-owned attachment or its weighted filter consumer is
enabled by this checkpoint; the user-supplied callback public scheme remains
unexecuted. No production soundness/principality, general termination, complete
Call, public export or cutover gate is promoted. The canonical obligation DAG
is unchanged. The new result is a proved direct solution of recursive PUSH
within a broad mathematical class and an actual source-generated instance,
with an executable finite observation procedure for its concrete source sets.
