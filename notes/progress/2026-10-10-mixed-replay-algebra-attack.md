# Mixed replay algebra: bounded-PUSH observers of cyclic debt grammars

Date: 2026-10-10
Status: algebraic arguments independently reviewed at their stated scope; bounded checker evidence, no source or production certification
Baseline: `e2f29d0a30f81616b4963cb1b2a42d9a798af2b3`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Scope: one ID, natural counts, common fixed active family, All filters during replay
Lease: this note and `tools/research_mixed_replay_algebra.py` only

## Result and boundary

For a **debt-only** finite regular tree grammar, an exact query algorithm exists
for every fixed finite observer made from the inspected replay, swap, prefix,
suffix and `both_from_right` operations. The observer may contain PUSHes,
multiple independent holes, or multiple uses of the same selected debt value.
Let S be the sum of the PUSH counts in all its constant leaves/prefixes, counting
each syntactic use. Compute the grammar in the finite domain obtained by
clipping each debt coordinate at K=S+1. Evaluate the observer on that domain.
This preserves the active count exactly and every zero/nonzero debt, side-entry
and identity observation. It does not preserve exact nonzero debt counts.

The clipping is an observer-specific proof device. Keep the grammar and repeat
its finite evaluation for a future observer with a larger PUSH budget. Neither
replacing retained source weights permanently nor sharing a quotient across
unbounded future queries follows. Cyclic copying is allowed **inside the
debt-only grammar**; no regularity of its exact unary output language is needed.
The previous powers-of-two obstruction is compatible with this theorem.

This is a conditional algebra theorem, not a source-generated grammar theorem,
compiler result, or independent certification. The precise source premise is
that the recursive grammar supplying observer holes introduces no PUSH. A
mixed recursive grammar whose siblings supply unbounded PUSH mass does not
satisfy that premise. Kind stratification or absence of cyclic copying alone
does not prove it.

## 1. Exact operations and canonical forms

The source premises are the frozen Oracle's
`crates/infer/src/constraints/mod.rs:3566–3612` and
`constraints/directed_weight.rs:12–42,137–176`, also recorded in
[the counterexample note](2026-10-10-contextual-effect-counterexamples.md) §1.
Those exact pinned regions were inspected read-only. Natural arithmetic is the
explicit research model; Oracle's numeric-width boundary is not covered.

For a raw weight W=(p,n,r), p is left leading debt, n is left active depth, and
r is right debt. Left composition is

    (p,n) compose (q,m) = (p+max(q-n,0), m+max(n-q,0)).

Replay composes left words in the displayed order, adds right debts, and mixes.
Mix leaves single-sided states unchanged. With both sides present it appends
right debt to the left word, retains any active residual on the left, and moves
a pure residual to the right. Swap is (r,0,p); both is (r,0,r). Prefix composes
its fixed left word before W's left word; suffix adds fixed right debt without
mixing immediately. Hence raw wrapper/both states must not be assumed mixed.

Every mixed one-ID state is exactly one of identity, pure left debt L_p,
pure right debt R_r, or A(p,n) with n>0 and r=0. This follows directly from mix's
two-sided branch; conversely every displayed form is unchanged by mix. It is
not a closure assertion for raw prefix, suffix and both intermediates.

## 2. Exact finite homomorphism for debt-only productions

On n=0, let cap_K(p,0,r)=(min(p,K),0,min(r,K)). Debt-only replay first adds
left and right coordinates, then either keeps a single side or moves their
sum to the right if both sides were present. Saturation commutes with addition:

    min(a+b,K) = min(min(a,K)+min(b,K),K).

Saturation also preserves zero versus positive, so it preserves the branch
choosing side placement. Swap, both, debt-only prefix/suffix and identity
likewise commute with cap_K, with a cap after each operation. In particular,
raw both correlations (r,0,r) survive exactly at the level of clipped values;
the two coordinates must not be independently sampled after applying both.

Consequently a grammar evaluated over this finite algebra computes exactly
the cap_K image of its finite-tree denotation. Proof: induction on each finite
derivation gives soundness of its clipped value; induction on finite saturation
derivations supplies an actual finite tree giving every added abstract value.
The least fixed point terminates, with at most (K+1)^2 raw debt states per
nonterminal. Recursive copying and arbitrary bracketing do not alter that proof.
No rule reassociation is used.

Ordinary repeated occurrences of a nonterminal choose independent derivations.
An observer that deliberately reuses a single chosen value must enumerate one
clipped value and reuse it consistently. Marginal sets do not establish arbitrary
external correlations between distinct grammar variables.

## 3. Why S+1 suffices for any fixed observer

Here is a token-level proof of the observer claim. Give each observer PUSH token
a distinct leaf/occurrence label. There are S such tokens. Replay and left-word
composition only concatenate and cancel them. Swap drops PUSHes; both copies
only right POPs and drops left PUSHes. None of these operations copies a PUSH.
Thus at most S PUSH tokens can ever cancel any POPs in the entire evaluation.

Compare an exact execution and a clipped execution using the same tree and
chosen hole values. Keep the same labeled surviving PUSH sequence. A debt block
is either represented at exactly the same count, or is large in both executions:
its count exceeds the total number B of PUSH tokens that could still cancel it.
Initially clipped blocks >S are replaced by S+1, so this relation holds. B counts
live and future PUSH tokens, and decreases when a token is canceled or dropped.

At a cancellation, a differing large block cannot be exhausted: it consumes
all confronting PUSHes in both executions. After consuming a of them, both
block counts still exceed B-a. Exact small blocks cancel identically. Addition
of debt blocks preserves this relation, and swap/mix side movement does as well.
Copying a large debt block by both produces two large blocks without increasing
B. A clip inserted after any operation either changes nothing or replaces a
block by K=S+1>B. These facts prove the invariant by structural evaluation,
including binary replay and raw two-sided intermediate states.

Mix's branches inspect side presence and whether a PUSH survived after right
debt was appended. Those tests agree under the invariant. The final active
count is exactly the number of surviving labeled PUSHes, and the presence of
each debt block agrees. Thus (n>0), (p>0), (r>0), left entry (p+n>0), right entry,
and identity are preserved, as is n itself. The local compact left-entry query
from the supplied notes belongs to this predicate class.

A fixed family-filter test depending only on whether the common family remains
active is preserved. A fixed terminal head-residualization that changes that
family without changing ID/count is also preserved before the same local
presence/filter tests. This does not extend to unequal-family replay,
parameterized family compatibility, insertion scheduling, arbitrary new guards,
or the complete compact support/public collector.

For S>=1, K=S is insufficient for the full active-and-presence contract:

    replay(P_S,R_S)       = identity
    replay(P_S,R_(S+1))   = R_1.

Their R inputs agree after clipping at S. Swap makes the outputs identity
versus L_1, distinguished by local compact left presence. For S=0, cap_0 already
identifies identity with L_1. Therefore S+1 is the smallest uniform coordinate
cap for this observation contract at the specified PUSH budget. This minimality
concerns caps, not all possible finite representations or active-only observers.

## 4. Complementary eventual-affine lemma

For a fixed context with exactly one occurrence of its hole and no both on the variable route, normalize its
final result and supply R_q. Let M be total count mass (POP plus PUSH) in its
constant operands. For every q>M, the result has exactly one variable debt
coordinate q+c, with fixed active count and fixed side placement. For input
both(R_q), the variable coordinate is 2q+c instead. In either case its offset
and active count satisfy |c|+n<=M. Thus the side/active observers are eventually
constant, though exact debt is still unbounded.

Proof invariant before final mix: p=a*q+b, r=d*q+e, n=f is constant,
a+d=1 (or 2 for copied input), and |b|+|e|+f<=M consumed so far. Any coordinate
with positive coefficient is strictly larger than all constant PUSHes available
to confront it once q exceeds the total M. Every q-dependent cancellation branch
therefore has a fixed outcome. Prefix, suffix, replay against a constant and swap
preserve the invariant, with total constant mass added to its offset budget.
Final mix merges all variable debt onto one side whenever needed, yielding the
claimed form. With repeated both on the route the coefficient may grow, so the
coefficient-1/2 statement expressly excludes that case. Section 3's clipping
theorem does allow both in a fixed observer and is the stronger query result.

## 5. Executable attack and reference boundary

The leased checker attacks three concrete claims: eventual affine behavior,
debt-only cap homomorphism, and fixed-observer clipping despite raw both and
binary/shared-hole uses. Its count candidate and literal-token reference share
the supplied operation premises and mix-side rule. The reference does not call
candidate composition or replay. Agreement is bounded implementation
consistency, not an independent source oracle or proof by enumeration.

One successful Python process ran:

    TIMEFORMAT='cpu_user=%U cpu_sys=%S wall=%R'
    time timeout 30s bash -c 'ulimit -v 262144; exec python3 -B tools/research_mixed_replay_algebra.py'

Result PASS: 2,955 linear contexts of depth 0..3 over 14 operations, 45,592
candidate/literal comparisons, 23,640 tail-affine checks; 11,368 debt-only
homomorphism checks at K=1..4 and p,r=0..6; 16,807 clipped one-hole cases of
depth 0..2 over 18 operations and p,r=0..6; 62,208 two-hole cases with debts
p,r in {0,1,4,7}, PUSH prefixes 0..2 on each side, and independent choices of
identity/swap/both at the two branches and root. The shared-hole diagonal is
included in those independent-pair cases. Both the universal positive-debt
collapse and cap-S presence mutations are killed. No random seed, timeout,
omitted shard, or production invocation.

Measured resource accounting: user CPU 1.082 s, system CPU 0.017 s, wall 1.098 s;
address space limited to 256 MiB, maximum RSS unmeasured. The first attempted
launcher failed before Python started because `/usr/bin/time` is unavailable;
the retry used Bash's time keyword. This is one successful lightweight process,
not a performance benchmark. Exact output/resource files are in isolated scratch
`/workspace/scratch/15155572c47b/mixed_attack/` and are not commit candidates.

## 6. Source boundary and handoff

The algorithm decides the displayed supplied grammar/query problem. It does
not prove the frozen Oracle or successor's actual recursive grammar debt-only,
nor that all consumers have a fixed finite PUSH budget outside that grammar.
An authentic cycle R_(1+4k), if separately source-derived, fits this theorem;
that source fact was communicated by the primary and was not audited here.
General mixed cyclic one-ID reachability, source endpoint finiteness, all-ID
correlations, extrusion/intrusion/freshening, filter registration/erasure and
whole solver soundness/principality remain omitted. No impossibility or
undecidability claim is made for those larger scopes.

Dependencies read: AGENTS; design-authority, orchestration-budget,
agent-orchestration, research-lab, git-concurrency and testing rules; current
task/research queue; annotation hygiene integration; the four assigned progress
notes. Final dependency SHA-256 snapshot:

- contextual-effect-counterexamples: `96f7c1545f9e4dbfef8c2190a8ca1b9849ee288c88fbb93e325737b36d33492a`
- contextual-effect-path-theorem: `dacb7529e02f06ab38aa37ad88ca3c1e6544b4bb1eaea95e9331ce1e27c3aca3`
- bracketed-replay-decision-obstructions: `33b332d25c68d9ab10620d4c5d94d367602617a816f3172f1ce716b58ad9b3dc`
- correlated-mixed-replay-discriminator: `7e0c48efdafe03a5c503c508c5706375382c0e1b3e9262e6b08c70c51dab0db4`

No dependency edits were made. The primary must recheck these against its
integration snapshot; this lane did not snapshot their hashes before the reads.
No Cargo, compiler tests, builds, formatting, children, or Git mutation ran.
Read-only Git show inspected only the pinned Oracle owners listed in §1.

Commit packet: exactly this note and `tools/research_mixed_replay_algebra.py`;
baseline and Oracle SHAs above; producer-frozen unreviewed conditional theorem
and bounded consistency evidence. Suggested message:
`research: bound fixed replay observers of cyclic debt grammars`.
Shared task/theory/index changes are deferred to primary. Recommended next action:
establish the actual source debt-only/consumer-budget invariant or state the
remaining mixed PUSH cycle separately. Do not close the general mixed replay
gate from this result.

Independent review: `mixed_observer_referee` inspected producer snapshot
`14cc550ba447df7debd4bf405f6fc549d147ed40e34cd1513999f9f60e551b47`
together with the companion theorem and pinned operation owners. It found no
blocking or major mathematical defect. The primary made the one-occurrence
scope of the affine lemma explicit: a repeated selected hole such as
`replay(t,t)` doubles right debt even without `both`, and is covered by the
clipping theorem rather than that coefficient-one lemma. The bounded checker
was not treated as a source Oracle or universal proof. Producer-era unreviewed
handoff text above records the earlier snapshot, not current certification.
