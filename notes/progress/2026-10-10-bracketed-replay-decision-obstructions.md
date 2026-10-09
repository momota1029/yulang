# Bracketed one-ID replay: two exact obstructions to proposed decision methods

Status: unreviewed conditional research result; frozen at handoff.
Objective: decide exact active-stack, filter, residual-head and pending-POP observations of cyclic bracketed production grammars, without count caps or changing source semantics.
Baseline: origin/research/simple-sub-intrusion 328bd8328a55da45f18393a2b78fe4aba45a161a plus primary integration bfa325ce50e5e51d1659a64ce7b47d574ddb54b5. Oracle: a58eefc31e22141574b6f20c6a5748151c6d79f1. No baseline mutation performed.
Governing inputs: contextual-effect-path-theorem sections 3–8 and contextual-effect-source-correspondence sections 2–5, including source-defined residual and compact presence consumers. Accepted decisions: preserve actual bracketing; replay is nonassociative; no finite support/count quotient, numerical cap, or new semantics.

## Exact hypotheses

Work in the natural-number lift of one authentic attachment identity i; do not use Oracle u32 saturation to obtain finiteness. Write W=(p,n,r) for left POP^p PUSH^n and right POP^r, with All filters. Families are absent on the pure-POP values below, so neither changing residual family nor same-ID family compatibility is assumed.

The conditional grammar obstruction requires the production cycle T -> replay(I,both(T)) and leaf T -> R_1, where I=(0,0,0), R_q=(0,0,q), and both is the inspected both_from_right. The cycle is a grammar-level hypothesis. It is not a proved source-reachable endpoint/owner cycle. Authenticity of i does not establish that cycle. The inspected source-schema premise for both is an actual Pos::Fun versus Neg::Fun comparison whose positive arg_eff is Neg::Bot; the child compares upper_arg_eff with the upper return-effect target after stripping its Neg::Stack wrappers (propagate.rs:234–248,401–410). Its context is both_from_right(W). A replay returning that child to the same eligible retained bound slot is an additional unproved premise. Source ownership, kinds and these endpoint conditions must hold; an arbitrary unary edge carrying the name both is not enough.

Relevant exact source owners: crates/infer/src/constraints/mod.rs:3566–3612 (swap, prefix, suffix, both_from_right, replay); constraints/directed_weight.rs:12–39,137–176,399–420 (mix and count composition); constraints/machine/propagate.rs:234–248 (actual pure argument-effect branch). Source correspondence records row_effect.rs:175–233,1190–1244 (changed residual family and gamma splitting) and compact/collect/mod.rs:1019–1043 (entry-presence observer). These source rules are dependencies, not conclusions proved by a checker.

## Method 1: finite word automaton / ordinary pushdown normal-form language

For every positive q, both(R_q)=(q,0,q). Replaying I with that value leaves left POP^q and right POP^q before mix. Both sides are present; mix appends the right POP^q to left POP^q, obtains POP^(2q), and moves that pure residual to the right. Therefore

    replay(I,both(R_q)) = R_(2q).

Induction on the finite derivation chain proves the grammar's exact value set is precisely {R_(2^k) | k>=0}. There are no other productions and every recursion increases k once. A nested RHS uses one nonterminal and two productions; a flat production grammar uses T -> R_1 | replay(I,U), U -> both(T).

The corresponding unary normal-form language is {D^(2^k) | k>=0}. It is not regular: if pumping length is h, choose 2^k>h and pump a nonempty segment of at most h letters once; the length lies strictly between 2^k and 2^(k+1). It is not context-free either: in the CFL pumping decomposition the combined pumped length is between 1 and h; the same choice and one extra copy give a length strictly between consecutive powers of two. This uses the ordinary pumping lemmas and does not rest on an unproved source hypothesis beyond the displayed grammar cycle.

Consequently no finite automaton or ordinary pushdown grammar can represent the exact reduced unary output language for all such bracketed grammars. This obstruction concerns the language representation of the whole cyclic grammar, not the computability of an individual transition. In particular, unary doubling D^q -> D^(2q) is itself finite-state transducible. Iterating such an operator under a cyclic grammar need not retain a regular output language. An arithmetic, copying tree transducer, or higher-order machine may still decide observations; the example does not exclude those formulations.

This is NOT undecidability. On this grammar every active-stack query is false; pure right debt is always present; after swap the left pending-POP observer is true. For a concrete prefix PUSH^q after swap, identity occurs exactly when q is a power of two, which is decided by repeated exact halving. Infinite/non-context-free residual language alone leaves terminating observation algorithms possible.

Source operator invalidating this attempted extension: both_from_right copies the same right count onto the left while retaining it on the right; replay mix then adds those copies. The section-3 walk construction contains no such duplication. Disallowing the pure branch or imposing a count cap would change the task unless a source-derived invariant proves the cycle unavailable.

## Method 2: componentwise upward-demand saturation on full directed counts

Let pending(W) mean p+r>0, and active(W) mean n>0 after directed mix. Both are upward predicates on raw natural coordinate tuples. The required predecessor closure fails on normalized source-algebra inputs.

For pending, take X=I and Y=(0,1,0). Then X<=Y componentwise, but

    replay(X,R_1)=R_1       (pending true)
    replay(Y,R_1)=I         (pending false).

Thus the predecessor of the pending target under t(Z)=replay(Z,R_1) is not upward. It cannot be represented exactly by the finite minimal antichains used in the section-3 proof.

For active, take X=I and Y=(1,0,0). Then X<=Y, but

    replay((0,1,0),X)=(0,1,0)    (active true)
    replay((0,1,0),Y)=I          (active false).

Thus an active observer's predecessor under t(Z)=replay(PUSH_1,Z) is also not upward on the full three-coordinate order. Reversing a debt coordinate is not an automatic repair: the reversed natural order has the infinite bad sequence 0,1,2,..., so the supplied Dickson argument no longer applies. This does not rule out a different domain, mixed order, or effective non-upward representation; none is established here.

Source operator invalidating this attempted extension: replay performs exact same-ID cancellation of active pushes against debt, and mix transports uncancelled debt between sides. The one-sided append theorem deliberately eliminates leading debt only for its forward active queries; full bracketed consumers cannot eliminate it.

The fixed-family upward proof also cannot silently cover actual residual-head consumers: row_effect subtracts retained head families from the active payload without changing ID/count, then splits through gamma. The local compact observer checks ID entry presence including leading POP. These are already established source boundaries in the governing notes; they were not newly proved or widened here.

## Result and stopping boundary

Claim class: conditional exact grammar counterexample plus two minimized local predecessor witnesses. No general impossibility or terminating exact algorithm for arbitrary bracketed grammars is proved. The shared untouched premise after two methods is an effective observation domain closed under copying by both_from_right, exact binary replay, side transport, payload residualization and the actual compact presence predicate. Ordinary finite automata/PDA residual languages and componentwise upward antichains do not provide that domain.

No third equivalent toy model was run. A grammar with finite endpoint keys is still a terminating representation construction, not a decision proof. In addition, gamma is keyed by the exact residual weight in row_effect.rs:185–233; even a fixed-endpoint theorem does not establish that the source creates only finitely many such endpoints. This is a separate source-finiteness premise, not an inferred divergence result.

Oracle independence: this is a symbolic derivation from inspected pinned source rules. It has no executable oracle, candidate checker, differential comparison or independently reviewed proof. The cited source itself remains the dependency of both calculations. Mutations and seeds/ranges: none. Coverage: all q>=1 in the conditional doubling grammar; two exact local input pairs for predecessor failure. Omitted: actual source reachability of the grammar cycle, all-ID correlations, parameterized families, family compatibility after residualization, source finite endpoint generation, full compact support/generalization, whole solver termination, and production soundness/principality.

Checks: read-only git show of the four exact pinned Oracle owners above, and authorized read-only git rev-parse 328bd8328 for the full baseline SHA; no Cargo, compiler tests, build, formatter, benchmark or Git mutation. One failed narrow read used the wrong crates/compiler prefix; corrected to crates/infer before source reasoning. Resource usage: a bounded symbolic proof effort and lightweight reads only; CPU/RAM and exact wall time unmeasured. No child agents. Changed path: only this isolated scratch note.

Recommended next action: establish or refute the source-owned endpoint/port invariant that prevents a cyclic both_from_right -> replay -> same retained bound route. Supply a minimized authentic source/certificate witness if it fails. This directly decides whether the copying obstruction belongs to the required consumer, and avoids asking another finite-count probe to prove the source premise.

## Commit packet

Exact lease/output: /tmp/yulang-bracketed-replay-proof/result.md (scratch-only; no repository path leased and no commit-ready repository artifact).
Baseline SHA: 328bd8328a55da45f18393a2b78fe4aba45a161a; primary dependency integration: bfa325ce50e5e51d1659a64ce7b47d574ddb54b5; pinned Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1.
Dependency hashes changed: none observed or changed by this lane; current repository dependency hashes not independently rechecked because read scope was pinned.
Review status: unreviewed producer argument; frozen at handoff; no independent review claim.
Checks already run: exact scoped source reads and baseline SHA resolution only; no executable experiment needed for these symbolic witnesses.
Proposed checkpoint message, only if the primary separately leases and imports the note: research: identify copying and monotonicity obstructions in bracketed replay.
Shared-record deltas left for primary/curator: record the conditional power-of-two grammar obstruction and failure of naive full-count upward saturation; keep the general bracketed observation gate open; add source cyclic pure-port copying reachability as the discriminating next premise. Do not declare the source cycle reachable or a solver impossible.
