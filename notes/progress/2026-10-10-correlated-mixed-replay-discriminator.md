# Correlated mixed-bracketing and residual/compact discriminator

Status: frozen producer research; no independent review, source reachability, or production claim.
Baseline: assigned `origin/research/simple-sub-intrusion` at `328bd8328` plus primary commit `bfa325ce50256a6c980ef3c5a59ea4986e22ef60`.
Lease: `/tmp/yulang-bracketed-replay-search/` only.

## Objective and method

Test whether active/filter/presence summaries suffice for exact mixed bracketed replay with one ID. Use correlated nested trees, a copied-tree swap/replay observer, terminal concrete-head residual consumption, and the local compact left-word presence predicate. Preserve every replay grouping; use natural counts without caps. This is a different continuation from the previous fixed-prefix POP-count witnesses: the observer itself copies its supplied tree and swaps the copy, so its count challenge grows with that tree.

Governing sources: contextual-effect-counterexamples §§4–7; contextual-effect-path-theorem §§5–8; contextual-effect-source-correspondence constructor/contextual-operation/filter/residual/source-invariant sections and its fixed-family/compact follow-up; annotation-effect-hygiene-integration §§1–4,6. Rules research-lab, design-authority and git-concurrency read. Dependency SHA-256s are recorded in `dependencies.sha256`; the four dependency hashes remained unchanged at final recheck. No source language meaning was selected here.

## Explicit hypotheses and claim classes

Established inputs, retained at their stated scope: replay is nonassociative; exact source operation order must survive; one-ID count composition/mix and swap equations are the source-inspected equations in the pinned notes; active residual families may change; local compact presence can observe leading unmatched POPs.

Candidate synthetic schema: let e=(0,0,0), D=(1,0,0), P=(0,1,0). P_c is a fixed left-associated replay tree of c copies of P, including e for c=0. Define

    X_c(0) = e
    X_c(k+1) = replay(D, replay(X_c(k), P_c)).
    C(t) = replay(t, swap(t)).

The two occurrences of t in C(t) are copies of **the same chosen finite derivation**. An ordinary grammar production `replay(X,swap(X))` with independent choices at its two X occurrences does not impose that correlation. The model therefore concerns an explicitly correlated tree transformer, not the unrestricted denotation of that production. Actual source ownership or retained evidence must justify any such correlation before using its arithmetic as a source invariant.

All replay operands have the same one-ID active family {E}; head consumption changes that family only after the last replay. The only subsequent operation is swap, which discards active payloads. The model never replays unequal same-ID family payloads. Inactive family fields in code are placeholders; their values are not an asserted model of source pop-entry payload layout. F is All for all replay steps. The filter Empty is an external local check, not an insertion scheduling model. The compact query is specifically the supplied left StackWeight method-input predicate with one declared fact (i,{F}), F distinct from E, and written head E. It is not a complete directed-context conversion/public output collector.

The derivation below is a conditional theorem under that schema and these operation equations. The executable run is bounded characterization/consistency evidence. Neither establishes source-schema reachability. There is no independent source oracle or Oracle execution.

## Derivation and smallest witness in the correlated family

Induction on k, retaining the displayed nested grouping, gives

    X_c(k) = (k, ck, 0).
    swap(X_c(k)) = (0, 0, k).

At C's root, replay keeps (k,ck) on the left before mix and appends k POPs from the right. For k>0:

    C(X_c(k)) = (0,0,(2-c)k)      if c<=1;
    C(X_c(k)) = (k,(c-1)k,0)     if c>=2.

For k=0 the result is e. This is an exact calculation for these trees, not associative flattening of arbitrary replay expressions.

Compare c=1 and c=2. For every k>0 their inputs agree on signs of p,n,r, active family {E}, active-filter result, and local compact left presence. For k=1:

| Stage | c=1 | c=2 |
| --- | --- | --- |
| Input | (1,1,0;{E}) | (1,2,0;{E}) |
| C | (0,0,1) | (1,1,0;{E}) |
| Consume written head E | (0,0,1) | (1,1,0;Empty) |
| Check active family against Empty | passes | passes |
| Compact left presence | false | true |
| Swap consumed result | (1,0,0) | (0,0,1) |
| Active presence after swap | false | false |
| Compact left presence after swap | true | false |

The pair (1,1) versus (1,2) minimizes positive pop/push counts **within the specified p=k,n=k versus p=k,n=2k family**: k=1 is its first nonempty depth and no smaller positive counts exist. No global minimality over arbitrary source trees is claimed. The concrete compact retention formula here is E retained iff this left word contains i, because the sole fixed fact would otherwise exclude E.

Consequently even a summary retaining both sign bits, active family/filter observations and initial compact presence cannot give C's exact root compact observation. Keeping only active depth after swap also loses the pending-POP discriminator. Conversely, this witness does not refute every finite representation or observation algorithm: the syntactic c and the Boolean k>0 yield a terminating exact scheme for the entire restricted family, without enumerating counts. After head consumption, the Empty check always passes; compact presence is `(k>0 and c>=2)`, and after swap it is `(k>0 and c<=1)`. This is a structural finite decision theorem for this schema, not a finite congruence of arbitrary weights.

## Executable and oracle independence

`search.py` evaluates explicit immutable tuples as trees. The count candidate uses arithmetic composition and guarded mix. The reference expands each evaluated child into literal POP/PUSH tokens, reduces the concatenation, then applies right POPs and the same directed-side placement rule. The reference does not call candidate composition or replay. It does share the supplied count-to-word encoding, swap equation, mix-side rule, one-ID/common-family restriction, residual equation and local observers. Agreement therefore validates arithmetic/grouping implementation against those premises; it cannot prove the source rules, insertion schedule or source reachability. Family/compact mutation checks use the supplied local equations directly, not an independent compiler oracle.

Coverage: exhaustive k=0..12 and c=0..3, including empty, pop-only, balanced and excess-push trees; 104 candidate/reference comparisons (input and correlated observer for each of 52 pairs); 12 c=1/c=2 paired nonempty depths. No random seed. Maximum reference root count is 36 pushes, far below Oracle numeric-width boundaries. No enumeration over arbitrary grammars, omitted shards, or timed-out search.

Three named mutations were rejected:

- Treating active family as immutable after E-head consumption rejects the c=2 result against filter Empty, while the actual residual Empty passes.
- Implementing compact presence as active-only loses the leading POP after swap of the c=1 result.
- Reassociating `(D replay P) replay R` into `D replay (P replay R)` changes root compact left presence. This is an integration guard for this tree, not a new associativity result.

## Commands and resources

Executed once, one lightweight Python process; resource envelope authorized by primary: one process/run, 128 MiB address space, 30 s/run, at most 90 s aggregate search CPU.

    /usr/bin/time -f 'cpu_user=%U cpu_sys=%S wall=%e max_rss_kib=%M' \
      timeout 30s bash -c 'ulimit -v 131072; exec python3 -B /tmp/yulang-bracketed-replay-search/search.py'

Result: PASS; 104 comparisons, 12 paired depths, all three mutations killed. Recorded user CPU 0.04 s, system CPU 0.00 s, wall 0.05 s, maximum RSS 12,960 KiB. Timing is resource accounting of one run, not a benchmark. `result.json` and `resources.txt` preserve exact output. Repository rules/notes read; no Cargo, builds, compiler tests, formatter, children, or Git mutation. Initial setup mistakenly used two read-only Git queries (HEAD and status) before treating the packet's no-Git boundary literally; primary was informed, and no subsequent Git command ran. No repository paths changed by this lane.

## Blocker, omitted scope, and recommended next action

Precise remaining premise: the actual source-produced replay/Function rule graph has not been shown to generate the correlated tree transformer C, nor to retain the balanced/drift ratio invariant of X_c. This is the production-relevant source/consumer seam; increasing k cannot resolve it. Only this one bounded model attempt was made. No Oracle divergence, global termination failure, source rejection limit or all-grammar decidability result is claimed.

Omitted: changing-family replay and its agreement/failure conditions, residual gamma generation/incidence, multi-ID interactions, open registered filters and insertion order, complete compact/public support, function source formation, admission/self-drop/subsumption, freshening, extrusion, intrusion and rollback. The full arbitrary mixed-bracketed grammar observation gate remains open.

Recommended next action: source-correspondence lane should determine whether the owning Function/replay construction retains the exact shared derivation/count correlation needed by C. If yes, test this consumer there; if no, use the actual retained production schema as the input to the observation analysis. A generic sign-summary quotient is already falsified, while the restricted syntax-directed exact scheme remains valid under its explicit premise.

## Commit packet

Exact frozen scratch paths:

- `/tmp/yulang-bracketed-replay-search/search.py`
- `/tmp/yulang-bracketed-replay-search/report.md`
- `/tmp/yulang-bracketed-replay-search/result.json`
- `/tmp/yulang-bracketed-replay-search/resources.txt`
- `/tmp/yulang-bracketed-replay-search/dependencies.sha256`

Baseline SHA: `bfa325ce50256a6c980ef3c5a59ea4986e22ef60` (assigned ancestry `328bd8328`). Dependency changes: none; SHA-256 snapshot in dependencies.sha256. Review status: producer-frozen, unreviewed research; no independent review claimed. Checks already run: the one bounded deterministic model command above and final SHA-256 dependency recheck. Proposed one-line message if the primary elects to promote a self-contained repository artifact: `research: distinguish correlated mixed replay residual and compact observers`. These temporary paths are not repository commit candidates without a new primary-owned lease/placement step.

Shared-record deltas intentionally deferred to primary/curator: record the new correlated-tree summary discriminator, the conditional syntax-directed finite observation scheme, and the exact source correlation premise. Preserve the full mixed-consumer/source-reachability gate as open. No shared index/task/authority/question-board file was edited. Writes stop at this handoff.
