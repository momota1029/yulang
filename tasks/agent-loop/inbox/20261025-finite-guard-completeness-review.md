# Finite guard completeness — independent review r1

Verdict: CLEAN for the exact finite accepted-graph mathematics. One minor naming-warning finding was accepted and closed before this freeze. No open mathematical, scope, axiom or receipt finding remains. Primary retains adjudication and integration authority.

## Identity, authority and independence

Assignment: /root/finite_guard_completeness_review_astra_r1, revision 1.
Sprint: GUARD-INTERACTION-THEORY-20261025/r1.
Contract SHA-256: 1d872d3972784a4f96be0d86002efa1c3e5ca369dbff6325cde86ce6537dac06.
Baseline: e9c0a89d2f92ac0116a75e5c7e24623e4c38acd9.
Requested model/effort: gpt-6-astra/medium. Observed model/effort: UNKNOWN; no runtime metadata establishes them.
Actual runtime evidence: this fresh child received the primary's independent-review NEW_TASK and performed the recorded read-only tool calls in this session. Exact spawn acknowledgement time is not exposed here; supplied conservative lower bound is 2026-10-25T07:01:09.969096+00:00. Grant is 300 wall seconds from acknowledgement, with no reset or extension.

I am a fresh nonauthor of the proof. Source authors are /root/finite_guard_completeness_astra_r1 and /root (acknowledged repair coauthor). I performed no proof construction or source repair and have no descendants. The sole write lease is this review file. The minor finding below concerns deprecated names, not a new proof argument.

Read root AGENTS.md/AGENTS.pre-sprint.md, sprint/proof skills and governing rules, current state/README, exact contract, source/note, accepted GuardedValueGraph source and original parent note, runner/query and recorded verification. This is the sole substantive review of lane A; it does not certify lane B's mathematics.

## Frozen artifacts

- FiniteGuardDecision.lean: a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa.
- 2026-10-25-finite-guard-completeness.md: aa434e4ed6fbb30f4f0c422955e7c8ecbf8c438c70150bfbe09e9f5cd6a8ca4b.
- 20261025-guard-interaction-theory-r1-verification.jsonl: 22f1466cc14d8769b7695801e2e0fa89e19f818901873169c31c24df4cefcedd.
- .lake/guard-interaction-theory-r1-check.lean: e8189fc26cb9b44afc42bd2c50fac96301032409b9bac6acbd20c13cca3ce3d9.
- .lake/guard-interaction-theory-r1-run.py: 2d8de6ac027de1266022e0289166f77ce7c7d7900d4c22d024c68c97b8fe4b06.
- Accepted GuardedValueGraph.lean: 4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55.

All hashes were independently recomputed. Initial review source d8b76b2fa6be7a6071d51350680922ee1e60684470c43be1ae6fdbb75f617f73 and note c2e67a4657bd39b82904a2b1423fafeaa0b97278bbf574506555f633002922bd were bound by initial receipt 0fb9c8d51b6729d43d7edb203c102ef288a6d3296442f6cee3cb50271c9f72e2. Renewed freeze was supplied at 07:02:48.569559 UTC; delta inspection carries forward the unchanged mathematical review.

## Mathematical audit and original-gate application

FiniteGuardDecision.lean:8–46 defines exact terminal distance, computable bounded height and nonempty-path concatenation. Lines 50–105 prove the finite-list bound constructively using actual decidable equality. Lines 114–167 use an explicit membership decision and structural recursion on fuel alone. The invariant combines distinct seen vertices, seen.length + fuel = n, and a nonempty path from every seen vertex to the current vertex. A repeat produces a nonempty cycle; a new vertex at zero fuel contradicts the list bound. The terminal result includes a concrete terminal vertex, Observes evidence and distance < n. Reaches is extended on recursive return, so cycles reached after a nonempty tail remain reachable from the requested root. There is no assumed termination oracle.

Lines 173–212 discharge AllEnd from NoCycle by this walk, compute rank as height g n and ceiling n, and prove strict descent on every actual Node.next edge. ends_height establishes exact distance, including the maximal n-edge chain on n+1 vertices. The opposite direction uses the accepted strict-rank cycle contradiction. Thus guarded_iff_noCycle proves precisely the finite accepted-graph completeness direction missing in GVG-GUARD-COMPLETE-1. Lines 224–254 give a total scan over finRange, a certificate-or-explicit-cycle result and a constructive Decidable NoCycle; they do not assume NoCycle to run the decision.

Lines 258–279 project exactly fresh-to-fresh transparent successors. freshGraph_edge supplies an iff to the actual fresh node equation; old targets are locally terminal because allocate maps every old reference into Sum.inl. The accepted allocation source at GuardedValueGraph.lean:231–298 preserves old nodes and combines old bounded ranks with the constructed local ranks. The old graph can be infinite; its original bounded Guarded certificate is explicitly retained. No false converse from arbitrary infinite acyclicity is claimed. Lines 308–329 embed local nonempty paths into actual allocated paths and prove allocation necessity as well as sufficiency under that old certificate.

Lines 283–305 remove the caller-supplied fresh rank/ceiling/bound/decrease from the original rec_extension at GuardedValueGraph.lean:318. Old typing, old guard, per-fresh-node typing and body typing remain. The conclusion is the same graph typing, canonical observation of every old/new reference, and simultaneous closed-body typing. When the old graph is finite its guard is also constructed from its own NoCycle premise. This genuinely applies the new result to the original restricted rec obligation.

The only traversed edges are the accepted Node.next: alias/view/roll/evidence. Pair fields and lambda/delay body references are genuine guards and impose no whole-graph DAG condition. Empty graph, quantified maximal chains, transparent selfcycle, 0→1→2→2 tail, shared terminal, actual opposite-reference lambda calls, data selfcycle and fresh-to-old alias are all represented. The mutual lambdas are typed; the self-pair has deliberately no fabricated recursive-type typing claim. Evaluation termination is not asserted.

## Recorded verification audit

No Lean, build, tests, checker or Git operation was run by this reviewer. I inspected primary evidence and used read-only Python SHA/text/JSON inspection; an initial unavailable `python` command was immediately replaced by `python3`, with no file output.

Independently checked all 85 contract pins and 44 accepted module chains across 8 prior receipts against current input/output hashes; no mismatch. The five explicitly excluded historical failures are CallEntryTyping, CallEntrySpine, CallStepTyping, CallUnwindTyping and CallEntrySpineRepair. Failed and passing-but-Classical.choice intermediate rows are retained and were not accepted as final evidence.

Final receipt has 22 calls totalling 13.554920365990256 seconds. Rows 20/21/22 succeed without timeout; input snapshots before/after are equal, all current source/note bytes and artifact hashes match, and final stdout/stderr contain no warnings. Query contains 148 signature/axiom pairs (143 module declarations plus 5 named query declarations) and 23 examples. Every one of the 61 public finite-guard declarations is queried. All 148 emitted axiom results are present and use only subsets of {propext, Quot.sound}; no Classical.choice, sorryAx or new axiom is present. Finite source has no sorry, axiom, native_decide or Classical.choice token. Query projections reduce the decisive finite graph cases by rfl, and finiteRecApplied applies the new theorem to an actual fresh alias allocation and typed variable body. These examples supplement, rather than replace, the universal proofs.

## Closed minor finding FGD-R1-1

Initial final row 17 warned about deprecated if_true/if_false at FiniteGuardDecision.lean:60,64,75,80. Repository hard invariants require active-diff warnings to close. Primary accepted this and replaced exactly two if_true and two if_false occurrences with ite_true and ite_false. I compared the renewed source against row 17's complete stored source: the entire delta is exactly those four names. Note delta is exactly the final source hash plus repair chronology. Renewed rows 20–22 are warning-free and preserve the permitted axiom closure. Finding CLOSED; no substantive proof change or new reviewer is required.

## Scope and remaining owners

Recommend primary acceptance of GVG-GUARD-COMPLETE-1 only for every FiniteGraph n in the accepted research grammar. GVG-FORMS-1 (actual mu, type-changing roll/views/evidence and missing forms), GVG-REC-RHS-1 (full original RHS/binder derivations supplying fresh-node typing), ENV-GRAPH-1 (native cells/preallocation/readback and constructor correspondence), original Simple-sub A/B and full F1/FK1 remain OPEN with their original owners. The paper remains a research proposal, not production semantics. No compiler/native audit or production authorization follows. The note's review-pending language is chronological at its freeze; primary outcome records this later verdict.

No mathematical TODO remains inside this finite-graph review packet. Primary owns status synchronization, adjudication and Git integration. No lease or authority expansion requested.

## STOP receipt

Freeze UTC: 2026-10-25T07:03:36.322389+00:00. Conservative elapsed since supplied pre-dispatch lower bound: 146.353293 seconds, below 300. Unused grant is not renewed or reassigned by this reviewer. STOP after this report: no running processes, background jobs, descendants or unresolved child leases; no future source/report writes scheduled. Only the exact leased report was created.
