# R57 Luna source-owner trace

Status: frozen read-only constructor/source-owner trace; author stopped; fresh review pending.
Sprint: `original-name-two-capture-20261019-r57`, revision 1.
Contract SHA-256: `b8fb35aa130304ab459b1c8ead188c5ebd6c86bb177420842f279a1d17f4c5a9`.
Baseline: `abef89fb8491c5709173ba55c76af7886897a5bd`; activation commit `b3530cd58`.
Exact leases: this file and `tasks/agent-loop/inbox/20261019-r57-implementation.md`.

No parser, preflight, solver, tests, build, runtime, probe, instrumentation, or measurements were run. R57 is static source inspection only. Parent forwarding-preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED.

## Exact source and constructor-domain check

The frozen candidate retains R56's concrete `io` declaration, explicit computation formals `q`, `t`, and `x`, direct Name body `forward(t)=t`, and original block/order, with one binding `b=forward x` inserted after `z=loop x`. Final result stays `z`. Each Apply argument is still the whole Name of its current formal (`x`, `x`, `x`, `q`); this is constructor-level membership in the unchanged direct-current-formal/Name fragment, not a claim that the source fully types or executes.

The source collector registers an annotated Lambda formal as Computation when its annotation has an effect row (`crates/yu-solver/src/candidate_source.rs:869–879`). A Name of that formal emits `FormalNameEffect`; a local Name targeting an active initializer emits Link, while an installed local emits Local (`candidate_source.rs:1219–1253`). Nested block initialization executes in binding order, with each initializer before its Install; initializer evaluation effects are routed to the block before installation (`candidate_source.rs:1038–1124,1642–1689`). Therefore the relevant ordinary action order is `a` Local-forward/FreshUse, `z` active-loop Link and Apply, `Install(z)`, then `b` Local-forward/FreshUse and Apply. The later outer `loop q` occurs after loop installation. No R56 source-set or physical-owner conclusion is assumed by this order statement.

## Immutable reference graph

The source value graph assigns each nested initializer its own `Local(binding.id)` owner; Apply event origin is that owner and receiver is the callee's expression value (`crates/yu-solver/src/candidate_value_graph.rs:89–143,181–196`). For this changed source the semantic Name edges are:

```text
forward → Parameter(t)
a       → Local(forward), Parameter(x)
z       → Local(loop), Parameter(x)
b       → Local(forward), Parameter(x)
loop    → Local(z)
outer   → Local(loop), Parameter(q)
```

Thus the four Apply events are `ea=(Local(a),Local(forward))`, `ez=(Local(z),Local(loop))`, `eb=(Local(b),Local(forward))`, and `eo=(Module(outer),Local(loop))`. Only `ez` is SCC-qualified, by `loop→z→loop`. Both forward-use Apply origins point to `Local(forward)` without a return path; the new `b` reference creates no edge from `forward` back to `a` or `b`. This is source qualification only; it does not by itself settle physical aliasing or source-set reachability.

## Actual Local capture ownership

`Action::Local` resolves to an installed `LocalScheme` selected by the same `forward` binding slot (`candidate_source.rs:1251,1687–1689`; `crates/yu-solver/src/candidate_scheme.rs:1964–1987`). Each Local occurrence starts a capture from that scheme's retained root and boundary (`candidate_scheme.rs:1995–2042`). `prepare_candidate_fresh_use` allocates a fresh context-use identity on each capture and constructs one row image table for that use (`candidate_scheme.rs:1555–1608`). Distinct action occurrences are retained independently in the local-use route; restoration is completed through that frame's own FreshUse maps before the captured root link is admitted (`candidate_scheme.rs:2011–2060,2100–2190`).

The source-level routing establishes how the two Local actions are separate capture constructors; the changed-input rows, maps, write footprint and direct restorations are derived below.

The incremental execution order is relevant to the intervening write set. In candidate source mode, `InferenceSession::execute` skips `admit_all_collected_facts()` before executing candidate loose/expression schedules (`crates/yu-solver/src/lib.rs:10426–10440`). Source collection having recorded a later event therefore does not itself pre-admit that event's relation before `a` or `z`. The block schedule emits each initializer before its Install; after `z`'s initializer and Install, it reaches `b`'s initializer (`candidate_source.rs:1038–1124,1642–1689`). On successful completion, `finish_route_transaction_with_candidate_accounting` calls `commit_local_use`; `GraphState::commit_local_use` pops that completed frame and publishes its `LocalFreshRoute` under the exact occurrence, with a debug assertion that the occurrence had no earlier route (`candidate_scheme.rs:662–691`; `lib.rs:9309–9312`). Thus the completed `a` frame is not an open continuation that `b` can resume. This is still an ownership/schedule fact, not yet the needed complete physical write-footprint proof.

## Changed-input physical trace

I rederived the recursive processing relation against this input rather than importing R56's conclusion. `L2<=N3` is the active Link and contributes no Apply event; the Native Apply contributes `N<=Dz` with `{ez}`. Replay of these two physical inputs gives `L<=Dz` with complete processing source set `{ez}` and identity context. The selected negative traversal at target 2 has structural ports `(X2+,h_z3+,C_z3−,U_z3−)`: it stops at `X2`, and the positive closure of `h_z` stops at `ex2`; `C_z` and `U_z` have no selected upper yet. The complete retained row-parent group I obtain from this walk is `(h_z3,h_z+,+,2)`, `(C_z3,C_z−,−,2)`, `(U_z3,U_z−,−,2)`, each retaining `{ez}`. The physical source links are `(h_z,−,h_z+)`, `(C_z,+,C_z−)`, `(U_z,+,U_z−)` and copied lower `(h_z+,+,ex)`. The original `forward` rows are not in that group.

For those three pairs, qualified settlement appends both copied bound sides to the selected parent representative, combines level/non-generic metadata, redirects each copied row to its parent and replays. It does not merge `X`, `ex`, `F0`, or any `t/n/r/v` provider row. This is consistent with the ordered Visit guard and merge implementation (`candidate_extrusion.rs:78–167,229–258,330–340`; `candidate_intrusion.rs:308–386,568–713`; `lib.rs:12369–12398`). The physical `a` path is the first-use path rederived in R57 proof §4: `a` writes the freshly reconstructed rows `t_a,n_a,r_a,v_a,F_a` and its own callee/effect rows. Its effect route includes direct keys `(h_a,−,t_a)`, `(t_a,+,ex)`, `(n_a,+,ex)`, `(r_a,+,ex)`, `(r_a,−,C_a)`, `(C_a,+,ex)`, `(C_a,−,E_a)`, `(E_a,+,ex)`, `(E_a,−,B)`, `(ex,−,B)`, alongside restored `(t_a,−,n_a)`, `(n_a,−,t_a)`, `(n_a,−,r_a)`. Those compose a path to `B`; they do not create direct `(r_a,−,B)`. Bound admission chooses the younger endpoint, and row/row propagation creates no extrusion parent (`candidate_extrusion.rs:856–969`).

Between the qualified group and `b`, the source schedule performs the `z` initializer effect routing and `Install(z)`. The group-local rows are only reachable through the established loop/Name/initializer owners; they do not provide a structural operand back into the forward Function. The new `eb` is nonqualified and is not an input to `L<=Dz`; `eo` occurs later. Therefore the pre-`b` writes leave the original `F0` closure and its physical `(t0,−,n0)`, `(n0,−,t0)`, `(n0,−,r0)` bounds intact, with original rows still generic at level 2 and representatives unchanged. This is a finite write-footprint claim under successful ordinary prefixes, not a conclusion from SCC qualification alone.

The second Local action is the distinct `b` occurrence at the same installed `forward` slot/root/boundary. The completed `a` frame was removed when its route committed, and the per-occurrence route map rejects publishing a second route under the same occurrence. `b` therefore captures live `F0` afresh. Capture follows the positive Function and its captured bounds, so the actual second graph includes `t0,n0,r0` and the three original bounds; its authentic partial map has `mu_b(t0)=t_b`, `mu_b(n0)=n_b`, `mu_b(r0)=r_b` (and maps the captured root/Function rows on the same table). `prepare_candidate_fresh_use` allocates a distinct `context_use` and one canonical image per local generic source row; numeric identities are immaterial. Function reconstruction and captured-bound restoration share this table. Direct restored provider keys are `(t_b,−,n_b)`, `(n_b,−,t_b)`, `(n_b,−,r_b)`; these are actual restorations, not transitive conclusions. The new `b` root link follows restoration. If its Native Apply prefix continues, `{eb}` seeds its own Function comparison; it gives `h_b<=t_b` and `r_b<=C_b`, while the restored chain yields `h_b<=t_b<=n_b<=r_b<=C_b<=E_b`. This supplies the bounded second-use mapped scalar admissions; it is not observed full-solver or runtime behavior.

My static owner trace agrees with Sol's frozen changed-input result. It uses the distinct `ea/ez/eb/eo` event identities and symbolic physical keys above; numeric solver row/parent/context-use identifiers remain unknown. Parent forwarding preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED. No code or execution authority follows.

Root author is not an independent reviewer. This trace and its inbox handoff are frozen; the author lane is STOPPED / WRITES_STOPPED. The exact hashes are recorded in `tasks/agent-loop/current.json`. Fresh independent review is pending.
