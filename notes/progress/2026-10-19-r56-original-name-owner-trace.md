# R56 Luna source-owner trace

Status: bounded read-only compiler-owner trace; independent review pending.
Contract: `tasks/agent-loop/sprints/original-name-source-trace-20261019-r56.md`, rev. 1, SHA-256 `052492309a379f3eef24078b9090f8e7081dceaf2e4c7af37ff90c75ffa013cd`.
Producer artifact: `notes/theory/2026-10-19-r56-original-name-source-trace.md`, SHA-256 `ee5edcaaa64b32323cd60b1a960aecd7f8cf239e17103a7f0e2bcc14cf8691fd`.

No parser, preflight, solver, test, build, runtime, probe, instrumentation, or measurement was run. This trace is not independent review. Parent forwarding-preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED.

## Root source-owner check

The exact sample stays in the parent’s direct-current-formal/Name fragment: the three annotated formals `q`, `t`, and `x` carry explicit computation annotations, and each Apply argument is the whole current-formal Name. Source collection registers an annotated Lambda formal as Computation (`crates/yu-solver/src/candidate_source.rs:869–879`). A Name of such a formal emits `FormalNameEffect`; a local Name that resolves to an active initializer emits `Link`, otherwise the installed local takes the `Local` route (`candidate_source.rs:1219–1253`). Binding initializer actions precede Install (`candidate_source.rs:1090–1124,1642–1689`). Thus `forward x` is one installed-local/FreshUse occurrence, `loop x` reads the active recursive initializer, and later `loop q` reads the installed loop. There is no second static `forward` Name.

The source value graph defines Apply event qualification by SCC equality of the initializer owner and callee receiver (`crates/yu-solver/src/candidate_value_graph.rs:89–143,181–196,245–247`). The resulting immutable events are `ea=(Local(a),Local(forward))`, not qualified; `ez=(Local(z),Local(loop))`, qualified by `loop→z→loop`; and `eo=(Module(outer),Local(loop))`, not qualified. This confirms the source-graph part of the producer trace; qualification alone is not used as an alias argument.

I independently followed the storage owners relevant to the proposed transition. Relation replay unions the two input relations’ source-event sets (`candidate_context.rs:3763–3835`); `retain_extrusion_parent` snapshots the currently processed relation’s source set and physical copy/parent rows, and queues only if a retained event qualifies (`candidate_intrusion.rs:305–365`). Qualified settlement resolves representatives, appends both physical bound sides to the parent owner, transfers origins, combines level/non-generic metadata, and redirects the copy row (`candidate_intrusion.rs:568–713`). These rules make provenance, representative equality, and an actual physical BoundKey distinct evidence.

Capture expands only the actual canonical root and rows reached through their stored endpoints and bounds (`candidate_scheme.rs:755–790,1017–1155,1216–1292`). Its FreshUse reconstruction has one per-use row map; a row is freshened only when the captured row is local, above the boundary, and generic, while shared/nonlocal rows retain their live representative (`candidate_scheme.rs:1555–1608`). Uncaptured forward endpoints therefore receive no image through source metadata alone.

## Bounded physical trace to review

The producer derives, under successful ordinary constructor-prefix conditions, the first forward capture map `mu1` on the actually captured original `t0,n0,r0` rows, yielding `t1,n1,r1` at level 3. The direct physical effect route is:

```text
(na,+,ex), (na,−,ex), (na,−,t1),
(t1,+,ex), (t1,−,n1), (n1,+,ex), (n1,−,r1), (r1,+,ex),
(r1,−,Ca), (Ca,+,ex), (Ca,−,Ea), (Ea,+,ex), (Ea,−,B), (ex,−,B)
```

The path gives composed `ex<=B`; it does not assert a directly materialized `r1<=B`. The physical owners and signs do not themselves create a reverse edge from `ex` or `B` to the forward Function rows.

For recursive demand `Dz=Function−(X2+,nz3+,Cz3−,Uz3−)`, the active Link gives `(N,+,L)` with no Apply event, the Apply contributes `(N,−,Dz)` with `{ez}`, and the producer’s ordered replay derivation gives `L<=Dz` with complete source set `{ez}`. The traversal target is 2: `X2` and selected `ex2` stop at the target; the complete retained group is `(nz3,nz+,+,2,{ez})`, `(Cz3,Cz−,−,2,{ez})`, `(Uz3,Uz−,−,2,{ez})`. The producer reports no forward row in that group. Settlement can merge only those listed copy/parent pairs; a source association is not a row alias.

The producer then traces two captures: `z` first at boundary 2, with shared `Uzbar2` and no forward endpoint image; later the outer `loop q` Local capture at boundary 1 reconstructs loop ports and the `ex<=B<=rLoop` route under map `nu`. The producer claims none of `t0,n0,r0,t1,n1,r1` occurs in that capture graph, so `nu` is not a later same-provider `forward` map. Static source schedule confirms the order and absence of another forward occurrence. The complete physical closure and endpoint absence are specific claims for fresh review, not yet accepted facts.

## Bounded application and remaining work

If the producer’s constructor derivation survives independent review, this exact source fails to supply R55’s proposed original-provider alias/exposure before a later capture of the same provider. The result is conditional on successful source actions, scalar drains, and restorations; it is not observed solve completion or a counterexample. It does not establish the general preservation invariant, arbitrary finite histories, or noninterference for other original-domain inputs. R55 remains OPEN 0→0.

Next source-owner task stays separate: find a distinct original-domain input that reaches the original provider closure through structural/physical operands and has a later capture of that same provider, or prove the applicable source case excludes it. Any later packet needs complete source sets, signed parents, physical keys, capture boundary, and honest partial maps. R56 grants no new source, code, execution, instrumentation, or semantic authority.

Root/Luna exact leases are this file and `tasks/agent-loop/inbox/20261019-r56-implementation.md`. Root authored this trace and makes no review claim. On freeze, record both byte hashes and stop writes before the assigned independent compiler and spec reviews.
