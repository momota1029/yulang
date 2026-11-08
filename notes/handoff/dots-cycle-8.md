# Dot cycle 8 — focused proof and recovery

## Status
Partial progress. General B4/T1c and X13–X16 outer PROVED remain unachieved.
Original worker started 2026-11-08 15:54:22 UTC, heartbeat stopped at 15:55:30, and was interrupted by the coordinator at about 16:15. The crash/hang cause is unknown. Recovery began 16:15:40 and completed about 16:18 UTC. Code is preserved in local commit `94638c89b`; latest fetched integration was `38631d5b3`.

## Result and assumptions
New module `Yulang.CommonRolePotentialChildClosure` computes a finite potential descendant list from all structurally matching declarations, not just the selected declaration. Termination is derived from the checked registry's structural decrease, not external fuel.

- `scan_hit_complete`: 任意の role、下上端点 lo/hi、可視宣言列 visible、宣言 d、payload lp/hp について、dがvisibleに属しroleが一致し、独立Inspectが両端でhitするなら、実scanにそのhitが含まれる。完全性の補助。
- `mem_next`: 任意のvisible、request q、childについて、実nextへの所属と独立Step visible child qが同値。健全性・完全性。
- `closure_complete` / `closure_sound` / `closure_exact`: 任意のchecked Registry、root q、targetについて、計算されたclosureへの所属と独立Reach registry q targetが同値。健全性・完全性。
- `reach_trans`: 任意のregistry、q、middle、targetについて、qからmiddleとmiddleからtargetのReachを仮定するとqからtargetのReach。補助。
- `filtered_child_step`: 任意のchecked registry、visible、q、childについて、visibleの全宣言がregistryに含まれ、実resolverのChild(Local visible) child qが成り立つなら、registryのStep child q。健全性の補助。
- `filtered_children_closed`: 任意のchecked registry、visible、root、q、childについて、visibleがregistryの部分列集合、qがrootのclosureに属し、実Child(Local visible) child qなら、childもrootのclosureに属する。有限仕事領域の補助。

The endpoints remain fixed structural syntax. This is not a proof for endpoint narrowing, arbitrary state-dependent materialization, generic saturation, final diagnostic classification or dictionary equivalence. Candidate filtering is supported only under the explicit visible-subset premise.

## Validation
Recovery reran:
```sh
cd lean
lake build Yulang.CommonRolePotentialChildClosure --wfail
lake env lean --trust=0 /tmp/cycle8-audit.lean
```
Exit 0. Output:
```text
Build completed successfully (270 jobs).
'Yulang.CommonRolePotentialChildClosure.mem_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePotentialChildClosure.closure_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePotentialChildClosure.filtered_child_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRolePotentialChildClosure.filtered_children_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
Full build/verify-lean was not run, as current standing orders prohibit it for dot. Yulang2 was not re-executed during recovery; original worker reported reading existing oracle. No new semantics was chosen during recovery.

## Publication and recovery limits
Published one module, exact append-only updates to Yulang.lean/Audit.lean/README.md, one design note and this report on work/dots-main only. Module and all three integration files were reread and byte-equal to the preserved local code. The branch's whole tree is not claimed equal to latest integration; upstream parser changes were not copied during this short rescue.

The original design note was mistakenly committed locally under forbidden notes/plan. That path was not published. Its text was preserved under notes/design instead. Original local commits remain intact.

Next bridges: (1) narrowed/materialized endpoint children into a computed source domain; (2) state-dependent saturation termination; (3) final independent diagnostic classification and dictionary adequacy. These remain substantial and unproved. Usage accounting unknown.
