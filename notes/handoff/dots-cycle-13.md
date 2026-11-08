# dots cycle 13: state-dependent finite work domain

## Start, recovery and basis

- Start 2026-11-08T20:25:04Z, proof/publication and tree verification 20:31:53Z, report at 20:32 UTC. Roughly 8 minutes; final heartbeat records end. Latest user cap25 minutes overrides old50–55 instructions.
- Fetched integration `a072a7d13`, read standing orders and entire I-7 inbox. ACTIVE, cap24. Prior heartbeat cycle12 completed with report. No recovery or concurrent writer observed.
- Reused `/workspace/scratch/1d0b4aaa3394/yulang-cycle6` and cache. Local commits `ceb98c6bc`, `9f86a66e0`, `1829b2be7`.
- `work/dots-main` now has integration as an ancestor; merge commit `e321e5fdc0a39aafa4839185e4a2cd0625a52729` retains upstream changes byte-for-byte. No other branch written.

## Result and precise boundary

`CommonRoleMaterializedDomain` adds a finite source template with stable `Fin n` slot indices and independently evaluable lower/upper endpoints. Slot materialization calls existing ordinary `materialize`; int becomes `Ty.atom.int`, everything else stays unknown. Computed domain includes every unknown/int template variant and its all-candidate checked-Paterson closure. It is independent of current state. Actual filtered, solver-gated children of materialized requests remain within it after arbitrary source state changes. Consistent extension of ordinary atoms preserves previously materialized int.

**This is int-only materialization, not general interval narrowing.** Shared slots may be enumerated independently in the overapproximation, so membership does not mean the request is jointly feasible. Source templates are fixed; creation and rematerialization of new source templates inside a child driver are not implemented. Structural children are real producer children. A supplied gate allocator is arbitrary: its source-identity correctness is not claimed. Finite list existence is constructive via `domain`, not an external finite-closure assumption.

**T1c, general B4, outer resolve_exact and X13–X16 remain unproved.** No full completion or principal typing claim.

## Declarations and Japanese quantified claims

Namespace `Yulang.CommonRoleMaterializedDomain`. Every declaration is auxiliary for B4 unless specified. `n,m` are arbitrary natural slot counts; registry includes its existing checked declaration condition.

1. `eval_present`: 任意のn、State nのs、Endpoint nのeについて、e.eval sはe.variantsに含まれる。補助。
2. `int_materialized`: 任意のn,s,i:Fin nについて、slot iの評価がTy.atom.int iff 既存materialize s.atoms iがintを返す。局所の健全性・完全性の両側、B4全体では補助。
3. `evidence_int_materializes`: 任意のn,s,i、割当assignmentがs.atomsの全制約を満たし、iについてintとの双方向の明示的ordinary原子Evidenceがあれば、materialize s.atoms iはintを返す。補助。モデル存在の前提を省略しない。
4. `materialized_int_persists`: 任意のn、before/after:State n、i、beforeの全原子がafterに含まれ、割当assignmentがafterの全原子を満たし、beforeでintがmaterializeされたなら、afterでもintがmaterializeされる。補助。矛盾状態には主張しない。
5. `root_present`: 任意のn,s,source:SourceRequest nについて、source.eval sはsource.variantsに含まれる。補助。
6. `domain_exact`: 任意のn,registry,sources:List(SourceRequest n),qについて、qが計算済みdomainに含まれる iff ある列挙rootがroots sourcesに含まれ、そのrootから独立な宣言StepのReachでqへ到達する。局所の健全性・完全性。source実現可能性とは異なる。
7. `materialized_root_present`: 任意のn,registry,sources,s,sourceでsource∈sourcesなら、source.eval s∈domain registry sources。補助。
8. `materialized_reach_present`: 直前と同じ任意の引数・所属前提に加え、任意のqがReach registry (source.eval s) qを満たせば、q∈domain。補助。
9. `filtered_child_closed`: 任意のn,registry,sources,visible,q,childで、visibleの全宣言がregistryに含まれ、q∈domain、実Local visibleのChild関係がchild qに成立すれば、child∈domain。補助。
10. `state_child_closed`: 任意のn,m,registry,sources,visible、全visible宣言がregistry所属、allocate:Ty→Fin m、gateState:State m、q,childについて、q∈domainかつchildが実produce visible allocate q gateStateのchildListに含まれれば、child∈domain。補助。allocateの正当性を証明したとは主張しない。
11. `materialized_child_present`: 任意のn,m,registry,sources,sourceState:State n,source∈sources,visible（全宣言registry所属）,allocate:Ty→Fin m,gateState:State m,childについて、source.eval sourceStateに対する実produceのchildListにchildが含まれれば、child∈domain。補助。外部closureやAccの前提は不要だが、固定int-only source template断片に限定。

## Verification

`git fetch origin integration/m1-final work/dots-main` and tracking-ref fetch succeeded. Local integration merge succeeded. No full `lake build`, Audit, or `verify-lean.sh` was run, per current standing-orders/I-5. Supervisor full verification remains pending.

`cd lean && lake build Yulang.CommonRoleMaterializedDomain --wfail`, final output (exit0):
```text
✔ [280/280] Built Yulang.CommonRoleMaterializedDomain (1.1s)
Build completed successfully (280 jobs).

real	0m1.249s
user	0m0.904s
sys	0m0.455s
```

`cd lean && lake env lean --trust=0 /tmp/cycle13-audit.lean`, exit0, full output:
```text
'Yulang.CommonRoleMaterializedDomain.eval_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.int_materialized' depends on axioms: [propext]
'Yulang.CommonRoleMaterializedDomain.evidence_int_materializes' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.materialized_int_persists' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.root_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.domain_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.materialized_root_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleMaterializedDomain.materialized_reach_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleMaterializedDomain.filtered_child_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.state_child_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMaterializedDomain.materialized_child_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All eleven declarations registered in Audit. Only standard propext/Classical.choice/Quot.sound. No sorry/new axiom/native_decide; token scan empty. `git diff --check` passed. Public full `lean/` tree matched local verified tree (`git diff --exit-code HEAD origin/work/dots-main -- lean`, exit0). `git merge-base --is-ancestor origin/integration/m1-final origin/work/dots-main`, exit0.

## Publication, limitations and next steps

- Six artifacts published one by one with exact content readback: new module, design note `notes/design/2026-11-08-cycle13-materialized-domain.md`, append-only `lean/Yulang.lean`, `lean/Audit.lean`, `lean/README.md`, `notes/design/INDEX.md`. This report is seventh; heartbeat separate. All only on work/dots-main.
- Baseline integration imported26 unchanged upstream paths using existing GitHub blobs; no upstream source/spec/plan edits were authored. Four historical local-only files from older cycles were deliberately not included: cycle5 report/types, crash4 note, and old cycle8 plan path. They remain on disk. Entire Lean tree is identical, but the whole repository tree is not claimed identical because of these historical files.
- One initial compilation failed because `extends` is reserved; renamed the binder to `included`, final build passed. Publication preparation detected the above historical local-only files and excluded them before creating the integration merge. No runtime interruption or approval wait observed.
- Disk free start/end19G/19G (63G volume,70%). No new clone or copied cache; unpublished local records preserved. Usage accounting unknown.
- Yulang2: read integrated x-oracle (X13–X16 context). No fresh Yulang2 run. This domain enumeration and int-only adapter have not been runtime-conformance tested. Ordinary evidence, not unique impl guessing, remains source of known int. No new semantics decision; fragment restrictions are explicit in docstrings.
- Five substantial main bridge groups from cycle4 translation remain: source_boundary_adequate, generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact, resolve_dictionary_order_sound. This cycle advances group2, not closes it. Exact remaining small-lemma count is unknown.
- Next: (1) retain source slots/provenance through creation of child templates and prove their rematerializations are in one domain; (2) move from int-only adapter to general interval endpoint representation, without conflating unknown endpoints with source identity; (3) finite-new-facts saturation after that domain bridge. No question note added because no language-semantic choice was made.
