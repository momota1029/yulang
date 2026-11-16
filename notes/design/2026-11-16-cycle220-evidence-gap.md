# Cycle220: I41 後の EvidenceNode と amalgamation の残余

## 状態

2026-11-16、cycle220 の復旧環境で既存 Lean 定義・定理を読み直した記録。
この文書は **未証明の次課題** を特定する。V8 EvidenceNode の証明でも反証でもない。
Lean コード・ターゲット意味論はこの調査では変更していない。
cycle219 の protected aggregate / stale bounds 反例案は、この環境では確立していない。
旧環境の未公開コードを回収した、またはその検証結果を再現したとは扱わない。

## 量化を分離する

1. `HeadSharingConflict220.Feasible` は、ある journal model とある current Frame で sharing が成立するという **存在命題**。
2. `Frame.prepared` の `HeadModels` witness は raw head の存在モデル。1 の journal model と同一とは限らない。
3. `CurrentCompletion216.common_iff` は、journal・Agreement・HeadModels の **共通モデル** があることと、journal・Agreement・Overlap の共通モデルがあることを同値にする。
4. `CurrentHeadEquations217.common_iff` は、さらに HeadEquations を加えた共通モデルについて同じ Overlap 条件を与える。
5. `B4SkeletonV8.EvidenceNode` / `EvidenceAt` は、指定された **すべての journal model** で evidence を要求する。

ある一つの journal model で Overlap が失敗しても、3、4 の存在命題が偽とは言えない。
`completion_iff` の support-preserving extension と、`common_iff` の自由な存在モデルを混同してはならない。
また、1 と2の独立の存在証人を、そのまま共通の証人として使うことはできない。

## 厳密な次の補題型（未証明）

次の型は調査対象の十分条件であり、新しい公理・仮定として composition に追加していない。
既存 `CurrentHeadEquations217` と同じ名前空間 imports / open と implicit variables を置く。

```lean
-- Proposed statement only; no proof is claimed.
(checked : Checked registry)
(source : GeneralNominalSourceFormation.InitialSource registry context root)
(point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
(ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
(coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
(path : B4Target.Steps (Step registry root) (initial context root) state)
(candidate : Plan roles)
(frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
(sharing : ∃ model, Models state model ∧
  GeneralDictionaryCountedProjection216.Agreement candidate model) :
∃ model, Models state model ∧
  GeneralDictionaryCountedProjection216.Agreement candidate model ∧
  GeneralDictionaryMixedMerge216.Overlap
    candidate.packet.context.state candidate.packet.registry
    candidate.packet.site.occurrence.identity candidate.packet.declaration
    candidate.packet.bindings
    (GeneralDictionaryCurrentCompletion216.support state candidate) model
```

これは全 reachable Frame についての強い形であり、証明できるとは断言しない。
全域形が成立しなければ、実際の EvidenceNode が持つ selected、focus の生成到達性、focus/children の Stable を追加した狭い形を調べる。
`Frame` は already Prepared を含むので、別途 `∃ HeadModels` を仮定する必要はない。
ただし候補 bounds を `frame.located` と Prepared の located から一致させる必要がある。

### 既存の橋

- `HeadSharing220.holds_iff_agreement` と `DefaultRevisit214.frame_finished` により、Feasible で得た同じ candidate に上記 sharing 前提を移せる。
- `CurrentCompletion216.common_iff` により、上記結論は `∃ model, Models state model ∧ Agreement candidate model ∧ HeadModels ... model` と同値。
- `CurrentHeadEquations217.common_head` / `common_iff` により、上記結論から journal・raw head・HeadEquations の共通モデルを得る。
- `CurrentBranch215.branch_merges` は **その HeadModels witness 自身** が current merges を満たすことを与える。別の journal witness に merges を移す定理ではない。
- `MergeCriterion216.necessary` / `completion_iff` は binding endpoints を保護した有限 support で Overlap の必要十分性を与える。
- `OwnedMerges216.transfer` は旧新 extrema の Equivalent が別途分かる場合に旧 merges を再利用する。`point_transfer` は両側が同じ値の point の場合。いずれも一般の reobserve で extrema が不変だとは主張していない。

## 存在から全モデルへの operational な橋

単に EvidenceNode が全モデル命題であることは反例ではない。
`DefaultKernel208.Stable registry state focus` と、その focus の `Installable registry state effect` があれば、
`¬ Committed state effect.plan` は `.install effect enabled ...` という At を作り Stable に矛盾する。
従って Committed が得られ、packet/schema は全 journal model で成立する。

このルートでは、上の共通モデルに加えて Installable の残りの条件
（SafeKnown、CacheSound、materialized、ChoiceCompatible、cycle positions、alternatives、effect の Ready/outputs 等）を満たす必要がある。
common_iff だけで完成した EvidenceNode を得たとは言えない。
`TotalEvidence206.certificate_of_semantics` は frame・children・packet・Ready・ClassEffects から証明書を作る既存の最終橋である。

## cycle219 の stale aggregate 案をそのまま反例にできない理由

GroundCopy218 を「parent を repeated name に変更、actual の二成分をともに int に変更、loose descriptor で install、point descriptor に reobserve」と変える単純案を考える。
初回 repeated capture は purpose0/purpose1 aggregate を loose extrema に固定する merges を raw ordinary に追加する。
`Allocation.propagate_models` は旧 state と新 merges の両方を要求し、install の current はその private context を引き継ぐ。
新しい candidate の HeadModels も現 current の raw ordinary を満たす。

従って旧 low/high と新 point の extrema が固定値として非同値なら、新 HeadModels は両方の等式を同時に要求して不可能となる。
この場合 sharing が真でも Prepared/Survivor が先に失われ、V8 selected EvidenceNode の反例にはならない。
この推論は定義と `branch_merges` による候補の除外理由の解析であり、変更 fixture 全体を Lean で構築・検証した主張ではない。

## 次の実験の合格条件

新 fixture を書く前に、同一 current candidate について次の二つを具体的証人で両立させる。

- journal Models + actual sharing の witness。
- current HeadModels の raw witness（旧 merges も満たす）。

その上で全 journal + sharing witness に対する Overlap 不成立を示さなければ、common_iff による obstruction にならない。
固定 extrema の単純な食い違いだけでは二つ目で失敗する。
反例に進むには、raw witness と journal witness の分離が実際に存在する箇所を特定する必要がある。
さらに reachable・selected・stable・child evidence と最終 evidence 不成立の証明が必要。
現時点でその最小 closed fixture は見つかっていない。未証明として止める。

## Cycle220 内の有限断片

一般 amalgamation は未証明のまま、既存 `MergeCompletion216.Separate` を満たす断片を新規 `HeadSharingAmalgamation220` で実証する。
active purpose0/purpose1 aggregate が保護 support と交わらなければ Overlap の前件は空で、すべてのモデルで成立する。
特に全 inputName の occurrences が singleton なら active list は空であり、support に依存せず Separate が成立する。
この条件から fixed-frame の sharing feasible witness を共通 head witness に昇格する。
すべての reachable Frame でこの条件が成立するとは主張せず、EvidenceNode 全体の証明とも扱わない。

検証結果: `lake build Yulang.GeneralDictionaryHeadSharingAmalgamation220 --wfail` は PASS（1342 jobs）。
`common_iff_of_separate` と `common_iff_of_singletons` は fixed-frame の共通 head 存在と sharing witness 存在の同値。
`feasible_common_of_separate` は全 eligible Frame の Separate を明示前提として、Feasible が選ぶ Frame と共通 head witness を返す。
これらは別モデルの証人を無条件に同一視せず、既存の finite patch/common_iff を経由する証明である。

## 次のfreshness一般化の境界

FreshTerminal（同invocation/keyのHistoricalInvocationなし）から、今回の
Separate断片へ進むにはp0/p1 aggregate slotのsupport非出現が必要。
既存Default214FullFreshness.fresh_support_separateとActualJournalのreadbackは
purpose8のactual binderに特化している。RawSeparation213.current_separateは
purpose≥7を前提とするため、これらをp0/p1にそのまま適用できない。
AllocationSupport.private_sourcesはcurrent raw supportを「旧support＋当該invocationの
全reserved」に包むが、全宣言keyの予約を含む粗い上界であり、未実行のkeyの
不在をこの包含からは得られない。次はmerges_sourcesの生成元をより細かく追い、
raw ordinary中の当該p0/p1出現から同keyの実際のinstall履歴を復元する補題が必要。
このtrace provenance補題は今回未証明。freshだから自動的にSeparateと主張しない。
