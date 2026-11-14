# Cycle 178: 定理の入口と残っている前提

対象は I30 の中心つき ground 境界 G。以下の `model` は結論の Evidence
と同じ任意の現在モデルである。存在する別モデルへ置き換えない。

## 1. merge の正確な意味

`GeneralNominalMergeResidual178.merges_iff_extrema` は任意の state、registry、
invocation、declaration、bindings、assignment に対し、実際に生成された
merge 制約を満たすことと CaptureExtrema が同値だと示す。宣言された各入力名に
ついて、その出現が singleton でない場合、割り当てた lower/upper の値が
全出現の lower/upper extrema と同値である。0回の出現も除外していない。
`propagate_iff_extrema` は source Models、cross compatibility、同じ extrema
条件の連言を、propagate 後の Models と同値にする。

## 2. 有限 nominal pair

`GeneralDictionaryNominalPair178.branch_models_iff_residual` は、異なる二つの
外側 slot、同じ nominal 名、任意の有限個の相異なる type binder 名という
shape、requirements=[] と demand outputs=[] の下で、任意の assignment の
BranchModels を source Models・外側 endpoint order・実際の fresh merges
の連言に分解する。各 parameter 自体は点でなくてもよい。
`GeneralDictionaryNominalPairExtrema178.branch_models_iff_extrema` は二回出現を
実際の有限 union-lower / intersection-upper 等式として表す。

`GeneralDictionaryNominalPairDiscovery178.candidate_holds_iff_merges` は actual
Finished inspection から descriptor と parameter を取り出す。query/located
shape を仮定するが、descriptor witness を別途与える必要はない。

## 3. 現在の Candidate と無条件断片

`GeneralDictionaryCenteredNominal178.candidate_holds_iff_merges` などは、Candidate
と現在 Models から source/order を導出し、同じモデルでの Holds の残りを
merges として記述する。merges を Candidate の存在量化から導出したわけではない。

`GeneralDictionaryCenteredNominalPoint178.point_holds` / `point_evidence` は、
相異なる有限 binder、単一 nominal query、同一外側 slot、terminal/no-output
という明示した断片で、任意の現在 Models から Holds/Evidence を直接作る。
`nullary_holds` / `nullary_evidence` は binder を持たない nominal head なら
異なる外側 slot も扱う。上記の構文・位置・現在 Models の前提は残る。

`GeneralDictionaryCenteredNullary178.evidence_at_G` は、G の Reachable、
root または Generated、Local.selected、現在 Models と子 Evidence に対し、
当該 role の全 visible 宣言が nullary nominal / inputNames=[] / associated=[] /
requirements=[] という条件なら、現在モデルの node Evidence を作る。
associated=[] から demand outputs=[] を導く。Stable はこの狭い断片には不要。
これは G の実際の consumer だが、任意宣言を量化する EvidenceNode ではない。

## 4. 繰返し binder 名

`GeneralDictionaryNominalPairShared178.branch_models_iff_shared_residual` は
SharedShape に distinctness を要求しない。source Models・外側 endpoint order
に加え、同名 lower parameter の Coherent と実際の fresh merges を要求する。
`GeneralDictionaryCenteredSharedNominal178.candidate_holds_iff_residual` は
Candidate + 現在 Models の下で、Holds iff (Coherent and merges) を示す。
名前の繰返しを許すことは、coherence が自動的に成り立つという主張ではない。

## 5. 例と Stable の切り分け

`GeneralDictionaryCenteredNominalExample178.evidence_not_from_candidate_alone`
は、旧 source 値が一致する二つの assignment で fresh lower を変えると、
Candidate と現在 Models はあっても一方は Evidence を持たない例を示す。
この例は nonpoint root で G の Reachable や Stable を主張しない。
`GeneralDictionaryNominalPairJoint178.plan_holds` は actual binder center も
設定した第三の assignment で full centered Holds を作る。
`stable_not_selected` はこの state で Stable と selected が同時に成り立たない
ことを示す。したがって上の例は G.EvidenceNode の反例ではない。

## 6. 初期 source support と未完了箇所

`GeneralDictionaryNominalPairSourceSupport178.reads_exact` と `value_guard` は
有限 pair shape の検査が外側 source を読むことを示す。
`GeneralDictionaryNominalPairInitial178.raw_joint` / `raw_installable` は初期
singleton registry の Candidate と selected から raw 側を構成する。
`installable_of_joint` / `stable_instance_of_joint` はさらに明示した共通 centered
model の存在を必要とする。この存在の一般的 producer は未証明。
この nonpoint initial shape は G の point-root Initial に直接は合わない。

## 検証の読み方

16 module の全327宣言（private/generated含む）を trust=0 の別監査で検査。
公開の155個の型は tools/TypesCycle178.lean と検証 types.log に記録。
型の quantifier の最終的な根拠はソースとその出力である。
7 consumer から257/327、restricted G consumer から50/327宣言が到達可能。
既存の unrestricted composition からは0/327。これは field 未完成を明示する
依存関係の検査で、数学的な無関係性や完成度の百分率ではない。

## 7. original root の有限 linear nominal を実際の G へ接続

`GeneralDictionaryCenteredRootNominal178.root_point` は、G.Reachable の初期状態
の前提から original root の全引数が点であることを取り出す。`located_point`
は actual lookup と source injectivity により、singleton bounds の二端が
同じ slot だと導く。到達状態の全 slot が点だとは主張していない。
`reachable_root_point_bounds` がこの結論を現在の Candidate に接続する。

`point_linear_evidence_at_G_root` は任意 roles/registry/original root/current
state/key/children/model/dictionaries について、G.Reachable、root selected、
現在 Models、子 Evidence と role-local LinearTerminalAt を仮定して、同じ
モデルで root の node Evidence を作る。LinearTerminalAt は全 visibleな
同role宣言が、有限 injective type binder名の単一nominal queryで、inputNames
が一致し、associated/requirementsが空であること。Stable、Installable、
別の joint model の存在は要求しない。generated child はこの定理の対象外。
これも一般 EvidenceNode field の完成ではない。
