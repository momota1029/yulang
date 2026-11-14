# Cycle199 — I33 の exact prior EvidenceNode は成立しない

**新たに閉じた普遍的 bridge field: 0。指定された EvidenceNode: 1 本を、合法な具体的 roles で反証。** V6 の selected-only 健全性と全体の Statement は未解決で、この反例はそれらを否定しない。従来の一般境界の性質を変更していない。

開始: 2026-11-14T22:23:40Z。上限: 23:18:40Z。最新のユーザー指示の「検証・公開・報告まで55分」を文書の長時間実行指示より優先した。終了時刻は completed heartbeat に記録する。

## 復元・並行実行・対象

integration/m1-final を取得し直し、`90dd3be21d2aa3b362436d8431cb193b66bcc5bd` の standing orders と inbox I33 ACTIVE を再読。STOP はない。前cycle198の completed heartbeat と報告を確認し、前の writer/process が動いていないことを確認してから開始した。既存 checkout/cache を再利用。proof writer は1人、凍結した commit を別に独立検証した。公開先は work/dots-main のみ。22:53の再照会でも integration の先頭は不変だった。

正確な担当型は

```lean
B4SkeletonV5.EvidenceNode
  (B4TargetV6.prior (GeneralNominalCenteredHeadMatStepBoundary.boundary roles))
```

WF の旧境界や予定される Alloc 境界へ置き換えていない。`B4SkeletonV5.EvidenceNode` の定義と `B4TargetV6.prior` の alias、I33 の参照ノートを読み比べた。この型には OutputConflict の否定がない。

## 主結果: exact type の閉じた否定

`GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode` は、具体的な合法 roles に対し、上記の型の否定を追加仮定なしで証明する。任意の roles についての否定を主張するのではない。任意の roles でこの field を閉じる計画には、この1例で十分な反例となる。

具体例:

- 単一の検査済み宣言37。head は Int、where の子は0個。
- 関連出力0の定義は nominal0[Int]。
- 実際の root の入力 source1 は Int、要求された名前つき出力の target source2 もソース制約で Int。
- head のみの照合では一意。関連出力は Int と nominal0[Int] の衝突になる。

全前提と否定の証拠:

| exact field の要件 | 閉じた証拠 |
|---|---|
| Checked / コンストラクタ coverage / 実際の Initial | PriorConflictSource199.checked, coverage, initial_source |
| Reachable | 同 reachable: actual Initial から0-step |
| 与えたモデルが actual Mat journal Models を満たす | 同 source_model, inhabited。source1/2 は実際に Int |
| 実際の Stable | PriorConflict199.stable。全 administrative / refresh / install / merge を処理 |
| SafeKnown / head-Unique | PriorConflictLocal199.safe, unique |
| 親が root または生成済み | root 自身 |
| 全ての子の Stable と All₂ child Evidence | 子リスト=[]、辞書リスト=[]。terminal source の正当な空リスト |
| leaf Evidence がない | PriorConflict199.no_instance, no_evidence |

`no_packet` は全 assignment で actual total packet Holds が不可能なことを示す。したがって全候補 effect の `no_install` が成り立つ。これはモデルが空だからではない。初期 journal は明示モデルを持つ。`frame_plan` により、恣意的な1 plan だけでなく全ての現在の Frame を排除する。Stable も単なる halted の仮定ではなく actual Step の場合分けで示した。

`output_conflict` と `rejected` は、同じ状態を actual V6 Local が正しく拒否することを示す。**V6 selected の反例ではない。言語意味論の矛盾でもない。** prior の証明インターフェースが拒否ケースにも辞書を要求する、という不一致である。

独立 audit `Cycle199ExactPrior.lean` は閉じた否定を完全修飾した指定型に直接代入し、さらに Checked・Initial・Reachable・明示 Models・Stable・SafeKnown・head-Unique・空 All₂・Evidence 不在を1つの witness にまとめて再検査した。

## 併せて得た本物の部分結果

1. `MatGuardObstruction199` / `MatGuardWitness199`: 既存の covered multi-tag 例から、actual reachable Mat state と selected を構成し、同じ assignment で journal Models と全 total packet Holds が成立しても、旧 recursive Instance は全 key/children について存在しないと示す。`no_total_instance_conversion` は無制限な Holds→Instance 変換を反証する。packet の存在自体は既存 `MatStepRows.source_packet_extension` を再利用し、新しい成果とは数えない。
2. `MatGuardTrace199.install_step`, `not_stable`, `no_child_evidence`: その元の join 例は actual install が可能なので非安定であり、子 role1 の実装もない。したがってこの例から exact EvidenceNode の否定を推論しない。主結果の terminal output-conflict 例とは別物。
3. `MatEmptyLeaf199.evidence_of_frame_total`: 任意の Plan、actual Mat state、assignment について、現在の Frame、total Holds、requirements=[]、root の名前つき出力=[] があれば exact Mat leaf Evidence。旧 packet Models / BranchModels / 最終 Evidence は仮定していない。
4. `MatVariableNode199.evidence_of_frame_total`: 任意の現在の Frame と同じ assignment の total Holds、VariableClauses、root出力=[]、全canonical children の All₂ Evidence から exact node Evidence。VariableClauses は子の引数が正規化後に変数で、子の名前つき出力がないという構文制限。順序・重複を保持する。
5. 同 `evidence_of_recorded`: current journal Models と plan membership から同じ assignment の Holds を得る。ただし現在の Frame（packet context=current context）も必要。任意の古い記録を refresh/growing context 越しに回収する定理ではない。

新規 proof modules は上記5個と PriorConflictSource199 / PriorConflictLocal199 / PriorConflict199 の合計8個。既存の意味論、Evidence、Step、Stable、Local、allocator、spec、plan、lakefile は変更していない。root import と aggregate audit の公開済み追記は append-only。

## 検証

完全な実行出力と終了コードは `notes/verification/cycle199/`。全体ビルド・全体 Audit は行っていない。

- 公開commit `1cc141c090e26e7857d2b59e9cea851ab5324d74` の8 module focused `lake build --wfail`: PASS, 1019 jobs, exit0。
- 8個の個別 public audit を独立に `lake env lean --trust=0 -DwarningAsError=true` で実行: 全てexit0 (`all-eight-independent.txt`)。
- `Cycle199CompleteGate.lean`: 全8 module の117宣言を再帰依存まで検査、PASS。許可した公理は propext / Classical.choice / Quot.sound のみ。
- exact counterexample 3 module の gate: 67宣言、PASS。同じ3公理のみ。
- `Cycle199ExactPrior.lean`: 完全修飾した指定型と explicit premise bundle、PASS。
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: PASS (diff checks only, NO build), 8 REVIEW markers。全文 `verify-final.txt`。既存audit metaprogrammingと今回の環境走査gateは宣言を読み公理を集めるだけで、証明に公理を追加しない。人手review項目を消したと主張しない。
- CI、runtime、Yulang2 oracle の新しい実行はない。過去の独立 audit branch の観察は現モデルの証明に代用していない。

訂正した実行失敗も残した: 最初の補助gateのcount型注釈不足、実行bitのないscriptを直接呼んだ後のbash再実行、writer編集中の中間verifierのclean-tree失敗、補助witness auditでの定義展開の明示不足。各々訂正後に独立検証を通した。新しいproof本体の未解決エラーとして隠していない。ログがgitignoreの対象だったため、公開ログは.txt名で保存した。

## 公開と制限

- 第1 checkpoint: `8f73584d8716d34cc996905969fad40dff9e841e`
- 第2 checkpoint: `c71862845a410ccab2a2cb1b23982f2f7f28209a`
- 主反例の checkpoint: `1cc141c090e26e7857d2b59e9cea851ab5324d74`

それぞれ GitHub app の immutable objects と expected-head 非force更新で公開し、取得し直してtree比較した。第1/2はheartbeatのみ相違。主反例はheartbeatと下記の意図したaggregate audit差分のみ。検証済みソースと個別auditは一致する。

巨大な `lean/Audit.lean` の最後の10行（主反例用print登録）を含むblob作成が承認で止まり、この追加だけは未公開。承認を迂回・再試行していない。該当ローカルcommit `9b9665f8c` は保持し、公開側は以前のaggregate auditをそのまま維持した。新しいproof3 moduleと個別audit3個は独立した別ファイルとして公開済みである。保留中のaggregate更新を成功と報告しない。

## 境界の13項目

| 項目 | 今回確認した状態 |
|---|---|
| Checked | 一般nominal定義あり、今回の具体registryで証明 |
| Models | actual total Mat journalの一般定義あり、明示モデルあり |
| RootPending | head入力に対する一般定義あり |
| RootK2 | raw＋actual-position cycleの一般定義あり |
| CandidateK2 | 同上、Frame上の検査に対する定義あり |
| InspectionPending | head検査＋administrative readyの一般定義あり |
| Survivor | head-onlyの一般定義あり |
| Reorders | 一般定義あり、今回は変更なし |
| DictionaryEquivalent | 一般定義あり、今回は変更なし |
| Step | actual Mat一般定義あり、今回は変更なし |
| Stable | actual Stepの一般定義あり、反例で全ケースを証明 |
| Generated | 一般定義あり、反例はroot自体 |
| Evidence | 旧recursive source certificateの一般定義あり。指定prior-node普遍則は今回反証 |

V6にはさらに Initial / OutputConflict がある。一般定義があることと全言語の健全性・完全性を証明したことを混同しない。

## 次の正確な課題

1. `notes/questions/2026-11-14-mat-prior-output-conflict-evidence.md` に、現prior型の閉鎖を遅延する案を先頭に記録。監督役にV6 selected-only等の正確な代替型を指定してもらう。勝手に型を弱めたり意味論を変えていない。
2. conflict除外は今回の反例を除くだけ。total materialization と旧RequestReady/BranchModels の対応、現在のFrame、履歴context transportは別途証明が必要。
3. 正式な担当型の変更はinbox指定を待つ。追加の独立検査では、同じterminal fixtureのregistryがAllocEncodingで変わらないことと、AllocBoundaryの同じprior型の否定も検証した（下記）。allocation修正だけでこの契約問題が解消するとは扱えない。

利用量枠: 不明。

## 最終公開 tree の再検査

Audit/log checkpoint `76eba75a7a571e49bf891a0ce5b4ab664e660120` を取得し直し、検証済みローカルtreeとの差分がheartbeatだけであることを確認した。その公開commit自体をcheckoutし、strict complete gate（117宣言）と exact-type＋explicit witness gate（67宣言）を再実行して双方exit0を確認。proof writer、Lean build、git fetchの残存processはない。

この報告を含む成果の公開差分は42ファイル（heartbeatを除く）。heartbeatは別途更新。未公開なのは上記aggregate Auditの最後の登録10行だけで、意味論・proof module・個別auditの欠落はない。


## 追加の successor 契約検査（担当型の置換ではない）

`lean/Audit/Cycle199AllocPriorCheck.lean` の `encoded_registry_eq` は、この具体的terminal registryがAllocEncodingでそのままであることをrflで証明する（whereもoutput bindersもない）。`not_prior_evidenceNode` は同じ明示witnessをAllocBoundaryのexact prior型へ直接適用して、その否定を証明する。新しい意味論・targetは定義していない。既存AllocBoundaryのfocused buildはPASS1073jobs、strict auditはexit0、公理は標準3個のみ。初回は未生成の.oleanでimportに失敗し、focused build後に再検査した。出力全文は `alloc-prior-check.txt`。これは主担当Matの結果に加えた検査で、Allocの全体Statementやselected-only則を否定しない。
