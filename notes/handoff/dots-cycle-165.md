# dots cycle 165 — Shared の現在文脈の辞書と captured-input の実行

## 入力・時間・分担

開始 2026-11-13 12:30 UTC。今回の予定起動 12:27:19 UTC に対する最終期限は 13:22:19 UTC。ユーザー指定の55分上限を常設文書の長時間実行より優先する。終了時刻と最終公開照合は末尾の台帳に記録する。

`integration/m1-final` を取得し直し、`f22c75e5779bf23cc3116e5201119d55bb1ad3a1` の standing-orders/inbox、AGENTS/workflow/concurrency/testing、前回164の報告・completed心拍を読み直した。ACTIVE、前回の書き込みなしを確認。前回公開 `37a4975de630e514b4197b16ad98ad43dcb1f650` を保持し、最新監督役の変更を取り込んだ。担当は Evidence、意味論の定義は変更していない。書き込み先は `work/dots-main` のみ。

## 主結果（量化・前提・証明の側）

### 1. 点入力の identity leaf は、実際の refresh 後も現在文脈で証拠を持つ

`GeneralDictionarySharedSourceRetention.identity_current_evidence`：任意の roles/registry/root、実際の `Shared.SourceFormed` 状態、そこに記録された任意の packet、その宣言が head=`[var 0]`、whereなし、関連出力の右辺が全てvar0であり、その需要が同一sourceの点入力であるとき、**任意の現在の journal model** に対し、現在の文脈で、そのkeyと空の子辞書列の `Evidence` を構成する。現在の場所・metadata・source slot・ordinary Extension は仮定ではなく、実際のShared履歴から導いた。

補助：`step_retains` は全ての実際のShared stepについて旧type-sourceを保持するslotの存在を示す。refreshは証明書の埋め込みを使い、記録packetには履歴帰納で適用する。`formed_metadata` はrefresh/reobserveを含む全履歴でmetadataを保つ。`rebase_outputs` は旧出力方程式を同一sourceの現在slotに移す。この断片ではhead inspection自体が変数だけなので、descriptorの不変性を要求しない。これは健全性の橋渡しで、候補の一意性や現在selectedの証明ではない。

`GeneralDictionaryIdentityRefreshExample`：監督役のchecked identity例を実際にinstallした後、出力1をunknownからint既知へ変える**実際のShared refresh**を構成した。`refreshed_models` は全assignmentについて前後Modelsのiff、`nonvacuous_refreshed_evidence` は具体model.int付き。`not_ordinary_extension` はこの更新を旧ordinary-extension補題では扱えないことを示す。上記の一般補題を本当に新しい文脈で使う、非空の正例である。

### 2. captured-input 親の実際の install と fresh endpoint refresh

`GeneralDictionarySharedCapturedModel.branch_models` は前回164のchecked captured-input案について、元の0/1/2と新しいlo/hi/targetを区別した具体的有限modelで、private制約・投影・**全named-output materialization**を証明する。目的のBranchModelsを仮定していない。

`GeneralDictionarySharedCapturedInstallation.reached_parent` は実際のShared初期sourceから親をinstallし、モデルが存在し、producer/consumerが双方Generatedとなることを示す。一方、その直後は**双方ともraw RootPending**。`producer_shape` と `output_capture_equivalent` は全journal modelに対する意味的方程式であり、Knownへの読み替えはしない。

`GeneralDictionarySharedCapturedRefresh.endpoint_equation` は全journal modelについてlo/hiが `list(source2)` と等価であることを、親の実際のschema testとvariable useから導く。有限modelを仮定しない。この方程式により、source slotを3から5へ増やすinjectiveなrefinementと全Modelsを保つRefresh証明書を構成した。`shared_prefix` は初期source→親install→refreshの実際の二段階。`producer_ready` はraw RootPendingの否定、**producerのInstallableではない**。consumerは依然pending。descriptor-only `Revision` ではproducerのpendingを解消できないことも一般のrevisionについて証明した。

### 3. ordinaryな履歴の有限記録木

`GeneralDictionarySharedOrdinaryHistory`：任意の実際のShared履歴で、各stepが厳密なordinary Extensionでもある断片について、全記録packetから現在へのExtensionを導く。任意の有限 `RecordedTree` と現在modelから現在Evidenceを得る。実際のguarded installはこの履歴条件を自動で保つ。木やmodelの存在を仮定なしに作ったとは言わない。一般refreshを扱う主張ではない。

## Yulang2との照合

監査branch `work/dots-audit` を再取得（`55574b6052ef1534fd0fc36d6d3617ebede59a0e`）。role-boundariesのMORE-003/004とx-oracleの親子需要の結果、保存された6月role-system/invariant-sandwich文書を読んだ。旧実装の宣言whereとbody由来需要が異なる点を新specへ逆輸入しない。点入力の制限を一般区間の代表選択へ広げず、associated出力と通常入力を区別する。今回のShared観測台帳に対応する新しいYulang2実機試験は実行していない。GitHub上の別repoのREADME照会は404であり、実機アクセス成功とは扱っていない。

## 13境界項目とV5

| 項目 | 今回の状態 |
|---|---|
| Checked | 定義不変。既存checked宣言を使用 |
| Models | 定義不変。具体モデルと実際のrefreshのiffを追加 |
| Step | 定義不変。実際のShared prefixを追加 |
| Stable | 定義不変。一般の存在・完了は未証明 |
| Generated | 定義不変。実際の親installから両子を確認 |
| RootPending | 定義不変。観測前後の正負を区別 |
| RootK2 | 定義不変 |
| CandidateK2 | 定義不変 |
| InspectionPending | 定義不変。全Shared境界統合は未完 |
| Survivor | 定義不変。具体親の候補証明のみ |
| Evidence | 現在文脈の一般点identity橋と実例を追加 |
| Reorders | 定義不変 |
| DictionaryEquivalent | 定義不変 |

V5は継承した **8/14、未完** のまま。一般のsource-to-Evidence、非終端子辞書の存在、全候補の独立性、完全性・主型性の一般定理を完成扱いしない。

## 検証・公開（途中台帳）

- 開始心拍 `a48d9d3c23f7dfa95bd8929c2bf5ded1d1864710`。
- 第1途中公開 `b0ca837ee149fcf47fad4921813a4bc6d9f57a96`。最新integrationを第二親に含め、祖先関係を検証。
- 第2途中公開 `5a169d5589edce69ca33a47b5824c1dc196c45d3`。凍結したlocal `ce49a75c9` と、心拍以外の全treeが一致。
- 焦点を絞ったlake targetのみ。依存job総数はcacheを含むため、全件再buildの意味ではない。全repo build・全repo Auditは実行していない。
- 最初のfocused試験で未使用simp引数の警告を3件見つけ、新規ファイルだけ修正。`--wfail`で再検証成功。
- diff-only gateで、前回164から継承した既存auditが最新integrationと異なることを検出。拡張版を新しい `Cycle165Inherited164DependencyGate` に丸ごと保存し、既存164のgateは監督役版へ戻した。coverage削除ではない。再試験はPASS、audit-only依存検査2件をREVIEWとして明記する。
- 最終の凍結source、全新規module再コンパイル、全Cycle165 audit、依存gate、公開後照合結果は末尾へ追記する。

## 制限と次の作業

1. captured producerのraw readinessだけでShared DecisionGuard/Installableを主張しない。実際の信頼readback・説明付き観測を接続して次のinstallへ進む。
2. 点identityのEvidenceは現在の一意な候補という意味ではない。refresh後に競合する候補を排除する一般定理はない。
3. 非終端packetの有限記録木を、実際の子解決から構成する橋を続ける。一般V5の未証明項目を前提で隠さない。

使用量枠：不明。自動化の設定変更・停止は行っていない。

### 第2公開の独立した再実行

公開commit `5a169d5589edce69ca33a47b5824c1dc196c45d3` を別のdetached checkoutへ取得し、新しい出力用libraryで9新規moduleを全て `lean --trust=0` から再コンパイルした。全Cycle165 auditも成功。依存gateは157個のpublic/private/generated宣言を検査し、標準3公理のみ。全文ログは `notes/verification/2026-11-13-cycle165-first-public-replay.txt`。この時点の公開はまだidentity refresh/captured fresh-slot refreshより前であり、後続部分の検証と混同しない。
