# Cycle241 — I47: owner-local rebase の設計と検証済み断片

開始2026-11-17T13:30:30Z。研究上限14:15:30、公開照合の上限14:25:30 UTC。

## 判断と対象

integration1c675172のstanding-ordersとI46/I47を再読。I47は240反証を承認し、
rebaseと意味キーを停止性込みで比較して一案を選ぶ許可。Lean着手前に比較設計を保存し、
A（owner別の私有定義の置換）を選んだ。言語の採否・specは変更していない。

私有名が新鮮であることと、sourceに影響しないことは別。240では名がdescriptorへ逃げる。
そのため、sourceへの射影、全live consumerの保持、有限の進捗を別々に扱った。
I45は元source descriptorの保護として残す。旧239/240の偽目標を再開したわけではない。

統合競合は監督版を優先し、237のコメント修正と最新inboxを取り込み、240成果を保持した。
凍結Audit.lean/README・既存proofを独自に変更していない。

## 結果（全境界の完成ではない）

最終20新モジュール。新しい一般source境界のAcc/EvidenceNodeは未完成。
主張と前提の対応は各Lean定理の型を正本とし、主な内容は次のとおり。

- Store/Names:任意owner表の単一置換、他owner・public atoms・owner一覧の保持。
  固定有限owner/変数集合に対するstable cell名の有限列挙。有限owner集合自体の生成は別。
- Progress/Machine:任意有限fact/owner集合について、真の新factかdirty1件除去の実2規則。
  rank=(未取得fact数)*(owner数+1)+dirty数が毎回減り、表を含む機械の全状態Acc。
  任意blockを受け入れる構造計算なので、これだけで言語意味の保存とは言わない。
- Definitions/Projection/Owner:実merge式を同名cellで再評価。非escape、外部端点支持、
  actual center保護、非空captureを明示し、public/checks/他ownerとactual Fitsを保持する
  存在量化source射影を証明。同一assignmentの旧journal包含ではない。
- 230Private/Service:実230のcurrent merge式を使用。元raw source・actual W・旧cross/
  selfChecksを保ってO→Wへ再評価し、旧mergeとの同時保持が矛盾することを検証。
  有限work機械の実1serviceと停止まで構成。全source境界の経路や辞書定理ではない。
- Inline/InlineModels/InlineSyntax:有限同時patchに一致するordinary consumer代入。
  旧定義方程式を満たす任意モデルで型Equivalentとrow一致から意味保存。
  escaped equalityを削除せずsource式へ書き換える。循環解の生成・全支持消去ではない。
- ChildProduction:実versioned Frame/Holds、親actualラベル、Coverageから、子のactualラベル・
  厳密質量減少・1段のdepth予算・identity ancestryを構成。全traceの有限閉包は未完。
- BackExtension/OwnerBack:独立した旧新端点の区間精密化と非escapeから、保護pool値・
  他owner・checks・actual Fitsを保つ旧private/owner表モデルの存在を構成。
- LiveLabels/ProtectedLive/OwnerLive:全既存live centerのpool包含を別に要求する。
  具体的な新旧Store.ModelsとCapturedFitsにOwnerBackを適用し、ラベル・depth+mass予算を保存。
  原sourceや現在のdeclarationのactualだけを守ることでは代用しない。
- Noop/Escape:無制約置換には自己ループやsource制約の消失があることを小例で検証。
  選択した条件付き設計全体の反証とは扱わない。

199/202/204/206/218/239/240の新一般境界への回帰輸送は未完。
既存の定理を残したことを、新しい境界で全回帰が成立したこととは呼ばない。

## 中断・復旧

13:55頃に共有実行環境が切断・置換され、/tmpの旧worktreeと未公開ソースが消失。
中間公開8dc6c7ad（9モジュール190定義）と設計はGitHubで保全されていた。
永続領域の同版Lean4.35と220キャッシュを利用し、不足依存71本を焦点再ビルド。
未公開分を会話中の作成内容と保持された型・証明方針から再構成して再検証した。
元ソースとのbyte同一性は保証しない。元Private51宣言の逐語再現でなく必要主張の縮約復元。
以前の監査を再生成ファイルへ転用していない。
1c86e50c（14本228定義）、15d0b4c6（19本294定義）へ復旧分を段階公開・取得照合した。
新たな230Back具体回帰は未実装のまま。一般BackExtensionと混同しない。

## 検証

- 各追加moduleを依存順で `lake env lean --trust=0 -DwarningAsError=true`、exit0。
- `Audit/Cycle241All.lean`で全20moduleの生成宣言も含め推移公理を監査。
  許可はpropext/Classical.choice/Quot.soundのみ。最終個数は最終ログ参照。
- 完全な焦点検証ログ: `notes/verification/cycle241/final20-build-audit.txt`。
  初回・復旧・独立監査のログも同ディレクトリ。
- I46の追加Lean禁止語scanは0件。source-manifest.jsonに最終20ソースのSHA256。
- 凍結2ファイルと監督237コメント版をintegration1c675172と照合して差分0。
- 全体lake build / verify-lean.shは監督側専有のため未実施。CI成功は主張しない。
- 使用量の残枠は不明。

## 次回の優先事項（I47を継続可能）

1. 原sourceから有限owner genealogyを全traceへ接続し、endpoint・promotion・row/output・
   観測factまで有限閉包を生成する。owner有限だけで足りるとしない。
2. 実到達状態の全live consumerを追跡し、各rebaseの非escape/精密化/全center保護と
   output・子evidence保存を生成する。今回の条件付き断片を一般producerへ接続する。
3. 必要な全実操作をnewfact/dirty-drainに写し、仕事終了から本来のStable/Local/Evidenceを導く。

新しい意味論の判断待ちや全案反証は発生していない。I47の範囲で次回を継続できる。
ただし上のproducerなしに一般Accや全回帰完成を主張しない。

最終焦点監査結果:20 modules /298 constants、全direct compileと推移公理監査exit0。
