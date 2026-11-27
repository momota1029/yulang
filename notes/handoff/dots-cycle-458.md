この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C458 引継ぎ

- 実開始 2026-11-27 05:35:04 UTC。通常終了下限 06:25:04 UTC。完了と writer 解放は同コミットの heartbeat。
- I-86 の G04 だけ。開始時の権威 `integration/m1-final@3675a70f43b31066f6c00b7f5cfd5efb0735a683` / Lean `2095eb6a97d0f0422c31a073fd2724f53defe879` で C457 の固定 Lean と一致。最終照合 `integration/m1-final@3675a70f43b31066f6c00b7f5cfd5efb0735a683` / Lean `2095eb6a97d0f0422c31a073fd2724f53defe879`。
- [作業ブランチの固定成果](https://github.com/momota1029/yulang/commit/95b9cdca885a86ad1894fab90d70f9c7368412ac) / Lean `3103301de9296b4a356e41487ac6c25451d9d36d`。[I-86 根拠と設計](../design/dots-cycle-458-i86-inline-native-authority.md)、[四種の照合と境界](../design/dots-cycle-458-i86-structural-overlay.md)。

## G04 の実証

- **実際に訪れた field だけを報告する。** 既存 raw row・raw Alias・元の正規化候補の該当 field / tag / operand を照合する。開ける途中 site ごとに、元の inline parent と選ばれた payload の native syntax、同じ issuer、両方の元 route、および raw child から payload の物理 slot への旧 raw Alias を要求する。route やモデル内の同値だけで raw 接続を作らない。record は最初に見える field、pair は選んだ成分、nominal は実宣言 covariant の単項 point・元 ordinal 0。nominal の比較は同一の元 point と自身（両 context）で、異なる・非 point の端点比較ではない。
- `AuthenticatedHop458` は独立な各 hop と有限 trace を定義し、data-only wire との両向きの対応を証明。任意の有限長、全 proper prefix の raw K2 不在、末尾の既存 raw K2、使われた新しい照合を反映。元 graph には行も edge も付け足さない。単一可視候補、親の point 1 個、元 where 1 つ、出力指定なしの Ready 診断。ここでは選択・辞書・where 子生成・出力書込をしない。
- 累積入口は `RoutedInlineStructural458.check_full_structural458`。本周の先の `RoutedInlineVariant458.check_full458` へ直接委譲し、さらに C457 に全入力の旧 Bool を保存。局所独立導出から exact report の witness を具体化し、同じ State の任意の FitsFull で元の source 読みと field K2 を保存。witness にモデルを渡さない。
- 一つの本物の fitting-state fixture で、named record → covariant nominal → pair 第2成分 → variant → record field を通る。後続の四種の native inline 読みが同じモデルに実在し、正確な終点 5 を再生する。元 issuer・payload 全体の綴り・ordinal・where ID・報告先・末尾 K2 を変えた照合は false。payload 全体の綴りを変えた対照は上流の nominal で落ち、pair の非選択側を別の検査位置にはしない。旧の実正例も保持。前者は新規の言語受理・拒否・表示規則ではない。

## 残りと境界

- 有限パスの長さには制限がないが、元 inline payload を読む grammar は限定的。非訪問の pair 成分に推論された `int | str` を実 ordinary row で持つ適合対照では、今の入口の同じ field report に通る新規 wire がないことを別途確認した。これは witness 範囲の穴で、言語の拒否ではない。私的検証では、§6.3 の同一 tag 枝を元の head に重ねた別の適合対照も、全捕獲で同じ正規形・DeclarationReady を保つのに、元の綴りを直接読む現入口には通る wire がない。未訪問 payload を開かない狭い修正などは公開入口に入れていない。任意の inline source／bound pattern、上流のコンパイラが実名付き raw operand を供給する保証、旧 shape で hidden な raw-inline path は未解決。source の構造を raw edge に作り替えない。
- I-86 の移管どおり、open tail（解決済みも）は G06/G07、非 point nominal と一般 mode/kind/多引数は G20/G21。どれもこの周で始めていない。G04 は閉じない。G05・G03b・spec・凍結対象・一般 NFR/停止性は触らない。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。固定 Git bytes を production 9 と独立 Audit 11 として物理的に再検証、66 audit queries は標準公理のみ、3 組の実行回帰。Audit の import: Yulang.* 以外 0 件。既存 production 7,779・Audit 2,200 の blob を全照合し不変、集約は import 9 行の追記のみ。凍結ファイルは ID のみ照合。全体ビルド、verify-lean.sh、Rust、parser、ソースからこの FullProblem を生成する frontend は未検証。
