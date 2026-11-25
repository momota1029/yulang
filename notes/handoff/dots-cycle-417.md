この周に閉じた C の行: C09 / X6 後半（`dictionary_sound_R9`、`X6Ambiguous417.check_sound`）。同じ `R :{tick int}` に plain 合流 head と ground head の両方が当たるため、どちらも選ばず「曖昧」と報告します。

## 実装と証明

- [仕様 6.3](https://github.com/momota1029/yulang/blob/ad65248e70b70ca116703701c55bbb220c5e21c6/spec/06-roles.md#L117-L118)・[X6](https://github.com/momota1029/yulang/blob/ad65248e70b70ca116703701c55bbb220c5e21c6/notes/handoff/2026-11-08-m1-spec-examples-conformance.md#L24) の二候補だけを追加しました。実可視リストを二つの異なる元宣言でちょうど尽くし、その両順序を受け付けます。`PlainHit.originalHead` は元の二変数を同じ実 payload 全体に捕捉し、`GroundHit.originalHead` は同じ variant の実 payload を `int` と照合します。ground に必要な元の型つき観測を実番地で確認し、普通の生 int 行だけでは候補にしません。
- 生グラフの K2 を根・ground が実際に調べる payload で分けました。実到達の payload K2 は根が安全でも曖昧の報告を止め、未到達の実ループは妨げません。旧入口の根 K2 は元 int 観測の有無にかかわらず委譲します。C09 は内部 K2 一般の診断分岐を足す仕事ではありません。
- `R9` の追加は局所の `.ambiguous` だけ。選択・where・出力の作成を加えず、旧の固定 `DictionaryEvidence` と同じ State の全 fitting model に対する `check_sound` を保ちます。この対象状態に別の分類はありません（`exactly_the_ambiguity_classifies_for_actual_X6_417`）。任意の成功した R9 導出を元の event・順序・receipt のまま R8 に戻せることも示しました（`successfulTraceWasAlreadyR8`）。

## 検証

- 固定技術版 `9f3242f3742abc1e62ac4f1d346e87123af737eb`、Lean tree `84940bfb96de2b0043e26437d186c6fffa801236`。[検証詳細・コマンド](../design/dots-cycle-417-c09-verification.md)。
- Git の同一 blob を用いた公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`。独立 **10 source / 4 audit**、C416 合同 **20 / 8**、C409–417 の既存範囲を含む **78 / 49** がすべて終了 0。48 個の個別監査は標準公理のみ。
- 追加した `GeneralDeclarativeI65I74X6Ambiguous*417.lean` は Events・Visits・Rule・Replay・Report・Entry・Priority・Locator・Coherence・Conservative。新規 standalone audit は Core・Spec・Coherence・Graph の四つ。barrel は十 import の追記だけ。凍結二ファイルの内容は開かず、blob ID の不変を確認しました。規定の report/heartbeat まで含め全 20 パスです。
- 実例は両宣言順と両順の元 ordinary 行の六通り、同じ payload への alias、未到達の実ループを検査しました。元観測不足（同じ `int` が別の元 slot にある場合も含む）、別 payload、第三の可視候補、偽の選択・出力、根と実到達点の生 K2 を「曖昧」と報告しません。旧入口と現入口の 21 実行対照、番地の 32,768 組の対照も通過しました。実到達外の再帰がある同じ fitting model でも報告が成立し、七状態の有限色対照では根・payload gate だけでは元観測を代用できないことを確認しました。
- 最終確認時の `integration/m1-final` は `ad65248e70b70ca116703701c55bbb220c5e21c6`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C416 までの exact Lean tree 一致を確認しました。C417 の実装はこの報告時点では work/dots-main です。

## 範囲・次回

- 同じ State に実の一点 variant、元の自己 join、元の int payload 観測があり、where・関連出力がない対象に限ります。検査器は自己 join を追加しません。ほかの形への `false` は言語の拒否を意味しません。
- 全体ビルド、Rust・実 solver の証人生成の完全性、停止性は実行・主張していません。質問なし。利用量の枠は不明です。
- 次は C10。仕様 6.2 の可視候補を全部調べ、単なる読み取り失敗ではなく、実根拠のある構造的不一致を除いた上で一候補を選ぶ行です。本当に重なる例を非重複とみなしません。

- 最終照合開始 `2026-11-25T13:20:13.594Z`（50 分経過）。

**C の残り: 13 行（C10–C22）。** [一覧](../design/dots-cycle-417-c-coverage.md)
