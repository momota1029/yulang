この周に閉じた C の行: C11（`dictionary_sound_R11`、`ExplicitPick419.check_sound`）。仕様 6.5 の `impl Pick {x:'a,..'rest}: type out='a` に、元の二 field が根拠つきで分かる一点 record を渡し、捕捉した実 field を元の明示 B6 RHS から固定先へ返す例を通した。

## 変更と結果

- `R11` に実際の可視 singleton 宣言の局所選択を追加。出現・宣言順・出力順 0・固定先・元本文・元の型の木を同じ State から読み、根拠つきの実 field と residual を捕捉した。`check` の証人は実際の宣言と行の添字、raw 根の検査データだけを渡す。旧分岐の値は変えていない。
- 同じ State の全 fitting model で辞書と固定出力を証明した。使われる元の field と、残した residual の名前を区別する。元の二つの物理行添字から同じ出力を照合できるときも、論理上の出力順を変えられない。固定先に別の右辺の literal 行があれば、この成功分岐は通さない。`check_has_original_typed_write_at_supplied_locator419`、`check_cannot_change_report_at_actual_Pick419`。
- 根の raw K2 は B6 がなくても旧入口で優先。到達しない実循環がありながら同じ State が fitting model を持つ場合は、本来の選択と辞書を保存した。間違った出現・宣言順・出力順・型木・固定先・本文・保持されていない行は通らない。未対応の `false` は言語の拒否ではない。

## 検証と範囲

- 技術ピン `67bc8f0a7190cfcd6f39b574cf66b2f2e5060691`、Lean tree `c041981373f6e24053ab62e8795f5ea61161eb5a`。Lean **4.35.0**、厳格な `--trust=0 -DwarningAsError=true`。追試・標準公理・正負の検査は [固定証跡](../design/dots-cycle-419-c11-verification.md)（[一覧](../design/dots-cycle-419-c-coverage.md)）を参照。
- 最終確認時の `integration/m1-final` は `7d08c65efe086841811feb18e3391eaf2223aeda`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C418 までの exact Lean tree 一致を確認しました。C419 の実装はこの報告時点では work/dots-main です。
- C11 は一点・既知の実入力・where なし・明示関連型一つの範囲。非点や未完了 W、既定 RHS、`Index str int … char` 自体は含めない。I-65 の 1・2・3 と固定した意味は変更なし。Rust、全 Lean suite、停止性、solver の NoFalseRejection は未実行・対象外。使用量の枠は不明。

- 最終照合開始 `2026-11-25T15:20:24.753Z`（50 分経過）。

**C の残り: 11 行（C12–C22）。** 次は C12 の、実宣言に明示 RHS がない場合だけ元 role default を使う経路。
