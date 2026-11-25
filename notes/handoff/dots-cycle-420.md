この周に閉じた C の行: C12（`dictionary_sound_R12`、`RoleDefault420.check_sound`）。要求名と同じ明示 RHS がない場合だけ、元の role が持つ既定 RHS を選び、元の B6 の型木・宣言順・出力順・固定先を同じ State で照合した。

## 変更と結果

- 仕様 6.1／10.7 に従い、同じ出力名の明示式は既定値より優先し、別名の明示式は妨げない。同名の明示式の B6 が得られなくても、既定値へ切り替えない。
- 位置 0 の既定値は元の引数全体を読む。同じ数字 0 を実装の field binder に書いた場合と区別した。実宣言された再帰 nominal `tree` を返す既定値も、宣言本体由来の mode により検証した。共変 `Box` の追加監査は独立再検証を通ったが、ブランチ未反映なので今回の公開済み範囲に含めない。
- 実宣言と元の B6 plan が固定されれば、二つの異なる証人でも診断木と台帳は一意。元の固定先に別の literal RHS があれば肯定分岐には入らない。旧入口・根 raw K2 の優先はそのまま。未対応の `false` は言語の拒否ではない。

## 検証と範囲

- 技術ピン `676f02753db405bd1e5c8c67e6e6079891626e46`、Lean tree `c76d9eaa32800c156be5fe79f9970e0da74b32c6`。Lean 4.35.0、`--trust=0 -DwarningAsError=true`、標準公理のみ。[固定証跡](../design/dots-cycle-420-c12-verification.md)／[一覧](../design/dots-cycle-420-c-coverage.md)。
- GitHub が中間の ref 更新をエラーで返し、一部の心拍を公開できなかった。技術ピンの公開と検証は保った。
- 最終確認時の `integration/m1-final` は `24309085b67f46a328252917ef4035a4a436d190`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C419 までの exact Lean tree 一致を確認しました。C420 の実装はこの報告時点では work/dots-main です。
- 一点の二 field record・可視一候補・where なし・出力一つ・固定行に厳密に表現できる B6 RHS の範囲。仕様の `char` 例は今の `Inference.Base` にないため置換していない。B6 が型付けを与える側の証明、一般の矛盾診断、solver の NoFalseRejection、停止性、全 Lean suite、Rust は対象外。I-65 の固定された意味は変更していない。使用量の枠は不明。

- 最終照合開始 `2026-11-25T16:20:21.886Z`（50 分経過）。

**C の残り: 10 行（C13–C22）。** 次は C13、実際に選択した重複 head binder の元の中心どうしへ等式を加える規則。
