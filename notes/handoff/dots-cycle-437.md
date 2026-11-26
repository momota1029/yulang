この周に閉じた C の行: なし（C18 は未完了）

# Yulang cycle 437: 完了した Seed の出力から scoped Observe までを Lean で検証

I-79（inbox blob `63620853fb52ce1319c2bd85d2b42b2cca7b2e72`）の C18 のみ。入力の正本は `integration/m1-final@fdab22303a5b928c1af2f87458da7a55dd12b04c`。C17 は統合済み。今回は Lean を利用でき、次を実際に確認した。

1. **元 B6 出力と固定先。** 実ソースの declared covariant Box は native header を通り、旧 primitive/invariant 用ヘッダに必須の explicit constructor check は false。元 B6 の request/decl/output/body と、行番号つきの literal retained row を結ぶ。同じ target・同じ適合モデルの値を持つ別行でも、実際の型つき出力の字面が違えば reader は受け取らない。
2. **完了した別需要。** 元 [101] の Seed を実際に選び、原 B6 frame・出力0・固定先40・保持行0を保った同じ状態の有限 `SourceTrace`/`SupportForest` を得た。実 reader は別途検査した元の source basis と typed B6 出力を入力としてこの proof を組む。公開 witness の locator だけからその入力を組む入口は未接続。任意の適合モデルで Seed の辞書と元 B6 の lower 値を同時に得る。
3. **scoped consumer と raw K2。** 同じ状態の Observe で authored route のない L40 を上記の完成出力が支え、実 upper は slot42・issuer [303]。選択後に元の center issuer [202] を読み、捕捉名 (30,32,34) を保つ。明示した一つの適合モデルでは `nativeSyntax 40 = none` でありながら、Seed の辞書・lower の値・Observe の scoped 証拠が同時に成り立つ。postselection reader は実 upper、中心と同一の slot/構文でも issuer [999] の別記録、不存在をそれぞれ区別する。raw に行 `30=40` を一つ追加すると Observe 根で既存の raw K2 証人が通る（Seed 側の根は引き続き safe）。改変 raw state に適合モデルがあるとは述べない。

[検証した層と各 blob](../design/dots-cycle-437-c18-verified-cut.md) ／ [strict 検証ログ全文](../design/dots-cycle-437-c18-lean-audit-log.md) ／ [公開 entry につなぐ残り](../design/dots-cycle-437-c18-public-entry-seam.md)

## 検証と残り

- 公式 Lean 4.35.0、`--trust=0 -DwarningAsError=true`。新 production 5 本の個別 build と、production-only path／独立したディレクトリでの standalone Audit 7 本で全 exit 0。公開後の Git source を取り直した別プロセスの strict stdin 再検証も全 exit 0。Audit の import: `Yulang.*` 以外 0 件。36 個の公理出力は標準の公理だけ。scoped の既存 94 production も immutable Git bytes を確認して strict 個別 build。古い既存 cache は対象の source 3,789 本を Git bytes と照合したが全件再 build ではない。
- `Yulang.lean` の 5 imports は旧 bytes の完全な末尾追記のみ。既存各 Lean/Audit 本体、凍結ファイル、spec、統合 refs は変更しない。技術 pin `ed7e39f81d521b556dd37962b3b4baa5cb9b2351`、Lean tree `07eaa114f990a25365054ea6bd17ddc2b4ad46c2`。全体 Lake／`verify-lean.sh`、Rust、NoFalseRejection、停止性は対象外。使用量の枠は不明。
- 採用済みの canonical R17 は変更していない。**`dictionary_sound_R18`、公開 `check` の data-only 分岐と全入力での旧 Bool 保持、同じ外形 `check_sound` はまだ未実装。** 既存 C406 の scoped 判定を通過したことは、公開 entry の受理完了ではない。C19 に進んでいない。

**C の残り: 5 行（C18–C22）。** 実開始 08:33:48.401 UTC。50 分の通常ゲート後に報告し、sole writer を解放。
