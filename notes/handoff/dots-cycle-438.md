この周に閉じた C の行: C18（`CompletedEntry438.dictionary_sound_R18`、`check`、`check_sound`。work/dots-main の scoped 検証）

# Yulang cycle 438: 完了した別需要の native head を公開 Lean 検査器まで接続

I‑79（`63620853fb52ce1319c2bd85d2b42b2cca7b2e72`）で許可された C18 のみ。正本入力は `integration/m1-final@0512c698732a0aeeb444f869f586bccc0a15866d`、C437 と同じ Lean tree。仕様 [§6.3: 完了した需要を根拠にした再開](https://github.com/momota1029/yulang/blob/0512c698732a0aeeb444f869f586bccc0a15866d/spec/06-roles.md#L182-L197) に沿って、普通の等式の存在だけと、実際に片付いた source の出力を区別した。

- **独立の新規則。** すべての State・request・辞書について、旧 R17 の判断をそのまま入れるか、同じ State で選択・完了した別 occurrence の有限 producer を使う。元 B6 の出力番号・元の固定先・literal retained row を維持する。任意の適合モデルで、元 B6 の plan が評価した値と保持された下端の値は、双方向の部分型関係で同値になる。producer と consumer の辞書を同じモデルで解釈し、下端の authored syntax は仮定しない。旧の `Classifies` や `DictionaryEvidence` を内部から広げず、その上に新しい公開 entry を加えた。
- **公開 `check`。** 証人は位置・元の需要・有限 raw escape データのみ。source book、実型モード、元の B6 plan、保持行、別に根拠のある upper と payload の明示的な比較制約を照合し、選択後に元の center を読む。実 fixture は producer [101] / decl 0 / output 0 / 保持行 0 / L40 と、consumer [202] / decl 1 / capture (30,32,34) に通る。lower に authored route がなく、`nativeSyntax 40 = none` の適合モデルを明示した。保持行を取り違える、元の発生箇所や issuer を変える、旧 producer の出力を consumer の write として再発行する、Tree/辞書を変えると false。現行 State を raw alias 付きで実際に組み直した場合、C18 の選択は false、旧 raw K2 退けが true。既存 witness の Bool は全入力で変更しない（`rfl`）。未対応入力を言語の拒否とみなさない。
- **固定外形。** `dictionary_sound_R18`、`check_sound` と `verified_R18_result_classifies_in_same_State438` は同じ State とすべての適合モデルを量化する。既存の旧証拠の定義・語義は変更しない。新 checker の範囲は、元の unary covariant の一候補、保持された一出力を持つ where-free producer、consumer 自身の where/output はなし。この新しい分岐で再帰的に producer を作ること、全候補一般、入れ子のモード、solver が証人を生成すること、NoFalseRejection、停止性は未証明。

## 検証

[10 本の exact blob と受入条件](../design/dots-cycle-438-c18-native-entry.md) ／ [strict ログ全文と追加対照](../design/dots-cycle-438-c18-verification.md) ／ [残り一覧](../design/dots-cycle-438-c-coverage.md)

- 公式 Lean 4.35.0 で、正本の既存 182 依存と新規 production 5 本をそれぞれ `--trust=0 -DwarningAsError=true` で focused compile。production-only path、個別の空ディレクトリで standalone Audit 5 本。全 exit 0、単独 Audit が出力した 28 公理監査は標準 trio のみ。Audit の import: `Yulang.*` 以外 0 件。公開 source を Git から独立に取り直して 10 本を 1 プロセスずつ同 strict stdin でも全 exit 0。
- 追加対照では、同じ raw 等式と適合モデルでも本来の B6 plan がなければ不成立、実 Seed を残したまま consumer の raw cycle を足したときは新ルートは false になり旧拒否が通る。実 `check` の補助 `#eval`（コミットした Lean には追加しない）でも [true, false, false, false, true]。早期 pin `efecd0ba5ce1a63c184edaba75637f2e9a7cec44`、Lean tree `2bba5d89d1e8d9c2d94c5fc3a8a359c3b3b63421`。旧 7,665 production / 2,050 Audit entries と凍結例の blob ID を保持、barrel は末尾5 importsのみ。全体 Lake、監督役の `verify-lean.sh`、Rust は実行していない。この周の差分は 17 パス（production 5、Audit 5、barrel、設計 4、報告、心拍）。質問ノートなし。使用量の枠は不明。
- Yulang2 照合: 既存監査 [C3-PARENT](https://github.com/momota1029/yulang/blob/55574b6052ef1534fd0fc36d6d3617ebede59a0e/notes/audit/x-oracle.md#L61) の実 producer 出力に続く利用と、ROLE-003 の宣言 where の差を確認。既存の監査ログでは同じ exact native lower 証人・raw K2 の組を確認できなかった。新しい Yulang2 run は未実施。根拠は現行 §6.3、旧世代の推測は移植していない。

最終照合時の正本 `integration/m1-final@0512c698732a0aeeb444f869f586bccc0a15866d` の Lean `07eaa114f990a25365054ea6bd17ddc2b4ad46c2` には、まだ C438 の exact entry を確認できない。C18 の完了は `work/dots-main` 上。監督役の統合確認は別。

**C の残り: 4 行（C19–C22）。** C19 には進んでいない。実開始 09:30:32 UTC、50 分 を経過して通常終了。sole writer を解放。
