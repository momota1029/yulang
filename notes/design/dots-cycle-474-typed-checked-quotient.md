# C474: 最小商を同じ元入力の型意味に接続

C473 の公開 Lean tree `c6402e35b0f6b6392296fd5bdba6c4207cc0bdeb` を authority `397026ba53959d629f0112f5173111ebc73e2200` と同じものとして確認。I-93/I-94 に従い、既存 raw の名前・行、State、既存 checker、言語仕様は変えない。

1. 実際に照合済みの完全な観察コーンの各ノードから型つき構成子を復元し、旧構文の物理行と同じ選択子・子の順に対応づける。名前つきの読み取りは検査済み旧 Alias、inline は元の物理行・経路を使う。レコードの first-visible と安定な述語順の意味を旧 carrier の定理で証明する。
2. この構成子群を有限の再帰型ブロックとして解釈する。深さに関する帰納法により、同じ元 raw を満たす任意のモデルの各値はその再帰型値と同値。型つき構造が実際に検査した数値コーンに戻ることを示し、同じ商の点は全元 `FitsFull` で同値な型を表す。モデルの値を読んで商を決めることはしない。
3. 元の nested report の終端 checkpoint と物理位置を取り替えずに保持する。真ならその終端から構成子の非空の経路で等しい型の商へ戻る。偽なら同じ検査済み商の類への非空の戻りはない。偽を「証拠なし」や「任意の型等価性に関する否定」に置き換えない。
4. 実際の単一候補・事前確認済み GD・同相 source の例で、深い inline field と既存名前つき点が同じ類で全モデル同値、手前の field は循環値に到達しても自身は安全と分ける。従来の正誤 guard も維持。
5. 現行 compiler から元入力の author/物理行を発行する橋は未完。C332 は別途確証を持つ source を読んで捕捉結果を返し、その捕捉だけでは物理・著者 ordinal は復元できない。新しい author を仮定したり既存出力の発行を流用したりして G04 を閉じない。

## 異なる表示と入力 producer の境界

同じ構成子の符号帳のもとで、異なる個数・異なる展開を持つ二つの実際の到達コーンを有限対応関係で照合する。片方の代表や数字をもう片方へ写して source 報告を置き換えない。対応の後続が欠ければ未確定。三点と四点の実例では、二つの元報告の真偽と、元 inline 点と既存 logical 6 の全モデルの型同値を確認した。

`yulang3` の確認点 `68295bef1ff86060b33e6deebffe69c22ce64dfc`: `Cargo.toml` の Rust ワークスペースは parser/recovery と xtask。 `crates/yu-syntax/src/full_parse.rs` の `ParsedFile` と `SourceNodeKey` は parse revision と immutable CST node identity を持つが、I65 の型付き要求・raw 行・author ordinal のペアは出力しない。この checkout で新しい compiler 入力 producer は確認できない。Lean 側では C473 が示した C332 の capture 投影の情報欠落は残る。C353/354/356 の旧型付き source plan は固定 variant/unary companion 又は選択後の出力を扱い、当該 same-phase input manifest にはそのまま写せない。既存の読取り・解釈だけを証明し、producer を作ったことにしない。

署名表の順序が異なる場合も、元の子を変えず共通の構成子表へ単射で番号を付け直してから、有限対応だけを検査する。実例では元の二表を逆順にし、数字だけを比較すると失敗、共通の構成子を比較すると成立、元の source 報告は不変であることを確認。
