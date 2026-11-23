# cycle 379 handoff — I-65 step 1: actual native dispatch and selected where evidence

UTC 2026-11-23T22:30:43.430Z 開始。integration/m1-final `81dada7891044060e8d044f97852b87473163213` の standing orders / inbox / roles・inference を再読し、I-65、STOP なし。C378 `f628ccc011f7b6ccbc133f79e0a4287f59ba1f3a` から work/dots-main のみ expected-head / non-force。 [設計](https://github.com/momota1029/yulang/blob/dbb3a4c1facfd9278b74941055253f784eb3b90f/notes/design/dots-cycle-379-actual-unary-dispatch.md)。

## Lean で検証した六つの部分

1. [A](https://github.com/momota1029/yulang/commit/abec8c24199eba0e78be0ba79a9a5f750f3ae845) `ActualUnaryDispatch379`: C361 の実際の unary matcher が、経路・保存コード・正規化した候補構文の同じキーを照合し、宣言 kind 読みを通したとき、literal 子 ordinal 0 がその呼出しの対象になる。外側の結果は子の結果に従うため、子が失敗しても構文上の入口は消えない。C378 の正確に release された実行と元の候補位置を接続。古い reader は `.leaf n` の先の compound query では `none`。これを言語上の棄却にしない。
2. [B](https://github.com/momota1029/yulang/commit/33cc17af8e910cd820ac35e10e58acb50c9762ba) `ActualCandidateOrder379`: C361 の既存の可視2行 scanner は、その有限グラフ検査が候補検査に先立つ。同じ `Port` の実際の受信引数位置・保存行を保持しつつ、最初に書かれた unary 候補の子の結果と二行目の検査結果に分解。
3. [C](https://github.com/momota1029/yulang/commit/08cc4eb08fb764b4fe75acddb393923857c0754b) `EnteredOrdinaryRoot379`: 実際に開いた native 下端、positive dispatch、literal name、元の子の実際の普通翻訳があれば、別の普通グラフで最初の `Visit.here` を構成できる。未完出力は支持から外れていても同じ現在状態の unfiltered K2 を発火させうる。nominal-with-bare-capture の普通 query には子孫訪問がないため根の局所 return rank が K2 不在と同値。古い C361 が普通 K2 を実行するとは主張しない。
4. [D](https://github.com/momota1029/yulang/commit/213e4e8111500dcab681fe1189c98890dab11796) `IndependentlySelectedWhere379`: 別の**既存 C363 断片**で、独立に選定済みの native 非点親の capture を使い、実際の普通 `Finished` where body と literal な子の出現パスを得た。別に選定した子の現状態に、親の普通制約・区間・等式と元の実際の native board が保持される。一つの子側 fitting assignment で独立に release された三つの元端点を引き続き観測できる。この既存 root の固定出力は空。
5. [E](https://github.com/momota1029/yulang/commit/654001519b2cb48858c6beb99ad593cc9470012f) `ScopedNativeCalls379`: C361 の実際の gate 後の証拠付き順序。一行目の `none` は `[0]` だけ、`[0,1]` の二行目には実際の一行目成功の証拠が必要。trace の完了ビットは元 scanner と一致する。候補全体の言語の verdict ではない。
6. [F](https://github.com/momota1029/yulang/commit/f8a0a5bb9d3d95d4c7d02e3496de1dbf97d9b964) `AuthoredDispatchMode379`: 同じキーの authored declared mode は source graph の実読みで一意。実 unary constructor check と C378 の片側 prefix が同じ value kind と分散を読む。既に実際に入った親の片側 value port は、唯一の子 ordinal 0、同じ authored pattern、同じ physical payload に一致する。

## 検証・残り

- 正規保持 Lean 4.35.0。必要な不足依存を固定 GitHub ソースの exact bytes/SHA と照合して隔離再構築（A 28、B 16、C 1、D 26、E・F 追加なし）。各モジュールは `lean --trust=0 -DwarningAsError=true -o …` で exit 0。名前解決・依存 rewrite の試行失敗後、検証済みのバイトだけ公開。独立 Audit 6本は直接の strict 実行と再実行ともに exit 0。31 宣言は標準 `propext` / `Classical.choice` / `Quot.sound` のみ。6モジュール同時 import も exit 0。全 Lake・全 verify・Rust は未実行。
- 公開は Lean 6、独立 Audit 6、barrel、design、heartbeat、handoff の16ファイルのみ。全変更パスと exact bytes／独立 Git blob SHA、barrel 元バイト + 末尾 import 6、凍結2ファイルの ID のみを照合。終了ゲート 2026-11-23T23:13:04.824Z、実行環境 online。開始から約 42 分、利用枠不明。
- I-65 **1 未完、2・3 未着手**。C361 実有限 gate と C363 実選定は別断片。前者は compound 普通境界で止まり、後者は一般の候補内の実訪問順／早期 K2 を出さない。一般の同じ source occurrence / priority で混在入口を独立に構成する橋と、その選定を C376 の実際の typed capture / install / retention / grant に結ぶ橋が残る。S1/S2 未閉鎖、C 後回し。fixture・仕様・定理文を変えず、旧 Local/C334 の読み替え・停止性を対象にしない。仕様質問なし。

## 次周の新指示

終了確認中、integration/m1-final `4ae7b6d147cbb8763e81f1465578d7d8ea171c5c` の inbox `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e` で I-66 を確認。次周の最初に、固定定理を名前付きの Lean 補題へ分解した設計ノートを作り、証明済み／一部／未証明と未証明数を明記する。以後の「残り」はその表を使う。この周では新しい一覧の完成を主張しない。
