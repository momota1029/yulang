この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C461 引継ぎ

- 実開始 2026-11-27T08:34:06.861Z、通常終了下限 2026-11-27T09:24:06.861Z、終了と writer 解放は同 commit の heartbeat。使用量の枠は不明。
- I-87 の G04 だけ。権威 `integration/m1-final@2aff7bb9330c9eb1bfd1146c1cb76b8dbf4947d6` / Lean `3e5a327796943b4c84e362cedd8902dfbddc9ba7` は C460 と同一の Lean。C460 の exact な統合を開始時に確認。今回の [固定済み成果](https://github.com/momota1029/yulang/commit/39410d67092deaea747dd0c479cd4fd1796f2a2d) / Lean `bb03498abfa398bfb2152fdc636f19216a6a024d` は work/dots-main にのみ公開。設計: [実元の適格性](../design/dots-cycle-461-i87-source-eligibility.md)、[有限欄と安定性](../design/dots-cycle-461-i87-finite-source-shell.md)、[既設分岐の構造 scope](../design/dots-cycle-461-i87-existing-homogeneous-scope.md)、[同一 wire・同一 Bool](../design/dots-cycle-461-i87-same-existing-boolean.md)。

## 示したこと

- **元 source の適格性と一つの field 経路**。元可視候補、元 head 引数と実 point capture、role の元 table、唯一の元 where、出力空、真正な `DeclarationReady` を元の `OriginalAnchor` に結び付けた。実元 where は宣言の同じ位置・同じ ID から読むが、この読取を where の実行や別 candidate の選定には使わない。`EligibleStart` と独立の有限ヘッダ証拠を同じ C460 構造 reader に差し込む。任意の同じ author/構造 scope 下の実 field K2 の正確な report と有限データは iff。親 root K2 との別、実元の field 位置、同じ FullState の全 FitsFull を保つ。
- **既設 C459 の同じ Bool**。任意の FullProblem、report、旧 FieldWire で、既設 `HomogeneousClosedEntry459.check_full_homogeneous459` の `.fieldK2` は、同じ wire に中立な配置を足した構造 read が実元 report と **旧 true stamp** を返すかの Bool と等しい。旧の header key と raw hop/escape/terminal cycle tickets は両方向でそのまま。旧の真正ヘッダから閉じた正規形と実 constructor coverage を、旧 raw hop から選んだ各子の scope を帰納的に導いた。旧のこの分岐の成功が独立 `LegacyScoped` に一致するために、別の経路 scope 仮定を足していない。旧 checker は編集せず、新分岐・診断優先順位・spec を変更していない。`previous` の一般化ではない。
- **有限欄と全捕捉安定性は別**。元 role/point/入力/where・scope/coverage・静的 `Smaller` を有限に読む。これらが揃った同じ宣言では Ready になる残りの条件が、全捕捉の `StableSmaller` と正確に同じであることを証明。既知の反映済み安定性を与える場合の合成を定義した。旧 C457/C459 の真正な供給源に分解を適用しても、全入力のヘッダ読取と同じ route に対する report Option は同一。構文や静的サイズだけから一般の安定性を決めない。

## 実対照と残り

- 実 C457/C459 の起点に同じ reader、同じ受理された C459 raw wire を使った。nonpoint に変えるだけで、raw receipt は残っても実 eligibility と旧 Bool は false。別 role・issuer・原 clause・訪問位置や terminal K2 欠落も区別した。実 fitting state の named-only 経路は read receipt があっても false stamp なので旧 homogeneous field には送って受理させない。§6.3 の capture 後同タグ合流（元の単一 pair に包んだ対照）は、実有限欄と静的縮小を通るが、`'a := int` で strict descent が消えることを証明した。
- 一般の G04 で、元 source / role / where と point を同じ規則の下で供給する有限証拠（特に、既存のヘッダでない元構文に対する全捕捉安定性）、上流 inline/bound の実 raw 位置、既に残る join の現 visitor に対する対応は未証明。旧 residual join / 捕捉変数を読めないことは言語の拒否ではなく、任意の case を足さない。open tail は G06/G07、非 point・一般 mode/kind/多引数は G20/G21。G05、全体 NFR、parser/frontend は未着手。I-84 の表示に新判断なし。質問ノートは追加しなかった。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。公開固定 Git bytes の production 15、独立 Audit 18、公理照合 72（標準のみ、またはなし）、実 guard 3。Audit の import: Yulang.* 以外 0 件。旧 production 7817 と旧 Audit 2244 の全 blob は不変、集約は import 15 行の追記のみ、凍結対象は ID 照合。報告込み 40 paths、lean と notes のみ変更。全体ビルド・verify-lean.sh・Rust は未実行。
