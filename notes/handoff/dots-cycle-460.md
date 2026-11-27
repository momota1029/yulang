この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C460 引継ぎ

- 実開始 2026-11-27T07:30:06.509Z、通常終了下限 2026-11-27T08:20:06.509Z。終了と writer 解放は同 commit の heartbeat。使用量の枠は不明。
- I-87 の G04 だけ。権威 `integration/m1-final@2ae499473a7c541adf199e91c99596907cdb505d` / Lean `0763bfd35c027bb405149ec819e0b56780f1b09e` は C459 と同じ Lean、C459 の統合を開始時に確認。この周の [固定済み成果](https://github.com/momota1029/yulang/commit/20d51702bba6dd837a06a836744ec3542a619ad6) / Lean `3e5a327796943b4c84e362cedd8902dfbddc9ba7` は work/dots-main にのみ公開。設計: [元の全有限文法](../design/dots-cycle-460-i87-written-grammar.md)、[一つの経路](../design/dots-cycle-460-i87-joint-compiled-field.md)、[元アドレス](../design/dots-cycle-460-i87-original-report-locations.md)、[構造帰納と境界](../design/dots-cycle-460-i87-exact-finite-scope.md)。

## I-87 の成果

1. **元構文の全域・可逆読取**。元の解決済み `GeneralDeclarationPatterns.Pattern` の全構成子を相互帰納の `Term/Args` に表した。開いた tail、適用の全引数、variant の異なる payload や重複、join/括り、shadow も捨てない。同じ grammar を全 head と元 where の引数に適用し、元の ordinal/ID を別々に保持する。primitive / 名付き型の種別は実 catalogue から読む。lexer の綴りや解決済み Nat ID が持たない情報は復元しない。元 AST と既存コンパイラの正規化は別。
2. **構造ごとの一つの reader と訪問判断**。閉 record の選択 field、同じタグ、primitive pair の指定位置、実宣言 covariant 単項 nominal を構成子ごとに定義した。現在の authored catalogue / mode の結果は演算子の根拠であって、実の physical endpoint が point であることは旧 opener が別に検査する。実 raw `AtStep`（snapshot の row・Alias・issuer と実 child）から、同じ選択位置の元 query を元の `AuthoredQuery` に沿って子へ輸送する。別の兄弟を raw で開かない。元コンパイル後は各段でコンパイルをやり直さない。root/prefix の escape、terminal field と同じ raw K2 を保持し、新しい edge は作らない。各ステップの構造の大きさが減ることも示したが、全体 solver の停止性ではない。
3. **実経路の有限 witness と all-FitsFull 保存**。任意の元 `OriginalAnchor`、実選択位置ごとの `CompiledOpening` と真正 raw hop があるとき、任意有限の `ScopedRaw` を構造帰納で `CompiledTrail` にし、元 occurrence/decl/where ordinal/ID、既存 raw path と terminal を持つ同一 report への有限データ iff を示した（`any_actual_scoped_source_report_has_an_exact_finite_wire`）。witness が報告の値を勝手に与えないようにして、実 roster / head / 同位置 capture / 元 where を読んで構成する。同じ FullState の全 `FitsFull` で `any_scoped_source_receipt_is_the_same_field_in_every_fit`。この iff の scope は、独立な *実* scope / raw / compile が既にある経路の receipt であり、任意の source claim の受理や、経路を自動発見する定理ではない。

## 残り

- `OriginalAnchor` は指定番号の実 where を照合するが、raw path から where を選定しない。実例では二つの元 where が同じ raw route/terminal を持ち、同じ実 fitting model で別々の元 ordinal/ID を保持した。親の point/role/出力・DeclarationReady・該当する where の条件を現入口と照合する必要が残る。point を外して raw receipt だけが残る既存 fixture の狭い対照は私的検査だけで、新しい判定ではない。I-84 の表示位置は未定のまま。
- 既存の正規化で消える同じタグの重複を実 C459 の回帰で確認した。正規化後に残る join／bound 変数そのものには、旧 raw `Visit` の開始規則がない。任意の inline/bound の元位置に対する上流の typed/raw 対応が一般に成り立つという証明は未達。私的な実対照では、全捕捉での安定性を持つ元 DeclarationReady と同じ適合モデル・実 raw terminal K2 があっても、異なる二つの tag が正規化後も join なら旧 Visit でそこに達しない。これは言語の拒否ではない。open tail は G06/G07、nonpoint・一般 mode/kind/arity は G20/G21。今回それらの実装および G05 は未着手。
- 次に必要なのは、(i) 独立 G04 の起点が `OriginalAnchor` と実の readiness / point/role/where の条件を供給する証明、(ii) 許可範囲の元 inline/bound pattern と実 raw 位置の scope 保持、(iii) これらから同じ累積入口と同じ報告を通す合成。今回は新しい累積分岐や診断優先順位、spec の変更はない。質問ノートは追加しなかった。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。公開した固定 Git bytes の production 17、独立 Audit 19、公理照合 86（標準のみ、またはなし）。実 guard 2: 実 C458/C459 の同じ report と wrong issuer / 別の座標 / terminal / clause、実二つの元 where の address と不一致対照。Audit の import: Yulang.* 以外 0 件。旧 production 7800、旧 Audit 2225 は全 blob が不変。集約は import 17 行の追記のみ、凍結対象は ID 照合。開始からの変更は報告込み 43 paths、lean と notes のみ。全体ビルド・verify-lean.sh・Rust・parser/frontend は未検証。
