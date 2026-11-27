この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C459 引継ぎ

- 実開始 2026-11-27 06:30:00.195 UTC。通常終了下限 07:20:00.195 UTC。実終了と writer 解放は同じ commit の heartbeat。
- I-86 の G04 だけ。権威 `integration/m1-final@3c3662765a885fa3c06e21295761ff630b5af376` / Lean `3103301de9296b4a356e41487ac6c25451d9d36d` は C458 と同一。最終の権威 `integration/m1-final@3c3662765a885fa3c06e21295761ff630b5af376` / Lean `3103301de9296b4a356e41487ac6c25451d9d36d`。
- [固定済み作業成果](https://github.com/momota1029/yulang/commit/5e3601858bdb1fb14fb0da6c3ea375aa4b04ba40) / Lean `0763bfd35c027bb405149ec819e0b56780f1b09e`。[実施範囲](../design/dots-cycle-459-i86-actual-written-tag-scope.md) と [元同一タグの有限群](../design/dots-cycle-459-i86-exact-homogeneous-tags.md)。

## G04 の実証

- **同じ tag と同じ payload が元の記述で重複したときだけ**、閉じた補助 head を有限に読めるようにした。元の visible declaration、where 位置、正規化済み compiler query は取り替えない。二つの同一 tag から、全 leaf が字面まで同じ任意有限の join 部分木へ広げ、任意の有限の閉構成子文脈に帰納。任意の capture 後の正規形と Paterson の size/occurrence は同じため、元の `DeclarationReady` を保つ。捕獲後や正規化後だけ一致する別の payload はこの規則に含めない。
- 現入口 `HomogeneousClosedEntry459.check_full_homogeneous459` は二枝の正確な旧入口を直接委譲し、その先で C458 の Bool も全入力で不変。元閉 grammar を独立な判断として定義し、有限補助チェックとの同値、実 source から exact report の有限 witness の具体化、逆向きと全ての同じ FitsFull における正確な経路の保存を証明。新しい homogeneous 分岐は旧二枝の閉書式が使えないときだけで、別の empty key を使っても同じ problem で旧二枝・C458 の exact field 分岐と競合しないことを示した。元の same-state raw path/terminal を読むだけで、新しい edge・join の探索・where 子・辞書を作らない。
- 実の resolved source fixture は、閉 record→単項 covariant point nominal→pair 第2成分→variant→実 field の既存経路。二重と三重（左右両方の括り）の元 head を、同じ元候補・raw graph・origins・適合モデル・実 field 5 で照合した。旧 C458・旧二枝の実対照はそのまま true。別 payload、誤 ordinal・元 clause・見ていない site の差替えは不成立。これは局所的な report の検証で、言語の拒否の追加や全体の診断の優先順位ではない。

## 残り

現断片は単一の可視候補、point の親一つ、元 where 一つ、出力指定なし。where 本体の同一 tag 重複は元 Ready／全モデルを保っても現ヘッダの読取範囲外であることを私的に確認した。任意の元 inline payload/bound pattern と、上流が実 named raw operand を作る保証は残る。未訪問 pair 成分を含む新分岐は本周に入れていない。open tail（解決済みも）は G06/G07、nonpoint・一般 mode/kind/多引数は G20/G21、いずれも未着手。G05、一般 NFR、spec は変更していない。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。固定 Git bytes の production 12、独立 Audit 14、96 の公理照合は標準公理のみ（またはなし）、4 guard blocks（新しい対照2組と共通の旧 baseline の再生）。Audit の import: Yulang.* 以外 0 件。旧 production 7,788、旧 Audit 2,211 は全 blob が不変。集約は import 12 行の追記のみ。凍結対象は ID 照合。全体ビルド・verify-lean.sh・Rust・parser／frontend は未検証。
