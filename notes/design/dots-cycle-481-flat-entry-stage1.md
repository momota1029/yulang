# C481: 段階 1 の平坦入口と残った型商報告

基準: `integration/m1-final@e36a04e087f691695e79f1deb930048bcf8c4d24`、I-97。C480 の設計 §1 の18入口を対象にし、旧ソース・定義・集約の既存行を変えない。削除なし。

## 同じ旧入口を一層にする

`FlatDispatch481.check_full_flat` は report と witness の対応タグで直接 leaf を検査する。旧 `.previous` を剥がすのは互換 codec だけ。元の入れ子を実行時に渡して判定するのは、明示的に残す C446 の入口だけ。古い `Checker408.Result` の値そのものは変えないが、分類を混同しないよう7段の envelope を区別する。

| 対象（C480 §1） | 新しい一層の区別 |
|---|---|
| C446 retained、C447 selected、C448 opaque/whole、C449 list-site/list-frame、C450 NoSiblingMerge | `legacy` の7 grade と各 wire tag。親子順、出力なし、同じ where の兄弟ガードはそのまま。 |
| C453 GroupedEntry、C454 SamePhase | `grouped` / `rawGrouped`。別 report envelope の混同を false にする。 |
| C455 RoutedRecord、C456 RoutedMixed/RoutedNominalMixed、C457 ReadyRecord/ReadyMixed | 5 field tag、それぞれ旧 `checkField`。 |
| C458 InlineVariant/InlineStructural、C459 Projected/Homogeneous | 4 field tag。後ろ3つは C462 の同一 leaf boolean の証明で結ぶ。 |

- `FlatLegacyCodec481` と `FlatOuterCodec481`: 各入口について全 `p r w` で Bool 等式。旧入口の成功・失敗および不一致を保存・反映。C450 の表の境界は **NoSiblingMerge** であり、別の無ガード実験版は延伸しない。
- `FlatMeaning481`: 各入口の旧 report 分類および各 `m` の evidence は両向き。元の `FullProblem.state` と全 `FitsFull` を使い、どの model も取り替えない。
- `FlatSound481`: 任意の平坦データでの健全性。既存 C446 基底と直接 leaf の独立判断・モデル証拠から構成。18入口の同じ外形を取り直す。旧 per-entry soundness の単なる連鎖呼出しではない。
- `FlatRoundtrip481` / `FlatCurrentImage481`: report と wire の復元で元データそのものが返る。最新旧入口の report 像は C450 の guarded grade + 11 外側タグ、wire 像は全 wire。以前の legacy grade は以前の厳密な意味域で扱い、最新 report の分類に広げない。
- 実例: C459 authored triple の正 branch、古い plain branch、混線した tag と stale terminal。C450 は実 where 順を保持し、当時の無ガード版だけ真になり得る同入力を、現行ガードと平坦版がともに拒む。

## G04 は局所証明を足したが旧判定へ混ぜない

C479/480 の scoped event-wise 存在は証明済み。今回 `SourceExposure481` は有限な連続する旧 `Read.expose` だけを data-only で反映・復元する。元 raw の ordinal と **別途根拠のある**入力表の author ordinal を合わせ、alias はその source-only view 内で検査する。同じ ambient raw に alias があっても pending-only なら全 wire で不成立となる対照がある。単なる等式の存在や `Attached` は発行の根拠でない。既に qualified な `TypedInput` と `PriorPhase.ExactFor`、独立な末尾の Read を使う場合に限り、全元 `FitsFull` の Walk まで輸送できる。実行で消えた発行順や source 座標を推測しない。さらに、同じ logical 6 の二つの primitive pair 位置を含む旧 ordinary model 付きの対照では、位置ごとに別の exact owner 7/8 を読む。両方が正しいが一つの `Nat → Nat` の名前単位 redirect では両方の物理 owner を復元できない。出所を保つには位置ごとの差を残す。

全ての実 constructor 訪問に沿って、その同じ exact 原位置・raw/author 読取りを型商の path へ運ぶ有限 replay は未完。現行の直接 C332 replay が source alias を越える一例を落とすのは旧コードの観測境界で、今回の部品はその連続 exposure に限られる。release 側は exact 完了 owner・version・grant との結合を別に保つ。要求全体の root 優先と signed report の正負・同じ outward soundness を揃えるまで、新しい型商タグは平坦入口に足さない。G04 は未閉鎖、G05 以降には着手しない。

## 次回の削除で守ること

段階 1 が採用されるまで例外を開けない。採用後も、旧入口を含むファイルに新 codec が使う report/witness、直接 leaf 検査、分類・報告の意味・各 Fit の補題が同居する。ファイル丸ごと削除の根拠にはならない。まず対象定義や重複 Audit の直接・推移 import と I-65 使用を版付きで列挙し、移転先を決め、知らない依存は残す。許可単位の明細・前後件数と総ビルド/既存監査は実際の削除周でのみ報告する。`lean/Audit.lean`、`lean/README.md`、spec はその対象外。
