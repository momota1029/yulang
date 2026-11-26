この周に閉じた C の行: C15（`dictionary_sound_R15` / `StructuralWhere431.check_sound`）。
Audit の import: `Yulang.*` 以外 0 件（新規2本）

# C431: 元の構造 where を公開 R15 の入口で検査

開始: 2026-11-26 02:33:03.000 UTC。I-74 §6.3/X10 の原形を、元の **same-role** の実候補で実装。親218の元 clause 0 / argument 0 の `where Check {box:'a}` は、実保持行4・実捕捉中心3から元 occurrence `[71,0]` の子219を作る。親と子それぞれで実選択候補と実 ordinary rival の完全な可視列を確認し、訪問した根／field の K2 を元の graph 上で検査する。候補順を逆にしても同じ元の子。distinct-role fixture への置換や Tape367 の変更はなし。

1. `OriginalLocal` は同じ State の source、capture、実保持行、候補・raw 条件を持つ局所規則。任意の State・Request・辞書で `Classifies R15` が選択したら、任意の適合モデルに元の `DictionaryEvidence` を与える `dictionary_sound_R15` を証明。
2. 新しい `.originalStructuralWhere` witness は元の位置と有限 raw データのみ。子 Request、Event、辞書、モデル、分類結論を入力として取らない。実 `SourceTrace/WhereForest` の位置0に同じ Event を残し、support/outputs/writes が空で、表示の tree と verdict が厳密一致したときだけ通る。
3. 外側を変えない `check_sound` を維持。旧 R14 witness は任意の入力で同じ Bool。旧 R13 名称側の trace は同じ Event・木・writes・producer needs のまま写し、R14 の endpoint は既存の独立した規則を保持する。

## 検証

- 4つの追加 Lean source/Audit と末尾2 import のみ。exact Git bytes から追加 production 2件を再コンパイル。Lean 4.35.0 `--trust=0 -DwarningAsError=true`、production-only `LEAN_PATH`、各 Audit を空の別 cwd、peer Audit olean なしで実行。
- **新2本 + 旧回帰4本が exit 0**、標準公理のみ43表示。実 same-role 宣言の選択・独立適合モデル、可視並び順変更、元保持行、元の子／Event、誤った保持行、表示子の変更と欠落、異なる verdict、余計な writes、実 field K2 を検査。新入口で元の R14 端点と固定出力を実行して通過、改変写しは不通過。
- 追加の未登録対照として、旧 root K2 の original witness、旧 named sibling も新 `.previous` 経由で実行と分類を検査（各2件・標準公理）。[任意の受理済み wire の元 row 同一性](../design/dots-cycle-431-c15-address-certificate.md) blob `e501fba7a208136f3672e5468ae997732e1d1a1a` も独立 strict 検証（4件）。汎用 allocator の一意性を主張しない。
- 既存 R14 や固定声明・凍結ファイルは不変更。Rust・全体ビルド・網羅性・停止性、一般 where や関連型出力は検証していない。非対応で `false` の経路は新しい言語拒否ではない。

技術 pin `04be83be1baa9d1426f3598cb7a7c0ecf740f9cf`、[exact replay](../design/dots-cycle-431-c15-exact-replay.md) blob `34ad3cc2d79a99c9233de958f34ee1fe75a3faf1`。最終 integration `9ef86984658f7d5b152d0b56685033d7dc940e0b` は対象5 path 中 0 件一致で未採用。integration の C はまだ8行。

**work/dots-main の C の残り: 7 行（C16–C22）。**
