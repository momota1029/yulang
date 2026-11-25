# C416 / I-74 C08 / X6: 実際の同一タグと二つの plain binder

| 条件 | 実装と検証された範囲 |
|---|---|
| (a) 新しい局所規則と健全性 | R8 は、実際に宣言された唯一の `R :{tick 'a,tick 'b}` が元の一つの point `R :{tick int}` に当たり、二つの名前を同じ実 payload の point に捕捉する選択のみを追加。`dictionary_sound_R8` は先行規則を含む R8 全体を同じ State の全 fitting model で示す。 |
| (b) 実行可能な有限証人 | `PlainWire` は original/variant/int/join 行と宣言の添字および根の raw K2 検査データ。payload の値・選んだ二つの arm・モデルや検査結果を受け取らない。全可視候補を確認し、実 origin 一つ・同タグの raw variant 行一つ・実 int・元根の保持済み自己 join を照合。 |
| (c) 同じ契約 | `PlainMerged416.check_sound` は同じ Problem の正確な選択・辞書・空 where と書込みの報告を全 fitting model で保証。従来の入口は不変。元の declaration ID、序数、タグ、二つの実 binder 名は別証人で付け替えられない。 |
| K2 と統合位置 | 正規化した head は同タグの一つの構造だけ検査し、二つの binder の payload を内部まで開かない。raw graph をそのまま読む。自己 join 行で alias、raw 構造観測、K2、根の実行検査、モデル集合は変わらないことを別証明。これは保存性を示す補題で、実行時に元 State へ行を足していない。 |
| 既存 carrier の限界 | 元構文を読む `SourceHead` はこの head について実 join 行を必要とする（nominal 経路に変換不可）。型意味はその行なしでも同じ冪等な merge。行なしで同じ型に適合する実例は用意できるが、固定の元 head の実導出がなく checker は false。受理すべき構文一般が失敗するという言語結論ではない。 |
| 対照 | 単独 X6 と、元の順序を変えた例は true。偽の二 arm、同一型の別論理名、元 join 行なし、異タグ、宣言 role が fallback しかない、根 K2 の新分岐、ground 競合はいずれも false。根 K2 の旧診断は true。ground 競合の実判定は C09 なので未対応のまま。 |

[仕様 6.3](https://github.com/momota1029/yulang/blob/efb4a2de77af97ac26192fc5abfe651ef3e982f9/spec/06-roles.md#L111-L117)。固定実装 `469bce31ca2b00cd6ce5bfc0cdd4383736df0fca`（Lean tree `d25f04c174965a212b0b9f84308c82f92e0412f3`）。

固定 Git 実バイトの Lean 4.35.0 strict replay は 10/4、21/10、68/45 の三範囲すべて終了コード 0。C416 の 39 宣言は標準公理以内。
C408 を基準に C409–C416 の公開範囲 68 モジュール・独立監査 45 本を別に厳密再生し exit 0。最新入口のローカル結合試験は旧例を含む 11 正例 true・6 対照 false。同じ例の元行・binder 順と宣言位置を組み合わせた 24 件では元 payload を保持し、誤った単一添字 25 件はすべて false。別 arm の値が同じになる実適合モデルも作り、型の一致では別名を捕捉できないことを確認しました。いずれも全体ビルドではありません。
