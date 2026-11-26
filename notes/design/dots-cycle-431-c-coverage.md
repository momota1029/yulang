# C431 C の範囲（I-74）

C14 は既存 R14 に統合済み。C15 は work/dots-main に公開した次の狭い実例で閉じた。実 nested record 親が §6.3 の元の `where Check {box:'a}` を使い、同じ role の一子を生成する。完全な二候補 ordinary rival、元ソース順・実捕捉・zero outputs をチェック。R15 の独立局所規則と `dictionary_sound_R15`、証人のみの `check`、固定外形の `check_sound` がそろった。別 role へのすり替えではない。

- 技術 pin: `04be83be1baa9d1426f3598cb7a7c0ecf740f9cf`
- [C15 設計と境界](dots-cycle-431-c15-original-structural-where.md)
- C15 の integration 採用は canonical report の readback と区別する。未採用の場合の統合側の残りは 8。

| 行 | 未対応 | 既存例 |
|---|---|---|
| C16 | where の関連型出力を実子から読み、親・兄弟の順と固定出力へ | 6.3 `Wrap(list 'a,out=list 'b) where Container('a,item='b)`、`Show (box 'a)` |
| C17 | 未完了出力だけが入力を支える需要は一般の保留（K2 がない場合） | 6.3 `R (list 'a) where R('a,out='b)`、`Container/Wrap/P` |
| C18 | 真に片付いた別需要の出力で native head を裏づける（下端への独立 authored Origin なし） | 6.3 `Container/Wrap/P` の再開条件、C406 と C407 の固定 carrier の差 |
| C19 | 同じ名前なし引数の複数出力指定に矛盾があれば、その需要の型エラーを報告 | 6.3 `P int` の `R(out=int), R(out=:tick int)` と nullary `impl R` |
| C20 | 入れ子 nominal head の宣言分散と外側の invariant 文脈を継承 | 6.5 `list (list int)` / `list (list float)`（X14）、X17 と X19 のモード。型比較だけでは辞書 check を閉じない |
| C21 | 多引数／row parameter の宣言モードを正本で確認して本来の位置で照合 | 6.2 `impl Add (ref _ int)`・[4.6](../../spec/04-types.md) `ref 'e 'a`。X21 の rank-2 自体は B3 |
| C22 | row-valued nominal 引数を持つ関連型 RHS の固定行を平坦化せずに検査 | 6.1/6.3 の関連型右辺・4.6 の row 引数。両者を組み合わせた既存の直接例は未確認なので最後 |

**work/dots-main の残り: 7 行（C16–C22）。**
