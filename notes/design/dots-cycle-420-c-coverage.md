# C420: I-74 完全性の一覧

**この周に閉じた C の行: C12（`dictionary_sound_R12`、`RoleDefault420.check_sound`）。** 該当名の明示 RHS がなければ、実 role が宣言した位置 0 の既定値を元の一点引数全体から読み、元の B6 と固定先を照合する。未対応の false は言語の拒否ではない。

I-65 健全性の残りではなく、仕様例に対する適用範囲を数える。C01–C11 は [C419 の表](dots-cycle-419-c-coverage.md) を継承。C12 は本一覧時点で work/dots-main の検証。

| 行 | 形と期待される結果 | 仕様または既存例 |
|---|---|---|
| C01 | 既知の名前付き再帰 nominal は本体を開かず名前で選ぶ。型引数 0 の named head を 1 引数照合、singleton、空 where・出力、同じ元 name 読みで両端点（X12）。[完了と検証範囲](dots-cycle-409-c01-verification.md) | [6.3 K2](../../spec/06-roles.md)、`enum tree` / `impl Show tree`、X12 |
| C02 | 元の単一候補の不変 nominal `list 'a`。本来の一引数の実点を捕捉し、再帰 payload を展開せず選択。空 where/出力の X8。[完了と検証範囲](dots-cycle-410-c02-verification.md) | 6.3 `Len (list 'a)` / `len [loop 1]`、X8 |
| C03 | 実 where 子へ降り、その子の根 K2 と親・子の発現位置を記録。[完了と検証範囲](dots-cycle-411-c03-verification.md) | 6.3 `Show (list 'a) where Show 'a` / `show [loop 1]`、X9 |
| C04 | record の nested head が実際に内部へ入った箇所で K2。[完了と検証範囲](dots-cycle-412-c04-verification.md) | 6.3 `Check {box:{tick:'a}}`・`μ={tick:μ}`、X10 |
| C05 | 実候補を全走査し、実到達 K2 は選択・曖昧さより先。[完了と検証範囲](dots-cycle-413-c05-verification.md) | 6.3 `Check ({box:'a})` と `Check ({box:{next:'b}})`、X11 |
| C06 | record tail が未知なら保留、read の不成立だけで候補を落とさない。[完了と検証範囲](dots-cycle-414-c06-verification.md) | 6.3 `R {x:int,..'a}`、X4 前半 |
| C07 | 開いた record から既知 field を取り除いた正確な residual tail を捕捉し選択。[完了と検証範囲](dots-cycle-415-c07-verification.md) | 6.3 `{x:int,y:str} <: {x:int,..'a}` で `'a={y:str}`、X4 後半 |
| C08 | 同一 tag の plain binder それぞれに合流後の payload 全体を捕捉、単独なら選択。[完了と検証範囲](dots-cycle-416-c08-verification.md) | 6.3 `R (:{tick 'a,tick 'b})` / `R :{tick int}`、X6 |
| C09 | C08 と ground の同一 tag 候補が同じ出現・実 payload に当たり、選択なし・書き込みなしで曖昧。元 primitive `int` 観測と実到達点 K2 を確認。[完了と検証範囲](dots-cycle-417-c09-verification.md) | 同じ X6 に `impl R (:{tick int})` |
| C10 | 実一点 `R :{tick int}` の実可視二構造候補。`R :{tick str}` の根拠付き不一致を除き、plain 合流だけを選択。[検証](dots-cycle-418-c10-verification.md) | 6.2 共存規則の具体化。掲載の `Display (list 'a)` と `Display (list int)` 自体は重なる場合がある |
| C11 | 既知の二 field の一点 record に明示 B6 RHS を同じ出現・宣言順・出力順・固定先で記録し、捕捉した実 field を返す。[検証](dots-cycle-419-c11-verification.md) | 6.5 `impl Pick {x:'a,..'rest}: type out='a` の一点入力・元明示 RHS・where なし・出力一つ。6.2 の `Index str int` の `char` 例そのものではない。 |
| C12 | 要求した元の出力名に明示 RHS がないときだけ、実 role が宣言した位置 0 の既定値を元の一点引数全体に具体化する。同名の明示式は優先し、別名の明示式は妨げない。[検証](dots-cycle-420-c12-verification.md) | [6.1 の default 規則](../../spec/06-roles.md) と [10.7 RolesAssoc](../../spec/10-inference-core.md) の位置 substitution。`char` の例そのものではない。 |
| C13 | 重複 head binder は選択した後にだけ実中心どうしへ等式 | 6.3 `impl R 't 't` |
| C14 | 根拠付き両端点から record を選択、中心行は未完でも非点の捕捉を保持 | 6.3 `{x:'a,..'rest}`「中心の行に根拠がなくても選ぶ」 |
| C15 | 構造の where 引数を実構文から作り、元の子順を保持 | 6.3 `where Check {box:'a}`（X10 の原形）、変数だけの X1 とは別。正の where 子を通す例も必要 |
| C16 | where の関連型出力を実子から読み、親・兄弟の順と固定出力へ | 6.3 `Wrap(list 'a,out=list 'b) where Container('a,item='b)`、`Show (box 'a)` |
| C17 | 未完了出力だけが入力を支える需要は一般の保留（K2 がない場合） | 6.3 `R (list 'a) where R('a,out='b)`、`Container/Wrap/P` |
| C18 | 真に片付いた別需要の出力で native head を裏づける（下端への独立 authored Origin なし） | 6.3 `Container/Wrap/P` の再開条件、C406 と C407 の固定 carrier の差 |
| C19 | 同じ名前なし引数の複数出力指定に矛盾があれば、その需要の型エラーを報告 | 6.3 `P int` の `R(out=int), R(out=:tick int)` と nullary `impl R` |
| C20 | 入れ子 nominal head の宣言分散と外側の invariant 文脈を継承 | 6.5 `list (list int)` / `list (list float)`（X14）、X17 と X19 のモード。型比較だけでは辞書 check を閉じない |
| C21 | 多引数／row parameter の宣言モードを正本で確認して本来の位置で照合 | 6.2 `impl Add (ref _ int)`・[4.6](../../spec/04-types.md) `ref 'e 'a`。X21 の rank-2 自体は B3 |
| C22 | row-valued nominal 引数を持つ関連型 RHS の固定行を平坦化せずに検査 | 6.1/6.3 の関連型右辺・4.6 の row 引数。両者を組み合わせた既存の直接例は未確認なので最後 |

**この一覧で追う残りは 10 行（C13–C22）。** 次は C13: head に同じ binder が複数回現れる場合、選択後にだけ元中心どうしへ等式を足す。

[C407 の初期 8 分類](dots-cycle-407-i73-coverage-list.md) は順に C10、C15、C16、C18、C20–21、C06–09/C14、C22、C17 に展開した。C380 の横断的な残りを加算しない: S01–03→C01–10/C17–18（同じ実導出・全候補・K2）、S04–05→C01–08/C13–14/C20–21（head・捕捉）、S06–09/S13bbba/S13bbbb→C11–12/C15–16/C19/C22（元本文・固定先・実保持）、S10–12/S13 の親→各行の元順の木・一つのモデル・exact report。S13a/S13ba/S13bba は二重計上しない。S07 の物理 release/grant は、それを読む証人の照合だけ（I-67）。

閉鎖条件: (a) 正しい追加局所規則と `DictionarySound Rₙ₊₁`、(b) 同じ実例に実行可能な check の追加分岐、(c) 同じ報告と同じ State の全 fitting model の `check_sound`。既存分岐を変えず strict Lean で監査する。solver に証人を作らせる NoFalseRejection は別段階。
