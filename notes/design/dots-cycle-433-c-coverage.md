# C433: C16 の公開 Lean 検査と残りの C

この周に閉じた C の行: C16（`dictionary_sound_R16` / `WhereAssociated432.check_sound`）。対象は spec/06-roles.md §6.3 の実例 `Wrap(list 'a, out = list 'b) where Container('a, item = 'b)` の、元の一つの where 子を持つ形。元の関連型出力 slot と固定 row が既存状態に保持されている場合を扱う。複数の兄弟の一般ケースは、この行を閉じるための I-74 の狭い受理例に含めない。

- 独立局所規則: 既存 R15 と元の関連型読みを持つ指定の局所規則を結合。任意の適合モデルで、実際に選ばれた元の子から親の lexical binder と固定型出力が意味を持つ。
- 実行版: 新たな証人は元の行番号・宣言序数と有限 K2 検査データだけを渡す。親/子 request、実選択結果、辞書、型の意味を証人には含めない。同じ State から元の型つき RHS、固定 row、元の where occurrence を読み返し、exact な表示木・辞書・書き込み列を照合する。
- 保持: 旧証人での Bool 結果は全入力で R15 と同一。I-65 の `DictionaryEvidence` と `check_sound` の外形は変更しない。報告の順序は元の receipt の走査順であり、solver の実行順・順序独立性の主張ではない。出力専用変数を兄弟の匿名入力に昇格させない。
- 技術 pin: `eb15dba50001bc46a740cb1f378fd8746c84d80f`（I-74 三条件と、元の入口で実例・負例を検査）。監督側 integration の採用は別途照合する。

| 行 | 残りの対象 |
|---|---|
| C17 | 未完了出力だけが入力を支える需要は一般の保留（K2 がない場合） |
| C18 | 片付いた別需要の出力による native head の正規の裏づけ |
| C19 | 同じ名前なし引数の複数出力指定の矛盾と需要の型エラー |
| C20 | 入れ子 nominal head での宣言分散と外側 invariant 文脈 |
| C21 | 多引数・row parameter の宣言モードと元位置 |
| C22 | row-valued nominal 引数を持つ関連型 RHS の非平坦化固定行 |

**work/dots-main の残り: 6 行（C17–C22）。** 監督側が技術 pin を取り込むまでは integration の残りは 7。
