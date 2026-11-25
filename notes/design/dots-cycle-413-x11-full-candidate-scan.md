# C413 / I-74 C05: 実候補を全部保持する record K2

仕様 §6.3 X11: `Check {box:'a}` と `Check {box:{next:'b}}` が同時に見える。外側の実 point・元 raw row を元要求に照合し、同じ box field の実 operand を得る。変数だけを受ける候補は元 head の完全な `SourceHead` の証拠（元行への capture の代入）を持ち、その内側は訪れない。構造のある候補だけが元 pattern の実 field に入る。そこで raw K2 なら、他の一致が一つでも複数でも選定・曖昧より前に拒否。親は raw root cycle ではない。

- `MixedTape` は全 visible list と索引が同じ。nested 一つと他の実 binding-only 全部を保持。nested の ordinal は元の順から計算し、witness が候補や結果を決めない。未対応候補は無視せず false。候補 ID は相異なり、実 role と両方の元 declaration を検査する。
- 新規 `mixedRecordLocal413` は head 側の rejected-only `other`。旧 R4 に足した R5 の `DictionarySound` の型は固定。既存 checker をそのまま呼ぶ旧 branch と有限 raw data だけの新 branch。 `check_sound` の対象・exact report・全 fitting model 証拠は同じ。where 需要や擬似的な親 K2 は作らない。
- この途中確認では core・元 head の真正な rival match・先の報告の運搬・root and full scan・rigid site の raw K2・fixed check_sound が strict。具体的な X11 両順の実行試験と priority の追加監査を次にする。
