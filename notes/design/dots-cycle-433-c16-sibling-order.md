# C433: where 子を並べ替えても元の名前つきターゲットは変わらない

`checked_where_permutation_keeps_lexical_binder_targets433`: 同じ宣言の clauses だけを置換し、capture と clause/式 ID に対する placement を維持する。実 `DeclarationChecked` の元 clause ID 一意性から、元の binder を産んだ clause の `find?` が置換で変わらないことを証明。そのため出力先を第何子かから割り振り直さない。

`same_source_where_clause_keeps_demand_under_permutation433`: 同じ元 clause の role、匿名 input、名前つき fixed output を保つが、元 occurrence の末尾は元の索引から入替後の索引に変わる。実例で Container と別 role の clause を入れ替えた。別 role 側の fallback は 70 で producer の target 4 と異なるが、両順とも同じ名前つき target 4 を与える。両宣言は実チェックを通る。これは発行する元 request の順の話で、solver 収束、候補が同じ順で選び直されること、R16 の一般兄弟対応ではない。
