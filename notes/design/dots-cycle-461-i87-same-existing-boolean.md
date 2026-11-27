# C461 / I-87: 同じ既設 C459 field wire の Bool を保存する

旧 `check_full_homogeneous459` の既設 `.fieldK2` 分岐と、元の有限 header key・raw hop・escape・terminal の cycle wire が同じ条件のままの構造 reader を比較した。旧コードは編集しない。

- 全ての FullProblem / report / 旧 FieldWire について、実の旧 Bool は「同じデータに中立な構文位置を足して実行したとき、同じ report と **既存 raw true stamp** が返る」に等しい。成功時に新しい wire を探すだけでなく、同じ header 原 key、全 raw tickets、cycle ticket を両方向に元に戻せる。関係する旧 reader と新 reader は source と raw site を固定し、report は実読取の結果から得る。
- true stamp は旧 policy の実 inline/use アドレスから出る。generic receipt が出ただけでは true にしてはいけない。実 named-only 経路の false stamp や、不適格 nonpoint 起点、違う role / issuer / clause / 訪問位置は実対照で区別した。新しい診断をインストールしたのではない。
- 旧のこの分岐に必要だった本物の元 source 条件は、有限欄と実元 head/where の全部の捕捉に対する安定性に分けた。実旧 provider で分解前後の exact Option は全キーで同じ。他の `.previous` 分岐の一般化、一般の G04 source がこの eligibility と原 raw scope を供給すること、一般の有限性/判定法、臨時の raw graph 変更・残余 join の訪問は未証明。G04 は未完。
