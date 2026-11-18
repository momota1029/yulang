
## 付録：独立した検証probe（数学module185宣言の集計外）

### DriverProbe
- `changesAfterInstall`: 239の有限stateを引数に取り、remainingが空でなければ既存5facts、空ならbasis外のinstalled999を提案する、意図的に不正なobserverの定義。
- `initial_progress`: このobserverのnextは具体initialStateから具体finalStateを返す。source一般の一歩ではない。
- `later_unsupported`: 同じobserverのnextは具体finalStateでinstalled999の内部errorを返す。
- `no_whole_run_rollback_claim`: 同observerのsettleは具体initialStateからそのerrorを返す。2つのnext結果を使う。中間書込みがあった事実と、純関数の最終返値がerrorだけであることを区別する。
- 3つの#evalはI45/239の終点remaining=0、不正observerのunsupported件数=1を表示する煙試験。証明ではない。

### OutputCoverageProbe
- `atom`: 252の具体snapshotのslot2だけをatom0へ写す部分写像。他slotはnone。
- `facts`: owner0のinstalled、lower/upper atom0、binder0/1という具体5facts。
- `actual_decoder_accepts`: 252の実packet reportをcompileすると上記factsを返す。report_exactを使う構文の計算定理。
- `checked_write_accepts`: 上記factsを同じbasisの初期有限stateへchecked commitするとdoneを返す。basis内閉包と差分だけを保証する。
- `accepted_report_not_output_certificate`: 同じ実reportの構文受理、実prepared Frame、具体replace bottom assignmentの初期journal Models、同assignmentでのpacket Holds不成立を同時に示す。既存258のframe_not_packetを利用する。252用のfinite fact意味表や公開モデル同値を新たに主張したものではない。
