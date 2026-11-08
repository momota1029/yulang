# 中心なし区間の有限 role 展開: 正の構成 (2026-11-08)

更新契約 `6c346dace` に従い、readiness の境界反例で止めず、受理された宣言に対する
実有限展開と dictionary の正の定理を構成する。以下は full B4 E1 の代わりと称するものではなく、
その区間展開核を作る作業記録である。

## 定義の根拠

- `spec/06-roles.md` 6.3: 全 `where` は、捕捉後の合流を含めても head より小さく、変数の
  出現回数を増やさない。これを利用時の仮定へ移さず、宣言時の実有限検査から導く。
- `notes/reference/2026-06-02-role-system-yulang2.md`: candidate の照合で得た同じ束縛を、
  impl の全 prerequisite に適用して再び解決する。途中で異なる実引数を選ばない。
- `notes/reference/2026-06-06-invariant-type-sandwich-yulang2.md`: 引数は lower/upper の二境界で、
  中心は保存しない。構造が共変なら両 endpoint に同じ template を別々に適用する。
- 有限構文と宣言検査は既存 `CommonRoleCaptureNormalization.Form` と
  `CommonRoleStablePaterson.check` を再利用する。Form の局所正規化は idempotent join の段階であり、
  full nominal / record residual / merged row の全正規化と同一視しない。

## 1. 全 where の両 endpoint に対する安定な下降

`CommonRoleIntervalPaterson.every_where_decreases`:

> 任意の既存有限 `Declaration`、その実 `CommonRoleStablePaterson.check = true` の証拠、
> 任意の元 endpoint 二つを返す束縛、元 `requirements` に含まれる任意の where 条件について、
> 同じ束縛を両 endpoint に適用し既存の局所正規化を行った child 引数列の両側合計サイズは、
> 同じ宣言 head の両側合計サイズより真に小さい。

lower と upper は異なってよい。区間の中から点を選ばず、独立した二つの境界置換に既存の
全代入下降定理を適用する。`expand` は元 `requirements` 全列の map であり、role ID・順序・
重複する where・共有 endpoint 束縛をそのまま保存する。
任意の rank law、candidate callback、solver success、semantic point matcher は前提にしない。
ここで全称化する束縛関数は証明の入力であり、返却 dictionary に無限関数を保存する設計ではない。

検証: 対象 warning-as-error build（122 jobs）成功。
主要定理の直接 `trust=0` 監査は `[propext, Quot.sound]` のみ。

## 残る接続

有限 candidate capture、全 where の有限 dictionary 構築、分類との独立 iff を続ける。
繰り返される head 変数に異なる区間が来る場合は、元規則の lower join / upper meet と
交差制約を通常機械へ戻す必要がある。単に二 endpoint の構文一致を要求する matcher を
一般の role 照合の定義にしてはならない。構造が未確定なら pending のまま保持し、
後の source / recollection の義務を明記する。

## 2. 元 endpoint 対を読む実有限 structural capture

`CommonRoleIntervalCapture.capture_arguments_exact`:

> 任意の元有限 Form head 列、任意の元 endpoint 対列、任意の有限束縛表について、実
> `captureArguments` の返却がその束縛表であること iff 独立した `CaptureArguments` 導出が
> 同じ head と同じ endpoint 列の対応位置をたどり、その表を元順序で集める。

`Capture` は plain 変数で二つの元 endpoint subtree を一つの対として捕捉し、int / pair /
tick の一致する実構造を再帰的にたどる。型の同値を解いて代入を選ぶ規則はない。
table は有限 `(変数名, lower/upper)` 列であり、点や semantic callback を保存しない。

展開核の有限 `supported` 検査は、head が int/pair/tick/plain variable の構造であり、
全 head における変数名列が `Nodup` であることを検査する。**繰り返される head 変数と
join head は outside/unsupported** として扱う。これは一般 role 照合の拒否や pending と
同じではない。前節の pending は full source scheduler の未実装義務を指すもので、
この local kernel の結果名には使わない。

`bound` は head と全 where に現れる名前が有限表に存在することを実検査する。
total lookup に記した fallback は、この検査後の template から観測されない。
元々の一般ルールでは繰り返し捕捉を lower join / upper meet と交差制約で和解させる必要があり、
その拡張を literal endpoint equality で代用しない。

検証: 対象 warning-as-error build（123 jobs）成功。
主要 capture 定理の直接 `trust=0` 監査は `[propext, Quot.sound]` のみ。

## 3. 外部 oracle を持たない finite candidate scan

`CommonRoleIntervalCandidates.scan_exact`:

> 任意の有限 declaration 列、任意の元 endpoint 対を持つ goal、任意の有限 candidate 列に対し、
> 実 `scan` がその列を返すこと iff 独立した `Selection` 導出が、元 declaration 列の全要素を
> 同じ goal で検査し、同じ有限 endpoint 捕捉表を持つ候補を元順序で残す。

両境界を既存の局所正規化に通し、実構造から捕捉し、head と **全 where** の全使用名を有限表で
検査し、その同じ二境界置換で head を replay する。主張は linear structural kernel に限定する。
repeat-variable head や join head は実 grammar check により outside となる。
rigid head 位置の未確定 endpoint、片側だけ異なる構造、捕捉／replay に足りない情報も outside であり、
意味論的な `noImpl` や source の pending として誤報しない。
plain variable の head 位置は任意の元 endpoint 対をそのまま捕捉するため、両境界が異なる場合や
整合していない場合も構造捕捉自体は成功する。この成功は通常の区間整合性を証明しない。
`Rejects` は異なる role/arity、または両 endpoint が揃った rigid constructor の衝突だけを扱う。

`all_where_bindings_exist` は、受理された候補の任意の元 where に現れる任意の名前について、
実 lookup が元有限表の endpoint 対を返し、total extension の fallback を使わないことを証明する。
`accepted_child_decreases` は、実宣言検査と同じ候補の endpoint replay から、元 goal の
二境界サイズに対する child の真の下降を導く。replay は点の同値ではなく、元二境界の有限構文確認である。

検証: 対象 warning-as-error build（124 jobs）成功。
主要 scan と下降補題の直接 `trust=0` 監査は `[propext, Quot.sound]` のみ。

## 4. 実検査から停止する全 where 展開と独立 traversal

`CommonRoleIntervalExpansion.run_tree_exact`:

> 任意の有限 declaration 列、任意の元有限 endpoint goal、任意の有限出力 tree について、
> 実 `run` がその tree を返すこと iff 全 declaration が既存の安定 Paterson 検査に通り、
> 独立した `Traversal` が同じ registry、同じ元 goal、同じ tree を導く。

`run` は宣言列の有限検査を内部で実行する。`expand` の停止は、選ばれた実候補に対する
`accepted_child_decreases` から導く。呼び出し側が fuel、rank law、探索成功、全子の成功を
与える必要はない。registry の同一 declaration 値の重複は既存 `Roles.distinct` で除き、
異なる declaration 値は別候補として保持する。

出力は **構造展開 trace** であり、typed role dictionary の完成ではない。唯一候補の node は
元 goal、その候補の元 declaration と有限 endpoint 束縛表、および元 `requirements` の
**全列を同じ順番で**再帰展開した children を保存する。where の重複も残る。
`outside` / `noHead` / `overlap` は明示的な leaf として残し、兄弟を捨てない。
候補 head が複数ある場合は where を試す前に `overlap` とする。これは head 段階の分類である。
未規定の outside と兄弟 error の優先順をこの核で決めないため、単一のエラーへ畳み込まない。

`Traversal` は独立した有限構文の `Selection` と全子の導出を使い、`expand` 自身を前提にしない。
`outside` はこの有限 capture 文法で全 declaration を分類できないことを表し、一般言語の
pending や noImpl と同一視しない。たとえば rigid head `int` と `(int, int | pair int int)`
の組は、一般機械では上界を狭める余地があるため、この核は noHead とせず outside に置く。

任意 endpoint は不整合でもよい。tree に元 goal と捕捉表が残ることは、通常の
`lower <: upper` が成立したことを意味しない。次段で、全 node と全捕捉区間の整合性を
既存 `.check` 制約列へ返し、その Models iff を証明する。Parameters に条件を隠さない。

検証: 対象 warning-as-error build（125 jobs）成功。
公開 run の直接 `trust=0` 監査は `[propext, Quot.sound]` のみ。

## 5. 全 node の普通の区間制約を保持する

`CommonRoleIntervalExpansionChecks.constraints_exact`:

> 任意の endpoint 解釈、任意の元有限 trace、任意の template value assignment について、
> 実 `constraints trace` の Models iff 同じ trace の各元 goal・各捕捉表・全 where 子で
> lower <: upper が成り立つ独立した `Consistent` 判断。

`original_goal_checks` は、元 goal の全 endpoint 対の self check が実列に入ることを示す。
唯一候補の全子だけでなく、overlap leaf の全候補に記録された元捕捉表も保持する。
構造 capture の成功から区間の整合を勝手に導くことはしない。

検証: 対象 warning-as-error build（126 jobs）成功。直接 `trust=0` の公理は許可リスト内。

## 6. 独立した有限 dictionary と実 preparation の iff

`CommonRoleIntervalDictionaries.complete_iff_dictionary`:

> 任意の有限 declaration 列、全宣言の実 Paterson 検査通過、任意の元 endpoint goal に対し、
> 実展開の `complete` 検査が true iff 同じ元 registry と goal に対する独立 `Dictionary` が存在する。

独立 dictionary は各 head で元 `Selection` の唯一候補と、元 `requirements` の全 child dictionary を持つ。
実抽出は `accepted_child_decreases` による停止再帰である。既存 `RoleDictionaries.Plan` への
`erase` は declaration identity、全 where の順番と重複を保持する。

`CommonRoleIntervalDictionaries.elaborate_prepared_exact`:

> 任意の有限 declaration 列、元 goal、出力 plan と trace について、実 `elaborate` が
> `prepared plan trace` を返す iff 全宣言が実検査を通り、独立 dictionary の erase/trace が
> その同じ plan/trace に文字どおり一致する。

`elaborate` 自身が宣言検査、停止する全 where 展開、complete 検査を実行する。
成功・fuel・子の成功・意味的な点置換は呼び出し側の仮定ではない。
ただし **prepared は最終 selected ではない**。ordinary interval constraints は別に戻され、
その solver 成功と full source typing はこの theorem の結論に入っていない。
failure leaf は incomplete trace に保持し、一般 source の pending/rejected に読み替えない。

検証: 対象 warning-as-error build（127 jobs）成功。主要 iff の直接 `trust=0` 公理は
`[propext, Quot.sound]` のみ。

## 7. 元 source slot と同じ ordinary graph へ全制約を返す

`CommonRoleIntervalDictionaryCompilation.compile_trace_exact`:

> 任意の元 slot 命名写像、元 ordinary atom 列、独立した元全 slot assignment、元 trace について、
> 元 ordinary Models と trace の独立 Consistent の連言 iff、実 compiler に
> `original ++ generate name trace` を渡して得た同じ graph にモデルがあり、その readback が
> 全元 value/row assignment に文字どおり一致する。

`compiled_reflects` は任意の実 graph model（正則な Common realizer も含む）から逆を示す。
命名写像は既存 slot の識別であり、head capture を選ぶ semantic callback ではない。
同名は元と同じ slot を読む。既存制約・row・共有を失わない。
**graph はまだ subtype edge を持つ**。このコンパイルの exactness を、自由 parameter に
条件のない solved family の回収や、区間 resolver 全体の E1 と呼ばない。

検証: 対象 warning-as-error build（168 jobs）成功。主要 theorem の直接 `trust=0` 公理は
`[propext, Quot.sound]` のみ。

## 8. 確定した closed record の payload 検査と実 residual の接続

`CommonRoleClosedRecordInspection.inspect_exact` は、任意の元有限 field spine 二つと
任意 assignment について、実有限 inspector の返却 atom が成立 iff 同じラベル集合かつ
元 first-field-wins payload から作った Common closed record の全 depth subtype が成立することを示す。
元 spine に隠れた重複 field があっても、両側とも元 `lookup` の最初の payload を使う。
異なるラベル集合はこの same-spine 部品の **outside** であり、一般 record subtype の不成立とは言わない。

`CommonRoleClosedIntervalInspection.reconcile_exact` は、任意の元 lower/upper field 対列二つと
任意 assignment について、実 `reconcile` が満たされた atom 列を返す iff 同じラベル集合であり、
両方の self check と両向きの cross check が成り立つことを示す。
中心や canonical actual type は保存・選択しない。

`CommonRoleClosedResidualInspection.inspect_generation_exact`:

> 任意の元 labels、元 endpoint-field spine、要求された endpoint-field spine、任意 assignment に対し、
> 実 `capture labels fields` を検査した payload atom が成立 iff、計算された residual と要求の
> ラベル集合が同じで、既存 `CommonRoleClosedIntervalRecordGeneration.generate` が同じ元
> residual と要求に対して生成した全 ordinary checks が成立する。

引き算の答えを別の自由入力として渡さず、既存の canonical subtraction を実行する。
未知の spine を任意の row で埋めず、この部品は既に決まった閉じた spine に限定する。

検証: 各 packet の対象 warning-as-error build は 199 / 200 / 201 jobs で成功。
各主要 iff の直接 `trust=0` 公理は `[propext, Quot.sound]` のみ。

## 9. 元 shared endpoint slot での実 ordinary grammar

`CommonRoleClosedResidualSlots.inspect_all_exact` は、任意の有限 comparison 列と任意の
元全 slot assignment について、各 lower/upper endpoint が元 slot を参照する実 inspector の出力が
成立 iff、**全元 comparison** の計算した canonical residual と要求が同じラベル集合で、
同じ二境界に対する独立四方向 compatibility が成り立つことを示す。
endpoint の意味は任意の Common type（正則型も可）であり、有限木を意味論の仮定にしない。

`inspect_all_grammar` は、任意の comparison 列と実返却 atom 列について、既存 solved worklist の
三つの構文条件 `GoodAtoms` / `WidthAtoms` / row-shape `GoodAtoms` を内部で導く。
payload 比較を元 variable-slot 間の ordinary atom に下ろすため、negative `exactEmpty`
をそのまま既存 solver へ渡す障害を、この明示した局所領域では避けられる。
**実 `solveAll` family・元 source clause・全 source generator との接続 theorem はまだ追加していない**。
これは grammar までの部品であり、B4 全体を solved と主張しない。

検証: 対象 warning-as-error build（208 jobs）成功。
`inspect_all_exact` / `inspect_all_grammar` の直接 `trust=0` 公理は `[propext, Quot.sound]` のみ。

## 10. 復旧時点の正確な残りと、最新の仕様決定

**B4 の更新済み全体 E1 は未完。** 今回閉じたのは、明示した finite linear structural fragment の
下降・全 where 展開・独立有限 dictionary preparation と、その元 interval obligations の graph 生成、
および determined closed record residual の普通の payload 検査である。

残る接続は次の通り。

1. 反復 head 変数を全元 occurrence の lower join / upper meet と全 cross constraints で捕捉する実機械。
   現行 `supported` は head 名の `Nodup` を要求する。反復変数を endpoint の構文一致や
   existential point matcher で代用せず、より広い endpoint 表現と実合流後の下降を証明する。
2. 現行 finite Form から、宣言別 variance を持つ nominal・共変 payload 合流・record の残りを含む
   元 source head/where 表現へ拡張する。既存 record residual の局所下降と今回の検査は、まだ
   candidate scanner に組み込まれていない。現行 replay の literal endpoint equality は
   linear structural fragment の再構成に限り、一般 interval reconciliation ではない。
3. 元 lower head が未確定な場合の pending、元 slot/level を保つ起床と再収集、全候補での
   K2 再帰構造 inspection 検査と拒否優先、selected/ambiguous/rejected の独立した全体 iff。
   現行 outside/noHead/overlap/prepared という局所状態を、その source 四分類と同一視しない。
4. 全 where・associated constraints・元 ordinary constraints を同じ実 solver で処理した返却 family、
   **全自由 parameter** の健全性、任意の元 assignment の回収、元 source typing と辞書実行の接続。
   constraint graph の存在や返却 parameter 上の residual predicate を E1 と取り違えない。
5. 上を一つの元 source resolver に接続し、実 declaration/候補検査から停止を導く。
   利用側へ任意 rank、fuel、support、子成功、typed plan の成功仮定を移さない。

最新の確定事項は `spec/06-roles.md` の決定節を優先する。古い設計本文に残る「未決」は
現在の問いとして扱わない。

- 更新済み interval 全体 statement は承認済みで、旧 point theorem を書き換えない。
- 共変 `box` は合流後に一つの payload を持ち、head 変数がそれを丸ごと捕捉する。
  不変 `list` の矛盾する合流は構築時に拒否する。nominal alternatives の有限 cover 案は不要。
- K2 は **拒否が曖昧性・選択より先**。候補順や安全候補の個数に依存させない。
- variance は承認済み候補 1。関数 wrapper で即時走査を切り、使用・極性自体は消さない。
- **保留境界は不変な型引数だけ**（ユーザー決定 commit `4284375cf`）。共変 `box` は保留せず、
  `box user_id` から必要な `box int` へ後の境界で構造 cast する。これはもう確認待ちではない。
- record tail は元の確定 spine から明示 field を引いた結果。未確定なら pending を保持する。
- **K1 は宣言時の追加拒否をしない**（ユーザー決定 commit `dc6e7b304`）。receiver の無い
  member は従来どおり一つ以上の引数を取る関数であることだけを保ち、role 引数が引数型・
  戻り値型に現れるかを追加検査しない。型が分かった後で同じ role 制約を解き、
  一般化できない未解決制約は §6.3 と同じくファイル終端まで保持する。
  解決の手がかりが最後まで無ければその時点でエラーにする。これはもう確認待ちではない。

今回 B4 が追加した新しい仕様質問はない。上の残りは証明・実装の未接続であり、
既に確定した意味論を再質問しない。B2 の既存二問など、別目標の未決はこの記録で解消した扱いにしない。
