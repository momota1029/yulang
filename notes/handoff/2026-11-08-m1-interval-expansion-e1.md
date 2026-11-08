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
