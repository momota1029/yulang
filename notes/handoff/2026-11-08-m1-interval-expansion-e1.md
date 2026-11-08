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
