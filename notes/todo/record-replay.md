# Record / Replay TODO（決定的記録再生）

出典: notes/design/2026-07-02-parting-assessment.md §1（Claude Fable 5、ユーザ承認済み）。
関連正本: notes/design/2026-07-02-host-act-ffi-decisions.md（v2）。

## 目的

プログラムの一回の実行を記録ファイルに落とし、host なしで完全再生できるようにする。

- バグ報告 = 記録ファイル。再現手順の文章が不要になる。
- 本番サーバの事後検死: 落ちた実行を手元で何度でも再生する。
- golden fixture: 記録ファイルをそのまま regression test にする。

## なぜ成立するか（前提の確認）

次の三つが揃ったので、実行の非決定性は一本の漏斗に集約されている。

1. プログラムは unit を返す（v2 §0）。値はすべて effect で外に出る。
2. すべての host 由来の非決定性（file / net / server / clock / random）は
   host act registry を通る（v2 F2）。
3. state は純粋継続スレッディングで、言語内部に隠れた乱数源・時刻源がない。

したがって「registry を通過した operation の列とその resume 値」が
実行を一意に決定する。

## 最重要・時間制約のある一手

**registry / manifest の設計に、operation instance の識別子を最初から含める。**

- 各 operation perform に単調増加の列番号（sequence number）を振る。
- multi-shot resume（accept / undet 交差）で分岐した各世界に分岐 id を振り、
  列番号は (分岐 id, 分岐内連番) の組にする。
- これは record/replay を実装しなくても registry 実装時に入れておく。
  後付けは全 host act の再配線になる。

2026-07-03 現在、前提の一部は実装済み:

- compiler-produced host manifest は `hash`、operation `column`、決定的
  `symbol` を公開し、`debug host-act-manifest` と release smoke で固定している。
- Evidence VM scheduler の operation instance は
  `branch_id` / `parent_branch_id` / 分岐内 `seq` を持つ。
- suspended child spawn record は `parent_branch_id` / `child_branch_id` /
  parent-local `resume_ordinal` を返す。
- runtime host registry の resolved operation は manifest 由来の
  `act_id` / `operation_id` / `column` / `symbol` を保持する。

これは record / replay 実行モードの実装ではない。次の実装では、この識別子を
runtime host registry の全 perform 経路で発行し、記録ファイル / replay host /
wire codec へ接続する。

静的 route 昇格（notes/design/2026-07-02-static-route-promotion-plan.md）で
cert 検査を消した direct call についても、record モードでは列番号の発行だけは
残す必要がある。**direct call の高速化と記録可能性はトレードオフになるので、
record は実行モード（record / normal / replay）として分ける**。normal モードに
記録コストを乗せない。

## 記録フォーマットの素描

```text
header: { program hash, std hash, manifest hash, 開始時刻(記録用メタ) }
entry:  { branch_id, seq, act_id, op_id, resume_value (wire encode) }
branch: { parent_branch_id, parent_seq }   -- 分岐の系譜
```

- resume 値の encode は manifest の型レイアウト（v2 F2/F4）をそのまま使う。
  wire codec の最初の本気の利用者が replay になる。
- host 型（v2 F5、不変）の値は encode できないので、記録には
  「host 型を返す operation の再実行」か「不透明値の snapshot 化」の
  どちらかを選ぶ必要がある。first slice では host 型を返す op を
  record 非対応として明示的に弾く（黙って壊れない）。

## Replay の意味論

- replay host は registry の代わりに記録ファイルを引く。
  (branch_id, seq) が一致する entry の resume 値を返す。
- 記録と食い違う perform（列番号のずれ、op id 不一致）は
  即座に構造化エラー（「replay 逸脱」）で止める。程度の再現は狙わない。
- program hash 不一致の replay は既定で拒否（--force で緩められる）。

## First slice

1. registry 実装（FFI 指示書の実装順 2）に列番号と分岐 id を含める。
   - 2026-07-03: host manifest 側の `hash` / `column` / `symbol` と、
     scheduler 側の branch-local operation instance id は unit / CLI /
     release smoke で固定済み。resolved runtime host operation も manifest
     identity を持つ。未着手なのは、runtime host registry の全 perform 経路での
     instance 発行、record mode、replay host、記録フォーマット。
2. record モード: console + file だけを対象に、CLI `yulang run --record out.yrec`。
3. replay モード: `yulang run --replay out.yrec`（host act 全 deny + replay host）。
4. fixture: 乱数と時刻を使う小プログラムを record → replay で stdout 完全一致。
5. undet を含むプログラムの record → replay 一致（分岐 id の検証）。

## 完了条件（first slice）

- record なし実行の性能が計測誤差内で不変。
- record → replay で代表プログラムの観測（stdout / 終了状態）が一致。
- replay 逸脱が構造化エラーになる。
- host 型を返す op の record が明示的エラーになる。

## やってはいけないこと

- normal モードに記録用の分岐・トラバーサルを乗せる。
- 記録できない operation を黙って素通しする。
- 時刻や乱数を「再現のために」言語側で偽装する（漏斗の外に非決定性を作らない）。
