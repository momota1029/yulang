# Main statements の配置と全体判断の未接続

状態: 未回答。サイクル2、2026-11-08。

## 配置

inbox I-2 / T7a は `lean/Main.lean`（MainStatements も草稿候補）を示す一方、
現 `tools/verify-lean.sh` の新規 Lean ファイル検査は `lean/Yulang/` 外を拒否する。
監督用の検証スクリプトは変更していない。

1. **遅延案（現採用する暫定配置）**: 草稿を
   `lean/Yulang/MainStatementsDraft.lean` に置き、既存検証の中で確認する。
   所有者が gate と読み口の配置を調整するまで root Main への移動はしない。
2. 所有者が root の Main*.lean を明示許可する gate に変更してから移す。

`MainStatementsDraft` は7件の既存定理を元の量化子と前提のまま再掲する。
構文や言語意味論は変えない。root の Main ファイルが完成したとは報告しない。

## 全体 statement の source carrier

承認済みの B4 は、例えば次のような source の共有変数への関連型の流入を含む。

```yulang
impl Parent (box 'a):
    where 'a: Left
    -- 別の既知 receiver の Right(value = 'a) から同じ 'a へ型が流れる場合を含む
```

しかし、全実宣言・共有 constraint graph・kind/level metadata と、最終の
pending/selected/ambiguous/rejected・全 where 子・普通制約・有限辞書を同時に扱う
独立な source Classify は未接続である。任意の oracle / caller-supplied 関係を
変数として足した抽象命題を、承認済み全体 B4Statement として置いていない。

1. **遅延案（推奨）**: 既存の証明済み断片を名前で明示し、source carrier と
   独立 Classify がそろってから全体 B4/B6 の Prop を追加する。
2. 先に具体的な source carrier / 独立判断の別草稿を作り、意味上の未決点だけを
   所有者が確認してから Main に接続する。

草稿末尾の `OpenPassSemanticStabilization` は既存 pass のモデル集合が有限回で
一段不変になるという**未証明の局所目標**であり、全体 B4Statement ではない。
その命題の真偽は未確認。定義しただけで証明できたとは扱わない。

同サイクル内の追記: 上の局所目標は、その後 `CommonRoleOpenPassStability` の
全モデル exactness と意味的冪等性から `open_pass_stabilizes`（k=1）として
証明できた。未完なのは一般 source narrowing の飽和と全体 B4Statement の接続。
この追記は配置・carrier の問いを解消するものではない。
