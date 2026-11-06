# 型推論の参考資料と形式化との対応

## Simple-sub

Lionel Parreaux, *The Simple Essence of Algebraic Subtyping: Principal Type Inference with Subtyping Made Easy*, ICFP 2020.

- [著者の論文ページ](https://cse.hkust.edu.hk/~parreaux/publication/icfp20/)
- [公開PDF](https://infoscience.epfl.ch/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/download)
- [公式参照実装](https://github.com/LPTK/simple-sub)
- 論文対応ブランチ: `mlsub-compare`
- 参照したcommit: [`9bae772624c23b52a93c1b226157e16898b4d9db`](https://github.com/LPTK/simple-sub/tree/9bae772624c23b52a93c1b226157e16898b4d9db)
- [Typer.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala)
- [TypeSimplifier.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/TypeSimplifier.scala)

取得・照合日: 2026-11-06。参照実装はMIT license。現行のLeanコードはここで独立に構成したものであり、Scala実装の移植ではない。

論文§3の上下bound伝播と極性、§4.3の単極除去・共起・sandwich、§5の宣言的subtypingと主型性を参考にした。§5の定理はlet多相を除いたcoreについて述べられ、詳細な証明は省略されている。したがって、本文の定理名をLeanで検証済みの証明として取り込んではいない。

## この核で証明した構成

| 役割 | Lean側の構成 |
| --- | --- |
| 未知変数を挟む下界×上界の伝播 | `NestedValueSolver` の有限Horn閉包。全node対を有限universeとする。 |
| shared parameterの保持 | `ValueBoundSchemes` の `L_i ∪ ⋃(ρ_j ∩ U_j)`。入力と出力で同じparameterを共有する。 |
| 再帰値型の構成 | `RegularValueCoalescing`。変数だけの経路を有限lattice式へ展開し、constructorの子をguardedなgraph参照にする。 |
| 再帰値型の独立意味論 | `RegularValueTypes` の全有限観察によるsubtyping。有限型で元の代数と一致することを証明する。 |
| 単極・共起・sandwichの簡約 | `TypeSimplification`。全instance集合を保つ有限passであり、唯一の表示標準形ではない。 |
| sourceの論理的binderと選択肢 | `ConstraintNormalForm`。元のprincipal formulaの意味を保つ有限clauseへの変換。 |

ここでのcoalescingは、全未知型の**解そのもの**を自由parameterから構成する方式である。論文のrawな正負の表示展開をそのまま実装したものではない。正負が混在する場合も、全モデルの再現定理と全output instanceの同値を直接証明する。

`compactType` に見られるconstructorの合成等式は、現在のYulangの有限構造型代数から一般には導けない。主型構成と、安全な簡約に必要な法則だけを使い、完全なMLsubの代数を暗黙に追加しない。

## Yulang固有の規則

値型変数のlevel調整であるSimple-subのextrusionを、Yulangのeffect境界のintrusionと同一視しない。`'e?`、`[io,'e]`、signed transport、T3 snapshot、値制限、EOFの非defaultingは、`spec/` と対応する既存Lean moduleが定める規則を使う。

値型graphの求解が完成しても、未知rowの求解・sourceからの境界挿入・一般化・表示を含む全推論入口は別に接続する必要がある。各定理の正確な範囲は [`spec/10-inference-core.md`](../spec/10-inference-core.md) と [`README.md`](README.md) に記す。
