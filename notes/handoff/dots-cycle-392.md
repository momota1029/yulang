# Yulang cycle 392

この周に閉じた補題: なし（I-69: 元の型付き RHS の局所規則を部分実装、分割なし）

I-69 に従い、証明を始める前に [不足の二文と出所](https://github.com/momota1029/yulang/blob/ee6f4e8e2def5d33525c64232d9518d2bebd6df9/notes/design/dots-cycle-392-i69-missing-source-facts.md) を記録した。S13bbba の不足は「選んだ実出現の原 body/capture が、その ordinal の literal RHS を生成する」。S13bbbb の不足は「同じ実出現が作った等式が、同じ宣言的状態の固定先に成り立つ」。どちらも (a) の宣言側の規則。spec の関連型は変数と等式であり、物理 native origin や solver release まで必須だとは読まない。

## 実装・検証

- [model-free native RHS module](https://github.com/momota1029/yulang/blob/08935f6f1f00ef09716e723161e36d6a6456680d/lean/Yulang/GeneralDeclarativeI65NativeAssociatedRhs392.lean)、[独立 audit](https://github.com/momota1029/yulang/blob/08935f6f1f00ef09716e723161e36d6a6456680d/lean/Audit/Cycle392NativeAssociatedRhs.lean)。元 `Supplies` で選んだ actual body と original output ordinal に、出力先を推測せず literal receipt を接続する。explicit の actual capture と default の元 demand position は別。各 (value/row) capture には独立の source proof が必要。元 declaration の kind/variance を引いて、bare/tagged nominal app の一般 arity、型/行を混ぜた順つき引数、入れ子、継承 invariant の上下端を保つ。
- `native_source_emits_original_receipt392` は元の ordinal/target/source を持つ receipt を組み立てる。もとの receipt の同値を生成の前提にしない。 `native_body_rhs_functional392` と `native_associated_rhs_functional392` は、この source derivation 内の同じ source と binding では RHS が一意。 `native_rhs_wellformed392` は元の宣言文脈で well-formed を与える。
- [exact where の source 追跡](https://github.com/momota1029/yulang/blob/6e0eefd8ceac5d95c08523d52408bac1b0590621/notes/design/dots-cycle-392-i69-missing-source-facts.md)。associated body の名前は元 head だけでなく、実 where 出力からも来る（`Declaration.Scoped/Produced`）。元 clause/出力 equation ordinal を示し、**元の child/capture が実際に `EmissionForest322` と `ProducedNames325` で生成された場合**、その same output の exact target と body slot が一致することを検証した。C386 `whereAt` の位置・role だけではこの生成の証拠がない。元宣言の同名 associated equation がない条件で、同じ実 ordinal の供給元と literal RHS 全体の一意性も検証した。
- Lean 4.35.0: exact `lakefile.toml`、`lake env lean --trust=0 -DwarningAsError=true` で module を scoped build、独立 import audit を実行。GitHub の immutable source/audit を取り直して blobs を照合し、別 build output で両方再実行、exit 0。五宣言の公理は `[propext, Classical.choice, Quot.sound]`。where/source の四診断は exact 再取得した設計 bytes に `--stdin --trust=0 -DwarningAsError=true`、exit 0。再利用した source manifest（既存 7,356 パス）は exact repo と一致し、新 module の dependency graph の実ファイル 3,806 件も hash 照合した（その全件をリビルドした意味ではない）。full build/Rust/checker は実行していない。

## 残り

S13bbba は未完。全 selected source に **同じ where output の actual typed binding、kind、元 declaration の source emission を与える一般規則** と、native を含む record/join 等の compound RHS から exact literal output を得る表現・規則がまだない。scoped rule を global `Classifies` の拒否・条件としては入れていない。S13bbbb は不足の記録のみで proof 未着手。新しい意味の採用・受理条件の変更・spec 未決の選択はしていない。

**14 = 未証明 3（S01・S10・S13bbba）+ 一部 11（S02–S09・S11–S12・S13bbbb）。** 固定した最上段、checklist の分割/状態、既存 solver/Local/C334、fixture は変更なし。Step 1 は未完、Step 2・3 は未着手、C は後回し。質問ノートなし、使用枠は不明。

発行は `work/dots-main` だけ、expected-head non-force。設計・新規 Lean module・独立 audit・barrel の一行追記・心拍・報告の計 6 パス。凍結 2 ファイルは blob ID のみ照合。
- 最終照合開始 `2026-11-24T12:21:03.528Z`（50 分経過）。
