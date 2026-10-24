# 元の実行構文・代入・式本体から control への接続

LEAN-CORE-20261024/r1 および LEAN-STRUCTURAL-20261024/r1。primary の構文対応監査と停止後の共同構成。全元 constructor の well-formedness/typing は未構成である。元全体目標は OPEN。

## 元の定義

[O の実行型・構文・型規則](../../docs/yulang-operational-type-safety-ja.tex) §1、通常遷移 §2.2、Call と handler の規則を、[V1–V7](2026-10-24-corrected-core-value-continuation.md)、[G の全構文・adapter 接続](2026-10-24-source-core-action-coverage.md)、[D の eabs/eapp](../../docs/yulang-dot-selection-safety-ja.tex) と合わせて使う。O の旧 snapshot/一様改名は修正 CM/S に優先しない。有限型導出と実行の停止を混同しない。

| 分類 | 元 constructor / 必須の区別 | 凍結版で確認するもの |
| --- | --- | --- |
| 型 | 型変数、unit/bool/int/float/string/bytes/path/char、Top/Bottom | literal と対応型、Bottom 導入なし |
| 型 | union/intersection、tuple、required/optional record、polyvariant、nominal、μ、U、C、∀ | label/arity/identity/一つの型代入、μ/∀ binder |
| 追加型 | Kont(Q,A)、evidence arrow D⇒e^k A | ordinary callable と別、同じ response Q と結果 A |
| 構造値 | var/literal/tuple/seq/record/tag/nominal | seq は固定 List identity、record presence、nominal payload template |
| code 値 | Value/Computation lambda、Delay、wrap、eabs、cont | actual body、mode、receipt、capture と formal、wrap の二つの adapter |
| 証拠値 | type abstraction/application、in、both、roll、top、View、graph ref | both は同じ raw v の二導出、型適用は全出現に同じ置換、ref は local ではない |
| 計算 | Ret、let、Force、Call、Resume | let/Force で実本体を開始、Call の inert UA、Resume の Q |
| 構造除去 | split、field/lookup、switch、unroll、choose、unioncase、absurd | binder arity、optional の unit|A、MatchFailure と Bad の区別 |
| 宣言参照 | prim、perform、template | 同一 instance の宣言照合、template body の一段展開、62 primitive の全件 |
| 制御 | Handle、mapop、release、Scope、View/expose、enter、try、wait | 新しい frame prefix と旧 suffix、handler が捕捉される場合の差 |
| 再帰・失敗 | rec、Fail、raw Bad | 全 RHS と body の同時 binder、guarded graph、古い node 不変、Fail は列挙済み四理由 |
| 証拠適用 | eapp、admin result/effect View | source Call の新 receiver を作らず、実 body と effect を通常実行 |

## 代入の binder 条件

同じ source Γ の項代入を、以下の全子に同時に施す。

- lambda、eabs、cont は元 source では一つの term formal を body で束縛する。raw 表現では lambda/cont の formal は value namespace、eabs の dictionary formal は evidence namespace を使う。eabs を具体化するときは lexical binder identity の表を持ち、その formal に解決された出現だけを evidence index へ写す。別の value local や同綴りの shadowing binder と混同せず、eapp の引数は evidence namespace の当該穴へ置換する。この source encoding と型付けはまだ未実装であり、現在の証明の前提ではない。cont の control activation 名は term local と別の名前空間である。
- let の binder は後半だけ、split は payload 個数だけ、unioncase は各 branch に一つ、switch は各 arm の payload arity だけ増える。
- value arm は正常値、operation arm は同じ instance の payload と continuation を束縛する。wait 内の元 pending データを別 packet の binder と混同しない。
- wrap の引数・結果 adapter はそれぞれ独立の formal を持つ。同じ置換を両 body と被変換 callable に施す。
- rec は全 RHS と本体が同じ同時再帰環境を見る。再帰 binder を一つずつ独立に消費しない。
- type abstraction は type binder を増やす。term binder と type binder の lift を混同しない。型の μ/∀ 内でも type substitution を lift する。
- graph reference、nominal/family identity、receipt/receiver/target 等の保存 metadata は term variable ではない。項代入だけでこれらを改名しない。

型保存の代入定理は、独立に定義した typing 導出を変換する必要がある。raw substitution の恒等式、閉じた literal だけへの補題、全体の保存を前提にする型規則では V1 の義務を満たさない。型抽象の freshness は全 Γ と Δ を対象にし、共有資源の型も含む。

## principal step と control 入口

旧 `Control.Step.body` は `run code args saved :: fs` の body step 後にも `fs` をそのまま置く。このままでは let/Handle/mapop の child への入口で新しい frame を積むことを直接表せない。必要な形は、新しい有限 prefix `gs` を `gs ++ fs` として旧 suffix の手前に置くことである。`FramesTyped gs A B` と `FramesTyped fs B C` の実導出を使い、body の結果型 C を単に仮定しない。

let-return、Force-delay、split、unioncase、eapp の beta と template 展開は、対応する source typing の反転と実際の代入定理から導く。field/lookup、choose、unroll は required presence・同じ underlying value・同じ μ の反転を使う。perform は同じ宣言 instance の payload/response と恒等 K を実構成する。Call/wrap は一つの owner、receipt 前の Force 禁止、引数 adapter の遅延、結果 adapter の実順序を別途保持する。

handler の各 body で正常値が出た時点では、まだ Yes(B) ではない。G の direct result adapter を実行し、その正常出力にだけ Yes を付ける。途中の request/failure は通常の control を通る。これを単なる最終型の一致で省略しない。

## 凍結後の判定欄

[CoreSyntax](lean/YulangClosure/CoreSyntax.lean) の `Tag` は表の constructor 名を保持し、`Raw/Forest` が四つの独立した binder namespace を持つ有限木を定義する。全 metadata と型引数は raw 子として表せるが、各 tag の正しい arity/sort を強制する定義ではない。`rawBoth` は一つの値の子と二つの evidence 子を置くだけであり、それらが同じ値の型証明であることはまだ検証しない。`rawOperationInstance` は一つの operation identity と型引数列を置くが、宣言・payload/response の型規則自体は未構成。char literal の内容は String とし、単一 Unicode scalar に限定しない。grapheme validity は未定義の外在的条件である。

[CoreSubstitution](lean/YulangClosure/CoreSubstitution.lean) の `renameRaw/substituteRaw` は、atom を保ち、node の全子を巡回し、binder の名前空間だけ index を lift する。代入値が別 namespace の自由変数を含む場合も、その binder の下で shift する。全 Raw/Forest に対する identity・renaming composition・rename/substitute の両交換則・substitution composition が Lean で検査された。これは原始構文上の代入代数であり、全元言語の型付き V1 ではない。

外在的な `ValTyped/CompTyped` は **unit/variable/delay + Ret/Force/let** に加え、**union injection/case、同一値の intersection introduction/choose、Top、Bottom elimination** を定義する。`Context = Nat → Option Ty`、空文脈は常に none とし、未束縛変数が型付かない。`substComp_typed/substitute_top` は、この範囲の全型導出について、同じ context を持つ代入値から型付きの body を構成する。`substComp_raw/single_raw` は、その typed-fragment 操作が全 raw traversal の実際の制限であることを証明する。

[CoreExecution](lean/YulangClosure/CoreExecution.lean) は let-return と Force-delay の実置換、syntax-bearing bind frame の追加/消費を定義する。`step_preservation` は arbitrary old suffix を保持し、`progress` は空文脈で Ret または次の一段を得る。さらに raw 側の `RawStep.forceUnitBad` は unit への Force を Bad にする。View/graph/type application の外見が Delay でないことだけでは Bad にせず、その正規化規則は未完として残す。`raw_step_lifts` は、閉じた型付き image から出る **全 raw step** が実 typed-fragment step に戻ることを場合分けし、Bad branch を canonical form から排除する。したがって typed step の片方向 simulation だけから raw safety を推測していない。

`raw_finite_safety` は既存 root と同じ `YulangClosure.Prefix` を用い、任意長の raw trace の全末尾について型付き image、Bad 排除、型付き正常値または次の一段を導く。初期 `RawStateTyped` は構文の image と独立型導出であり、reachability や無故障性を定義に使わない。式本体の保存・進行を前提にしてこの結果を得たわけではない。

## 構造型を同じ全有限実行の定理へ接続

追加した規則は別の safety 仮定を要求しない。次のすべてが、同じ `ValTyped/CompTyped`、代入、`RawStep`、`raw_finite_safety` の場合として Lean 検査を通った。

| 元の規則 | 独立な型付けと実遷移 | 全実行の証明への接続 |
| --- | --- | --- |
| union injection/case | 左右の値型と各 branch の独立した一 binder。選択した branch に payload を実代入 | 両側の型付き代入・raw 可換性、`closed_union`、principal 保存、全 raw successor の逆方向対応 |
| intersection introduction/choose | 一つの `Val.both v` と、**同じ v** の `ValTyped env v a`、`ValTyped env v b`。choose は同じ v を Ret | 選んだ側の導出を用いる保存、`closed_intersection`、両 choose の進行・逆方向対応 |
| Top | 任意の既に型付きの v を `Val.top v` に包む。payload を無検査で取り出す規則なし | renaming/substitution と raw embedding の保存 |
| Bottom elimination | `absurd v` の前提は `v:Bottom`。Bottom introduction は存在しない | `closed_bottom` から閉じた typed state のこの場合を排除 |

O の `(v;d_i)` に現れる d は、この範囲では型導出として扱う。`ValTyped.both` の二つの Prop 証拠が元の d1/d2 に当たり、choose の保存証明は対応する方を選ぶ。計算部分の `rawProofBoth` はその二つの証拠を格納せず、一つの raw child を持つ。元の三 child の `rawBoth v d1 d2` とは別の、**型証拠を消去した表現**である。`rawBoth` の任意の明示 evidence を実行する一般対応定理はまだない。実行時 View/receipt/解除 metadata を消去したり、View の正規化を証明したりしたものではない。choose 自体は一段として数える。

`RawStep` は不正 unit の unioncase/choose/absurd が Bad に進む場合も持つ。`raw_step_lifts` は追加した全遷移を含む関係について、閉じた型付き image からの全 successor を調べる。旧関係だけの有限安全性を再利用したのではなく、拡張した関係について同じ定理を再検査した。実行長を有限の固定値へ制限せず、構造値内の delay と任意の let/branch の入れ子も同じ相互帰納に含む。

最初の検査は unioncase の branch 名と renaming 引数名の衝突を検出した。producer STOP 後に primary が修正し、未使用 simp 引数も除去した。三 module の再検査は exit 0、警告なし。独立査読の受理範囲と固定 hash は [structural outcome](../../tasks/agent-loop/sprints/lean-structural-20261024-outcome.md) に記録する。

## 未完の元義務と既存 control への接続

この成果は全元型・値の意味論ではない。型付き規則が未実装の全 tag、型の μ/∀/nominal 等、Call/Resume、eabs/eapp、primitive、guarded graph、handler/mapop、full source/native/SCC の義務は残る。raw 代入合成が通ったことから、それらの型規則も保存されるとは結論しない。

実構文から syntax-bearing frame を積む経路は let の範囲で構成した。既存 `Control` の `Nat` body label と値タグへ、この新しい構文を写す意味保存の変換は未構成である。既存三 Control module は変更していない。旧 body hook の unchanged-stack 制限、Handle/mapop 入口と全 body の接続は依然未完であり、今回の結果でその full bridge が閉じたとは扱わない。opaque interpreter に枠の実行を隠したり、全出力を許す certificate を追加したりしていない。

次の所有対象は、この同じ Raw 語彙に元の全 constructor の型規則を与え、現在の typed fragment を拡張すること、および source-bearing body/frame と control を結ぶことである。独立査読は、この raw 代入代数と明記した型付き範囲を受理した。BLOCKING/MAJOR 指摘なし。eabs の source formal と raw evidence namespace の対応についての MINOR 指摘は、未実装の lexical encoding 義務として上に明記した。
