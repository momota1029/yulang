# F1 cycle3: source経路の読取監査と成功/失敗対照

旧実装 `main@d4c8bc8fc`、新仕様/Lean `integration/m1-final@816ed8f1d`。既存ソースの変更・instrumentation・新規ビルドは行っていない。以下は親の実機台帳 `/tmp/audit3/f1.json` / `f1-effectarg.json` の読取りとRust/Leanの静的調査。

## 確認した対照

共通のhandlerはpingを7でresumeする。`our higher(f: int -> [ping] int) = f ARG`について:

| actual関数 | ARG=3 | ARG=ping::get() |
|---|---|---|
| pure named identity | check/poly/mono/run成功、3 | check/poly成功、mono/runで `[ping] vs []` |
| pure literal lambda | 同上、3 | 同上のconflict |
| 実際にpingを起こす関数 | 同上、7 | 同上のconflict |
| unreachable armだけpingを持つ関数 | 同上、3 | 同上のconflict |

したがって「純粋なactualをeffectfulな期待型へadapterする場合だけ失敗」とは説明できない。期待関数の戻り行を明示した高階境界と、**その高階関数の本体で渡す効果付き引数**の組合せに失敗が局在する。これはこの有限matrixの観測であり、一般的な必要十分条件ではない。

- 単独binding `my f: int -> [ping] int = plain` 経由の直接適用は、ARG=ping::get()でも7。
- 高階引数の戻り行を型変数 `['e]` または `[]` にすると、今回の効果付き引数例は7。
- 無注釈高階＋実effectful actualも7。
- poly表示のhigherは両側とも `(int -> [ping] int) -> int`。表示から効果消失や[]への同定を断定できない（hygiene/implicit rowが省かれる）。

## 既存ソースで確定している経路

1. `crates/specialize/src/lib.rs:77–81` の公開specialize入口は `specialize2::specialize` に委譲する。旧solve/ディレクトリだけを根拠にはしない。
2. 推論段階 `crates/infer/src/constraints/machine/propagate.rs:212–259` は関数部分型を分解し、actualのarg_effがNeg::Botなら、expected引数行をexpected戻り行（stackを剥いだもの）へ流す特例を実行する。`:401–409` がstack除去。
3. specializationのapplicationは `crates/specialize/src/specialize2/task_solver.rs:478–570`。calleeを関数として見られる場合、既知pure引数行なら `consume_expr_value` で実引数の評価効果を別に回収する。それ以外は `consume_expr_computation` で引数行を消費する。最後にcallee・call argument・returnの各効果をjoinする。
4. `consume_expr_value` は同ファイル`:237–276`、`consume_expr_computation` は`:329–356`。いずれもactual/expected occurrenceを作ってgraphへsubtype制約を投入する。
5. specializationの構造的関数subtypeは `specialize2/type_graph.rs:571–612`。arg/valueとarg/effectを反変、ret/valueとret/effectを共変に制約する。**このmatch armにはinfer段階のNeg::Bot passthrough分岐と同じ特例はない**。bool判定の `specialize2/effect.rs:36–48` も標準の4成分判定。
6. `specialize2/type_graph/bounds.rs:533–562` はslot候補のconflictを `SlotSolution::Conflicting` に保存する。エラー表示は `lib.rs:305–313`。同名エラーの生成箇所はtype_resolver/candidate等に複数ある。

## 原因の確度

- **確定**: polyまでは通り、monoでも失敗するため、VM実行だけの問題ではない。pure actualだけの問題でもない。
- **確定**: inferとspecializationは同じ関数subtype分解コードを共有しておらず、前者にだけ明示的なpure-arg passthrough分岐がある。
- **未確定/仮説**: この分解の違い、consumer signatureの構築、arg-effectのmaterializationのどれが今回のconflicting slotの直接原因か。call stack・slot provenanceの動的traceを取っていないため、`:599` 等の単独行をバグ原因と断言しない。上記apply_type自身にもpure引数評価経路があるので、「specializerにはF1対応が全くない」とも言わない。

## 新spec/Leanの現在の判断

`spec/05-effects.md` §5.5cは、**F1を矢印部分型には混ぜず、独立した明示変換(cast)判断として形式化する**と確定済み。cycle1/2の質問の「どちらに置くか」は再質問しない。型表示やcast挿入箇所の細部は引き続き要確認。

`Common.common_arrow_iff` (`Common.lean:166–180`) が標準の4成分順序であることは、新しい決定と整合する。そこにF1分岐がないこと自体を欠落や誤りとはしない。`Core.CommonSyntax.Typing.strictApp` (`CoreCommonSyntax.lean:132–134`) は起動時に実引数の行をjoinするが、任意の高階期待型に独立castを挿入する証明とは別。独立cast判断とそのsource接続の完成については、この監査で証明も全体ビルドも行っていない。
