# F1: 普通の関数の引数効果 passthrough（監査 cycle 1）

## 対象と判定

- Yulang2: main `d4c8bc8fc8a49173180932cd25921a2c41057354`。
- 新spec/Lean: integration/m1-final `3b34c9e94b255ecde581e92cac787604e8313cad`。
- 新spec §5.5c はユーザーの確定した考え方であり、ここで変更しない。
- **Y2の構造的subtypeには特例が実在する。新Leanの`Common.common_arrow_iff`には同じ特例はない。**
- ただし、**Leanに引数効果の伝播が全くないという判定は誤り**。`strictApp`の独立判断・生成器接続は存在する。関数型自体のsubtype/castと、strict application時の効果合流を分ける。

## F1 / X25 状態

**部分的。X25をPROVEDとはしない。** strict application断片は既存Leanにある。普通の関数型から効果付き引数を受ける関数型への変換を、現行Commonのsubtypeとして実現する特例はない。独立coercionとの最終接続は未確認。監査で書込み禁止のplan/conformance本体は編集せず、この表を監査側の状態表とする。

| 適合例 | 状態 | 証拠／残件 |
|---|---|---|
| X25（spec5.5c） | PARTIAL、非PROVED | Y2 ordinary/pipe/inferred-higher成功、明示higherはrun失敗。Lean strictApp部品あり。F1関数型変換の接続未完・未確認。 |

## 読取根拠

`crates/infer/src/constraints/machine/propagate.rs:234–245` は下側関数の `arg_eff` が `Neg::Bot` のとき、上側の引数効果 `upper_arg_eff` を `passthrough_ret_eff` へ流す。通常の反変引数行検査とは別の分岐。
同401–409行の `pure_arg_effect_passthrough_target` は戻り側のstack wrapperを外して通過先を求める。同257–262行で元の戻り効果も戻り行に流す。

applicationは `lowering/expr/tail.rs:535–563` で実引数のeffectを期待関数arg_effへ置き、calleeとのsubtypeでこの分岐を通る。callee自身のeffectとcall resultは615–623行で合流する。pipeはchain.rs:87–88,121–122とtail.rs:31–49により同じmake_appに入る。

省略引数行はannotation/constraints.rs:395–401とlambda.rs:1344–1353でpure bounds/Neg::Botとして作られる。内部表現だけを見てtopとは言えないが、passthrough特例があるので「空effectしか受け取れない」と読むことも誤り。
この規則はuser-defined cast tableではなく、structural subtypeの処理である。

## 実機・unit test

公式Rust toolchainを隔離workspaceへ導入。offline cargo buildは依存chasa不在でexit101、online release buildは91秒で成功。既存ソース変更なし。

`cargo test -p infer pure_function_argument_effect_passes --lib` は3件PASS、exit0、86秒。これはlowering/runtime全体の証明ではなく、制約機械の通過規則の既存回帰。

`--std-root lib --no-prelude` で自己完結した例を実行した。入力と出力全文・command・時刻は `runtime-cycle-1.md` に保存する。

| probe | check | run | 観測 |
|---|---|---|---|
| plain(ping::get())をhandle | 0 | 0 | `run roots [7]` |
| ping::get() \| plainをhandle | 0 | 0 | `run roots [7]` |
| 引数fを推論するhigher plainをhandle | 0 | 0 | `run roots [7]` |
| fに`[ping] int -> [ping] int`を明示したhigher plainをhandle | 0 | 1 | `conflicting type candidates: [ping] vs []` |
| 引数を使わず99を返すignoreへping::get()を渡し、handlerは継続せず7を返す | 0 | 0 | `run roots [7]`。効果が起動時に発生する具体的観測 |

明示高階例でのcheck/dump成功とrun失敗は**Y2の処理段階間の不一致**として残す。表示型では行が省略されるため、型表示だけから効果がないとは結論しない。ソース仕様を修正したり、Y2挙動を新言語の意味論として採用したりはしない。

## 新Leanとの対応

`Common.common_arrow_iff:166–179` は
`arg' <: arg ∧ rowLe argRow' argRow ∧ result <: result' ∧ rowLe resultRow resultRow'`。
非空rowを空rowの引数側へ写す前提は満たせない。したがってこのモデルのままF1関数型変換をsubtypeの定理として証明することはできない。具体的には任意の型A,Bと、あるoccurrence oを含むrow Rについて、`arrow A rowEmpty B rowEmpty` が `arrow A R B R` のsubtypeなら、iffの第2条件から`rowLe R rowEmpty`。oに適用するとFalseとなる。この一般反例は既存iffの紙上の適用であり、今回新規Leanファイルとしてコンパイルした証明ではない。

`CoreCommonSyntax.lean:130–134` は歴史的`.app`と`.strictApp`を分ける。`.app`の結果行はcallee行と戻り行、`.strictApp`は実引数行も合流する。lowering:64–65も`.app`を一律strictAppへ変更せず、strictAppだけforceApplicationへ送る。

`CommonCoreStrictApplication.StrictTyping`, `forceApplication_typing_exact` / `principal`, 推論接続の諸定理はstrict application断片の正当化であり、任意高階の矢印subtypeのpassthrough分岐を置き換えたという証明ではない。

## B4/B5/B6への影響

- B5: applicationの入口とeffect行の責任を区別しないと、historical appでF1のsurface例を覆ったと誤認する。
- B6: 共通carrierのarrow比較・有限constraint solver・cast挿入/明示変換境界の整合を要する。
- B4: 関数型を含むrole head/associated constraintが旧arrow orderを前提とする場合、モデル変更の波及点になる。具体的破綻例は未証明。

独立した監査であり、既存Lean/specの変更はない。モデルの修正方針は質問ノートへ分離する。
