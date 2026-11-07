# 共通 `Core.infer` の構文拡張 (2026-11-07)

状態: 下記の閉じた部分言語を実装・証明。全 Yulang の統合は未完。
対象ブランチ: `integration/m1-common`。

この作業では、最初に `origin/yulang3` の `a7fb60f1e` を取り込み、全体 build と Audit を通した。
出発点の棚卸しは [coverage idea](../ideas/2026-11-07-core-infer-coverage.md)、
前回の solver 完了範囲は [saturation results](../handoff/2026-11-07-m1-common-saturation-results.md) を参照。
本メモは仕様上の新しい言語規則を決めるものではない。

## 1. 今回の公開入口と正確な範囲

公開 `Core.infer` は `CommonSolvedCoreSyntax.infer` の有限 scheme 列を分類する。
独立した型判断は `Core.Typing (Core.CommonSyntax.model Common.model)`。
この判断の規則は generator、solver、lowering、`Formula.Holds` を参照しない。

現在の入力型は引き続き `Core.Required.Term = Core.Expr Core.Signature.empty`。
Float / Op / Key / Scope / Atom の各 carrier は `Empty` であり、これらを一般の署名にした定理はまだない。
`CoreExpr.lean` を実際に数えると構成子は **32 個**である。元の棚卸しにある 31 という数え方を訂正する。
単に構成子名が現れることと、その全 payload 文法を覆うことを区別する。

閉じた構文は、従来の 14 構成子に `literal`、`strictApp`、`leaf` を加え、
さらに次の部分的な `data` と `caseE` を任意に入れ子にしたもの。

| 構文 | 今回の範囲 | まだ含めない範囲 |
| --- | --- | --- |
| 旧 presence 14 構成子 | var/lit/lam/app/letE/branch/pair/fst/snd/emptyRecord/record/recordDefault/field/variant。旧 presence/default 規則を維持 | 全 source elaboration、一般の署名 |
| `literal` | 空 Float carrier 上で inhabit する int/str/bool/unit の全内容 | 浮動小数点の carrier と基底型の接続 |
| `data` | literal、pair、有限 record、variant。全成分を再帰的に検査 | nominal、list、およびそれらを内部に含む data |
| `caseE` | arms がちょうど `[(.bind name, none, body)]`。subject/body はこの全拡張構文 | 他の pattern、guard、複数 arm、default、照合順序、失敗行 |
| `strictApp` | この全拡張構文からなる function/argument | effect/role/nominal を含む一般署名への接続 |
| `leaf` | 任意のこの拡張構文を包む透明な wrapper | historical model と異なる追加効果は導入しない |
| `letE` の名前 | `none` / `some name` とも provenance として保持。参照は de Bruijn index | parser の name resolution の完全性 |

従って、空署名上で **17 構成子の全 payload と 2 構成子の明示した部分**を扱う。
`data` や `caseE` を丸ごと完了として数えない。`nil`/`cons` は未統合。

## 2. 公開 theorem の契約

任意の `e : Core.Required.Term`、任意の `c : PresenceGeneration.Comp Common.model` について、

```lean
Core.Typing (Core.CommonSyntax.model Common.model) [] e c ↔
  ∃ S ∈ Core.infer e, ∃ p : S.Parameters,
    PresenceGeneration.Comp.le Common.model (S.instantiate p) c
```

を `Core.infer_principal` で示す。任意の実返却 `S` と任意の `p` に対する
`Core.infer_instantiates`、任意の `e` に対する `infer_rejected_iff` と
`infer_ne_unsupported` も同じ独立判断を使う。公開前提に support、成功、fuel、closed cache、
残余条件はない。parameters は既存の自由な行・型・再帰 parameter の通常の積である。

構文外の式にはこの判断の規則がなく、scheme 列は空となる。
**`.rejected` はこの明記したモデルでの型付け不能を意味し、他の Yulang モデルでの型付け不能を意味しない。**
現段階の `finish` は `.unsupported` を返さない。この分類は旧入口の意味を保持する。
全構文を統合したと偽って `.unsupported` を削除しない。将来全署名・全構文が閉じた時点では、
既存の result 型の互換性を維持するため到達不能な constructor として残す方針を選ぶ。
削除は推論定理のためには不要で、利用側の exhaustive match に変更を強いるため採用しない。

## 3. 旧入口の保存

従来の `Core.infer` の本体と全 theorem は `Core.PresenceOnly.infer` 以下に残す。
この入口は従来どおり `PresenceGeneration.CoreRules.model Common.model` を使う。
theorem の量化・前提・結論を変えずに namespace だけを分けた。

`Core.infer_presence` は、任意の旧 syntax-supported Core term について、
新旧の `Result` 自体の文字どおりの等号を示す。
`Core.infer_presence_typing_preserved` は任意の旧 presence typing と任意の結果を保存し、
syntax 条件は旧 derivation から内部で得る。
任意の旧 `Inference.Expr e` に対する `Core.infer_embed` の statement は変更していない。
旧 instance ⇒ 新 solved instance の theorem も statement を変更していない。

## 4. 独立判断から既存 solver へ接続する理由

新しい有限 compiler を各構文で作り直す代わりに、独立な constructor rule と
exact lowering を一組ずつ作る。lowering は既存の有限 `Inference.Expr` に着地する。
その後の normalise / pack / graph / finite worklist / all-parameter solved family は再利用する。

`Core.CommonSyntax.lowering_exact` は、任意の covered term、任意の新旧環境、
任意の result について、`EnvRel` の下で型付けの両方向を示す。
`EnvRel` は各 lexical index における **全 computation instance** の一致であり、
環境の型名や最小値の一致だけではない。poly binding は元の RHS と captured environment を保持する。
`lower_isValue` は旧 value-let と computed-let の分岐を保つ。
public theorem では coverage は membership または独立 typing から内部導出する。

`lower` の全域化のための unit fallback は compiler 内部の未使用分岐である。
実 `infer` は最初に `covered` を判定し、false なら `lower` を solver に渡さず空列を返す。
fallback を受理する言語規則はない。

代案として `Typing := Formula.Holds` や「solver が返したものを型付けと呼ぶ」は採用しない。
独立の規則との双方向 theorem が失われるためである。

## 5. B1 / B2 / B6 の lowering の選択

### Literal と structural data

literal の内容は Core に保持し、その静的型だけを既存の base marker へ下げる。
data は独立 `Core.CommonData.ValueTyping` を持つ。
record の先頭 field を最も外側に挿入し、既存の first-field-wins を保つ。
隠れる後続 field も含めて全 stored value を型検査する。
空 record は `Common.exactEmpty` であり、width 型への置換をしない。

list を variant に符号化する代案は採用しない。仕様の list は nominal 引数を共有し、
invariance と construction/cast を伴うためである。`nil`/`cons` を閉じるには B5 の接点が必要。

### 単一の名前 pattern

`case subject: name -> body` に相当する一つの unguarded bind arm は subject を一度評価し、
その pure value を index 0 に **単相**で束縛する。
`let subject; body` への直接置換では、subject が syntactic value の場合に誤って一般化し得る。
そこで `fst (subject, unit)` を computed RHS にしてから let を作る。
`CommonCoreNamedCase.forceValue_typing_exact` と `lowering_exact` が、任意の captured environment と
任意の結果についてこの処理の型付けを保存・反映する。

一般 case の coverage / guard / first-match / default の theorem が別モデルにあることだけから、
この新判断にそれらの規則があるとは主張しない。

### `strictApp` / `leaf` / `free` / `atom`

`strictApp` は function を先、argument を次に評価し、pure argument value で適用する構文。
独立の型規則は function row、argument row、result row をすべて合流する。
同じ captured 環境の下で pair `(function, argument)` を一度束縛し、両射影を使う。
この macro の型付け iff は `CommonCoreStrictApplication.forceApplication_typing_exact`。
`CommonCoreStrictRuntime.eval_forceApplication` は任意の runtime operands に対し、
値だけでなく request tree 全体の等号を示し、記述順を保つ。

`leaf` は `CoreData` が保持する透明な wrapper であり、lowering は中身へ進む。
`free` は historical named syntax の翻訳で残った未束縛名を表す。ローカル束縛を参照するのは `var`。
closed inference に自由名を勝手に割り当てる規則は追加しない。
`atom` は model ごとの resolved payload のための carrier であり、現在の empty signature では inhabit しない。
一般 `Atom` の型表・意味との接続は未完で、空型であることをその完了扱いにはしない。

## 6. 次に進む順序と依存

| 段階 | 現状 | 次の独立した仕事 |
| --- | --- | --- |
| B1 | 部分。literal と structural data は public principal / 全 parameter / rejection / status まで接続 | 浮動小数点の署名・基底型。nil/cons は B5 nominal と construction の接続を先行 |
| B2 | 部分。単一 unguarded bind case は上記と同じ公開 theorem に接続 | Common 上の pattern 環境 exactness、coverage、guard、default、順序。nominal/list pattern は B5 に依存 |
| B3 | 部分。有限 head + flow + pure sink の全 instance row solver は閉じた。公開 request/handler は未統合 | finite operation declarations と signed row interpretation、protect/release/residual、handler の全称量化 |
| B4 | 未着手（既存接点と不足契約の調査・設計は実施） | 有限 visible impl registry と Common 引数に対する resolver/dictionary の exact bridge |
| B5 | 未着手（既存接点と不足契約の調査・設計は実施） | nominal invariant carrier の保存拡張と ground cast compatibility の橋。これは B1/B2 全体を待たず進められる |
| B6 | 部分。strictApp / leaf は公開判断へ統合、free / atom の役割を特定 | 一般署名・Atom table への接続。未束縛 free は受理規則にしない |

順序を一時的に変えた理由は、B1 の list が B5 の nominal を要し、B2 の全 pattern も
nominal/list と effect を要する一方、strict application、name case、head-row family は
既存の presence/row 基盤から独立に閉じられるためである。
具体的な B3/B4/B5 の量化と前提は
[effect・role・nominal の不足契約](2026-11-07-common-effect-role-nominal-contracts.md) に分ける。

## 7. 速度算法との接点

現 solver は参照実装のまま維持する。今回の head-row solver は参照文法への定数追加であり、
union-find 等による高速化ではない。directional bounds の共有、cycle でだけ許される変数同一視、
将来の Lean 関数の refinement 契約と B 各段階への接続は
[共通推論と将来の伝播算法](2026-11-07-common-inference-refinement.md) に記す。

## 8. 仕様に残した問い

新しい `notes/questions/` はない。今回の name case と structural data には確定済みの規則を使った。
E7（pipeline 左辺の effect と handler の到達）や K1（receiver を必須としない role member の整合条件）を
この内部モデルの都合で決定していない。これらが実際の B3/B4 の source 統合で必要になった時点で、
ユーザーが書ける Yulang コード、選択肢、推奨を伴う問いとして追加する。
