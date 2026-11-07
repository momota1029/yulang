# B5/B1: 宣言ごとの variance と中心なし不変区間

状態: **2026-11-08 のユーザー訂正（二回目まで）を反映。一般 B5/B1 は未証明。**
最初の版の「nominal 引数はすべて不変」「有限の constructor 入れ子でも不変」という読みは取り消す。
この文書が、旧点モデルと最初の区間版設計の解釈に優先する。

## 1. 権威、確定事項、保留事項

出典:

- [spec/06-roles.md §6.5](../../spec/06-roles.md): 不変区間、2026-11-08 二回目訂正の無限入れ子／box 共変、宣言時 variance、境界、deferred cast と EOF。
- [旧 role-system](../reference/2026-06-02-role-system-yulang2.md)「注意」: 中心なし lower/upper、同じ実引数の merge、交差制約、両側出現変数の等式、collapse。
- [旧 invariant-type-sandwich](../reference/2026-06-06-invariant-type-sandwich-yulang2.md): 同じ不変 slot の bounds merge、通常の制約機械への返却、全出現に基づく sandwich、再 collect の原因 key。
- [完了契約・最終追記](../handoff/2026-11-07-m1-completion-contract.md): 存在／任意代入を使う前に、実 solver の決定規則を仕様で確認する。未指定の選択で E2 を作らない。

**nominal identity は variance を決めない。** 各宣言の各引数位置に、宣言時に確定した variance を持たせる。
有限の入れ子では通常の位置による共変・反変を使う。`box 'a` の `'a` は共変である。
list/tree のように実行時に際限なく深くなり得る引数は不変である。そこを cast すると値全体を再構築するため、不変引数の内部へ cast を通さない。
「他の型構築子の引数ならすべて不変」としていた最初の版は誤りである。
宣言の検証結果に kind/arity/variance を焼き込み、推論や各代入の時点で variance を決め直さない。

普通の位置・複数出現・再帰的な引数伝播からこの表を実際に計算する宣言 verifier は、今後の証明義務である。
任意の表を外から受け取る局所 theorem を、宣言時導出の完了としない。
旧 role-system の raw impl-head demand と residual where の反転した読みは別段階であり、nominal の訂正でその二段階を一律に書き換えない。

### box の問いは解消

```yulang
struct box 'a { value: 'a }
my choose(c: bool, x: box int, y: box bool) =
    if c: x else: y
```

この結果は共変の `box (int | bool)`。先に提示した「box の区間併合で型エラー」という推奨は撤回し、確認待ちを終了する。
不変の `list int` と `list bool` の対応する合流は `(int | bool, int & bool)` の区間になり、整合性を満たせない。
この区別は 2026-11-08 の二回目のユーザー説明に従う。古い spec 内の box を不変としていた例を根拠に戻さない。

**deferred 境界**: 今回の証明の作業対象を不変 list の構築位置に絞る。spec が適用範囲を「要確認」としているため、
言語一般で不変位置だけに限られると断定したり、共変 box の包含／排除を確定したりしない。
不変 list 側の既定規則から先に進め、旧 box deferred 弱変数ルールを無条件に再適用しない。
有限で共変の box は、構築後にも宣言の有限 wrapper を一段変換できる。
この pending な source 規則を、任意 substitution の theorem や E2 で代用しない。

## 2. 不変位置の区間と既存 solver

この節は、**宣言で不変と確定した位置だけ**を扱う。

不変引数は `I = (L,U)`。中心を data として持たず、独立な実引数 t の充足を `L ≤ t ∧ t ≤ U` とする。
`bool | int | 'a & float & complex` の内部は `(bool | int | 'a, 'a & float & complex)`。
実引数 t は Models の独立 assignment であり、区間 data に保存する中心ではない。
同じ実引数 slot に来る I=(L₁,U₁), J=(L₂,U₂) は:

```text
merge I J = (L₁ | L₂, U₁ & U₂)
```

元の `Lᵢ ≤ Uᵢ` と交差条件 `L₁ ≤ U₂`, `L₂ ≤ U₁` を通常の制約機械へ戻す。
両側の具体成分が同じ単一具体型 T なら T に collapse する。両側共通変数の等式と、全出現を調べる具体 constructor の sandwich は区別する。
旧文書の `'a <: box 'b` / `'a <: box 'c` の区間例は、訂正後には不変の list 等の位置の説明として読む。共変 box にその merge を適用しない。

### 2.1 再利用の根

新しい点型 carrier や demand interpreter を増設して、区間問題を回避しない。
最初の補題では既存 `Common.Ty` / `Common.Subtype` を endpoint に使う。
nominal ID・arity・型／行 kind・variance・元 slot は finite descriptor / declaration data として残し、structural variant で nominal を代用しない。
一般の recursive nominal を endpoint 内部に持つ橋は別の義務であり、Common に専用 nominal/Float head があると仮定しない。

- `CommonBoundCoalescing`: arbitrary Common endpoints の lower/upper、有限 flow、rigid comparisons、実 `expand`、全 parameter と全 model 回収。
- `DemandBoundPropagation`: 同じ flow の到達、lowerBounds/upperBounds、要求根と反対極性。
- `CommonBoundRef*`: 元 shared node、required/optional/width 参照、有限 inspection/worklist、row family と全元 node/row 回収。
- `CommonCanonicalIntervals`: scalar lattice の captured/generalized interval と実 envelope。constructor・相関する複数出力へ無証明で広げない。

`CommonBoundRefPolarity` の source grammar と、宣言時 variance は別の判定である。
前者の generator/inspection 閉性を、後者の実宣言検証結果と元 source から導く必要がある。

### 2.2 代入をどう決めるか

固定した有限 bounds/flow の実 family は、既存 `CommonBoundCoalescing.expand`:

```text
lower(j) | ⋁(pᵢ & upper(i))   （i は j に到達する元 slot）
```

固定 endpoints の rigid comparisons は実 checker / inspector が検査し、その成功を返却 scheme の membership から導く。
parameter の条件として Consistent / Models / ResidualHolds を残さない。
元のモデルを parameter に置く実 retraction によって、全元 slot と全元 row を同時に回収する。

不変 literal の弱 slot は、既定の後の利用／EOF 規則で確定する。確定した target を元構築 site に戻す。
EOF 未確定なら、仕様どおり cast なしの元要素型 union に確定する。
open interval のどこかの T を都合よく existential に選んで cast 成功とする規則は置かない。
未指定の regular matching や正準 tail の選択に出会ったら、実 solver の決定規則を先に確認する。

## 3. 一般 nominal rule は per-argument variance を使う

### 3.1 collapsed な実引数での比較

検証済み宣言 D が nominal ID N と引数表 `[(kindᵢ, varianceᵢ)]` を持つとする。
任意の、宣言に合う kind/arity の二つの collapsed argument 列 A/B について、一般目標は:

```text
NominalSubtype D (N A) (M B)
  iff
N = M ∧ arity/kind が同じ宣言に合い、全 i について:
  Covariant:     Aᵢ ≤ Bᵢ
  Contravariant: Bᵢ ≤ Aᵢ
  Invariant:     Aᵢ ≈ Bᵢ
  Unused:        制約を追加しない（宣言の kind/arity 検証は保つ）
```

これは pure subtype/keep の rule。A/B がそのまま合わない場合の登録 cast の探索は別判断である。
したがって `box A ≤ box B iff A ≤ B`、不変 list の collapsed case は `list A ≤ list B iff A ≈ B`。
arrow/record/tuple/regular graph 内部でも同じ宣言表を参照する。
表に依らず全 nominal argument の両方向を検査する既存 interpreter は、一般 carrier には使えない。

### 3.2 open な不変区間と有限生成

`common_nominal_invariant_exact` は一般 nominal theorem の **Invariant 位置の射影**として言い直す。
一般側は `common_nominal_variance_exact` という作業名で区別する:

```text
任意の実検証済み有限宣言集合 D、宣言時に計算済みの kind/arity/variance 表、
任意 nominal IDs、元全 shared slot/row IDs と argument descriptions、
任意の独立な元 endpoint/row assignment について、
実 declaration-aware inspector の有限 bounds/flow/check の Models
  iff
同じ D を参照する独立 nominal comparison/reconciliation judgment。

共変位置は正方向、反変位置は逆方向の制約を生成する。
不変位置だけ、同じ実引数を共有する中心なし区間の lower/upper と全交差制約を生成する。
全元 Models を実返却 scheme の無制約 parameter 全体で回収し、
任意返却 scheme と任意 parameter は元 Models を満たす。
旧 Common の順序・typing・実 solver の契約を保存する。
```

区間 reconciliation と、任意の二つの区間の instance 集合包含は別判断である。
同じ slot の複数 occurrence に別々の actual witness を与えず、元の共有を保つ。
kind/arity/宣言検証失敗と、inspection の成否は実 data から計算し、外部 compatibility oracle にしない。
任意の表を前提にする局所比較 theorem だけで、実宣言から表を導く義務を終了しない。

## 4. ground cast も declaration-aware にする

旧 `CommonGroundNominalCasts` の raw nominal equality と `Casts.Compatibility.nominalInvariant` は、
**全引数が不変な宣言の collapsed case**に限って再利用できる。
上下を (T,T) にしただけでは、共変 box の比較は引数同値にならない。
既存 ground interface の `nominalInvariant` 要求自体が共変 nominal には強すぎるため、一般定理にそのまま使わない。

改訂 `common_ground_cast_compatibility_exact`:

```text
任意実 verified finite D、任意明示済み finite ground grammar の source/target A/B、
D の ID/arity/kind/variance を使って実正規化・比較する checker について:
check_D A B = true iff 独立 declaration-aware GroundKeep D A B。

scalar/scalar は元 Common scalar subtype。
scalar/nominal と nominal/scalar の元 grammar の bottom/top の case を保つ。
nominal/nominal は同じ ID と宣言表に従い、共変は正方向、反変は逆方向、
不変の collapsed arguments だけ双方向要求同値で比較する。
```

open 不変区間の target 決定を、任意の existential substitution に置き換えない。
実確定 endpoint を keep/search/failure へ渡し、同じ元 body の pure immediate row と、arrow の変換済み引数での request tree を保つ。
共変で有限な wrapper の成分変換は実宣言の有限構造をたどる。不変 list/tree の内部へは cast を通さない。
一般 wrapper の有限性・実行順・行保存を、nominal ID の一致だけから仮定しない。
既存 total PureCasts の局所障害は、宣言別の区間版 B5 全体の E2 ではない。

## 5. construction と B1

`common_construction_sites_exact` / `common_data_list_exact` の改訂目標:

```text
任意実署名、実検証済み list/nominal 宣言と宣言時 variance 表、
任意元環境・全 data/nil/cons/nominal-data 式・元結果 description、
任意独立の元 endpoint/row assignment について、
独立 declaration-aware Common Typing iff 実有限生成制約の Models。

全 field/site/元位置/元順序を保持する。
共変・反変位置は宣言表の方向で扱い、不変位置は元 shared interval slot を保持する。
不変 literal の必要 deferred pure cast を元構築位置へ戻し、各 site を一度だけ評価する。
実全返却 scheme の全自由 parameter 健全性と元全 Models の回収を接続する。
弱変数の後の利用／EOF は同じ元 slot に接続する。
Float の基底型意味と旧 Common theorem を保存する。
```

nil/cons の list element は、不変の interval/未解決 slot を保つ。各 site に別の element witness を与えない。
共変 box は不変 list の特例ではない。旧 box deferred example の適用範囲は spec の「要確認」と二回目訂正を記録し、決定済みとして証明へ埋め込まない。

## 6. 既存結果の正確な位置付け

| 結果群 | 訂正後の範囲 |
| --- | --- |
| `CommonBoundCoalescing`, `DemandBoundPropagation`, `CommonBoundRef*` | 元の量化・grammar・前提のまま有効。宣言 variance、nominal endpoints、実 source 閉性は追加の接続義務。 |
| `CommonCanonicalIntervals` | 元の scalar/captured/generalized interval theorem として有効。一般 nominal の canonical code ではない。 |
| `nominal_regular_invariant_exact`, `nominal_finite_invariant_exact`, `nominal_head_invariant_exact`（Full 系も含む） | 全引数を不変とした point interpreter の定理。whole nominal iff は **全引数が Invariant** かつ上下が同じ T に collapse した宣言だけ。引数同値の補助は mixed table の Invariant 位置に限り再利用できる。共変 box の一般 rule としては誤りであり、流用しない。 |
| `list_invariant_exact` | list の不変引数の collapsed case として使う。open interval/弱変数の全判断を表してはいない。 |
| nominal slot equality solver / point ground adapters | whole ground adapter は **all-Invariant 宣言の collapsed case**だけ。個別の equality 補助は mixed table の Invariant 位置でのみ使える。covariant/contravariant 宣言の whole rule に流用しない。 |
| FullDemand / FullCarrier 等の旧 point 候補 | 全 nominal 引数を invariant にするため、一般 Yulang carrier ではない。旧 theorem の意味を変更しないが、今後の一般 model として採用しない。 |
| 旧型埋込み・旧 `Core.infer` 像の保存 | 各旧 point model 上の theorem として有効。declaration-aware interval solver の保存拡張は別途必要。 |
| graph/AST allocator、order/位置の literal equality | 再利用候補。point Models の意味や全 family を新 variance/interval Models へ無証明で移さない。 |
| `CommonInvariantIntervals` | 不変 slot の区間代数・元 finite bounds 生成・既存 expand 回収。arbitrary Common endpoints に対する代数で、nominal 宣言全体の rule ではない。 |
| `CommonGroundIntervalSolver` | 閉じた scalar endpoints の区間/flow に対する実 checker と無制約 Common parameter family。一般 nominal source solver ではない。 |
| `CommonNominalIntervalReconciliation` | すべての対象位置を **Invariant** とした局所 metadata reconciliation。型・行 bounds と同一実引数を保持する補助。一般 nominal merge としては使わない。 |
| point-based construction/data generation | per-declaration variance、不変位置の区間、必要な deferred target 決定を含めて言い直す。 |
| 局所 cast 障害 | 指定済み表現に対する theorem のまま。未指定 substitution や未生成の核の型から実 solver の E2 を作らない。 |

中断時の未完成 `CommonNominalFullTypingReflection.lean` は未 import のまま停止している。
旧 point-model proof の補完を今回の declaration-aware な区間作業より優先しない。

## 7. 続ける順番と未完の実義務

1. 不変 slot の区間代数・cross constraints・collapse と、既存 bounds generation / solver family を閉じる。
2. **宣言済み variance 表を参照する** finite nominal inspector を作り、共変・反変・不変の出力制約を区別する。
   任意の表を読む局所 exactness と、実 finite declaration の recursive parameter 解析から正しい表を導く theorem は別に記録する。
3. per-argument subtype theorem とは別に、宣言ごとの constructor union/grouping、元 branch 生成と同じ結果への readback を証明する。特に `box int | box bool` が `box (int | bool)` として得られる実 source の合流橋を残す。head の局所比較だけから source join の完了を主張しない。
4. ground checker を declaration-aware に接続する。既存 all-invariant checker の保存 theorem はその正しい部分だけに限定する。
5. interval constraint の再 collect では、元 slot/path と原因の有限 key に新規の制約があるときだけ回す。
   合算済み bounds 全体を key にしない。global sandwich は全出現・captured/level 保護を保ち、区間由来変数等式との区別を証明する。
6. 元全 fields/sites を保つ declaration-aware generation、実全 family、弱変数の後の利用／EOF を接続する。
7. 必要な B5 基盤が閉じたところから B1 nil/cons/list/nominal-data へ進み、有限 wrapper の runtime cast / pure row / order を接続する。
8. 各 closed packet を `lake build --wfail`、fresh review、trust=0 Audit / 公理 allowlist で検査する。

結果は [2026-11-08 interval results](../handoff/2026-11-08-m1-b5-interval-results.md)、
進捗は [既存 progress](../handoff/2026-11-07-m1-b5-progress.md) に訂正後の状態を明示する。
部分言語・任意表の局所定理・追加仮説付き結果を B5/B1 の E1/E2 として報告しない。
