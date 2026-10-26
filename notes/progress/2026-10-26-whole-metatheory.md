# 元の Yulang 全体のメタ理論：2026-10-26 の証明と未解決義務

対象は `momota1029/yulang` の `yulang3`。今回の開始点は
`a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`。
元の全 source、完全 Call、Effect、一般化、各 use、将来の利用を含む
soundness・Effect 衛生性・principality・推論停止性を対象とする。

**全体証明は未完了。** 今回は四つの具体的な証明を追加した。
これらの局所定理が Lean を通ることと、元言語の主定理の前提がすべて
供給されたことを区別する。元言語の定義や supported domain を狭めて
全体証明と呼ぶ変更は行っていない。

## 1. 主定理の現在地

| 対象 | 今回の具体的な前進 | 元の全言語についての状態 |
| --- | --- | --- |
| 宣言的／推論 soundness | 既存の source publication・生成 use・owner 操作の具体的な不変条件を追加し、下記の変換・停止証明を接続可能にした | **OPEN**。全 source の独立した意味解釈、完全 Call、同じ scoped witness、実 native 成功との対応が必要 |
| Effect 衛生性 | 元 publication の frame/path/value の由来、owned return 後の失効、Name による履歴保存、scope 変換の順序付き代数を証明 | **OPEN**。全 source/world/resume/compaction との対応は残る |
| Principality | 既存の全有限 use 変換に対する共同解の降下の必要十分条件と逆方向を証明し、非単射の二 use 例を実際に構成 | **OPEN**。元 source から条件を満たす一つの戦略と principal scheme/order を構成する必要がある |
| 推論の停止性 | 実 Context scan の整礎性、fuel に依存しない全域関数、成功／拒否を含む有限実行、生成履歴からの child-ID 順序を証明 | **OPEN**。scan 後の callback、新規 allocation、Replay、extrusion/intrusion、一般化を含む全遷移の進捗が必要 |

根拠となる元の定義は
[`Contracts.lean`](../theory/lean/YulangClosure/Contracts.lean)。
`SourceProblem.Elaboration`、`InferenceSoundness`、`SourceScopedCoverage`、
`PrincipalCoverage`、`NativeCorrespondence`、`InferenceTermination` は
要求を表す `Prop` の定義であり、具体的な元言語の証明済み instance
ではない。既存の [`CoreComposition.lean`](../theory/lean/YulangClosure/CoreComposition.lean)
による合成も、その独立した前提を要求する。

## 2. Scope 変換の正確な合成則

証明は [`NativeScopeTransformer.lean`](../theory/lean/YulangClosure/NativeScopeTransformer.lean)。
対応する実装は [`candidate_scope.rs`](../../crates/yu-solver/src/candidate_scope.rs)、
意味の選択は既存の
[`compose` release 構成](../theory/2026-10-15-compose-scoped-release-construction.md)
と [採用済み設計](../design/2026-10-15-compose-scoped-effect-release.md)。

入力タグ集合を I、既存の保護集合を P とする。変換器は追加タグ J と、
各 scope s の `(keep_s, M_s)` を持つ。証明した内容意味は次のとおり。

```text
I' = I ∪ J
s ∈ P' ↔ (s ∈ P ∧ keep_s) ∨ ∃ tag ∈ M_s, tag ∉ I
```

missing-tag の判定には、変換前の入力 I を使う。第1変換の後に第2変換を
実行する合成は、各 scope について次を満たす。

```text
J12    = J1 ∪ J2
keep12 = keep1 ∧ keep2
M12    = (if keep2 then M1 else ∅) ∪ (M2 \ J1)
```

`evaluate_then` は、この具体的な計算から
`evaluate(T1.then T2, state) ≈ evaluate(T2, evaluate(T1, state))`
を証明する。`≈` は入力と保護の要素関係の一致であり、非正規なリストの
構文的同一性ではない。

`protect_then_release` は新たな保護と既存の保護の両方を解除する。
`stamp_then_protect` は既に刻印されたタグによる新規保護を抑制するが、
既存保護まで消さない。有限列の実行と合成の一致、順序を保った結合則、
新しく現れた保護がその実行列中の適用可能な guard に由来することも証明した。

名前替え `evaluate_rename` は、変換器と入力状態の双方で共有する一つの
単射 scope map と単射 tag map の下で成立する。
`local_support_injection_is_insufficient` は、変換器に現れる scope だけでの
単射性では足りないことを具体例で示す。`release 0` の外部にある保護 scope 1
を scope 0 に潰すと、名前替えと解除が可換でなくなる。
これは局所 support 検査から大域的単射性を導く誤った橋を退ける例であり、
実 source allocator がそのような map を生成するという主張ではない。

この結果は Rust の sorted-vector loop、allocation failure、実 native caller
からの map 構成まで検証するものではない。generic な carried witness を
丸ごと保存する定理も、元の Call/world の witness を新たに構成してはいない。

## 3. 元 publication と owner の Effect 衛生性

証明は [`OriginalEffectHygiene.lean`](../theory/lean/YulangClosure/OriginalEffectHygiene.lean)。
既存の `OriginalSourceGeneration`、`SourceIdentityWorld`、
`NativeClosureEnvironment`、`PaperTypeSubstitution` の定義をそのまま使う。

- publication lookup と、復元環境での固定 event の `executionValue` lookup
  の成功から、同じ元の publication record、binder、entry path、frame および
  保存された完全な value の由来を取り出す。
- 単一 binding の実 `publicationValid` が成立すると、元 publication から
  replay を構成できる。必要な binder と entry path に合う保存 frame が
  なければ lookup は拒否される。
- `description.isEvent = false` を満たす記述環境の拡張は、保存した replay
  を保つ。`.invocation`、`.rigidOperation`、`.response` への拡張は replay を
  消し、その新しい scope で replay value を取得できなくする。
- 生成された `newUse` について、source と client を同じ instance frame の
  下で再構成し、元 publication を保つ。元の共同 satisfaction の前提は残す。
- owned return が invocation owner を無効化した後、Name の読み取りで
  その owner が再び有効にはならない。同時に古い receipt は保存される。
- 型代入は operation の宣言 identity を変えず、別宣言を同一視しない。

Native の三定理は `Site : Type` を任意に取る。古い receipt が存在することを、
現在の owner の活動や capture/resume 権限に読み替えていない。

全 Effect 衛生性には、元 `Kernel.atom`・`admitted` の真正な解釈、
event-parent の整合性、複数 binding／再帰群、現在 world を使う再開、
任意代入・compaction における相関の維持がさらに必要となる。
operation identity の補題だけでこれらを代用しない。

## 4. 既存の有限 use に対する共同解の降下

証明は [`OriginalPrincipality.lean`](../theory/lean/YulangClosure/OriginalPrincipality.lean)。
元から存在する `Generalization.transport` を T とし、canonical quotient
から `T(T(i)) = T(i)` を証明した。新しい推論算法は定義していない。

元の全座標 valuation を ρ とする。次の必要十分条件を証明した。

```text
(∃ σ, ∀ kind i, σ(kind, T(kind,i)) = ρ(kind,i))
  ↔
(∀ kind i j, T(kind,i)=T(kind,j) → ρ(kind,i)=ρ(kind,j))
```

右辺が `FiberConstant T ρ`。T が同一視する座標に、ρ が同じ型を割り当てる
という条件である。逆方向では代表上の ρ 自身を使って σ を構成するため、
各 use や各 port で別々の witness を選んでいない。

既存の post-to-pre sound pullback に加え、`quotient_uses_complete_on_fiber`
は全 base/use/client store の pre-model から post-model を実際に構成する。
canonical quotient、store bounds、低位 anchor の保存、use bounds と明示した
fiber constancy が前提となる。
`joint_solution_coverage_iff` は valuation 全体の任意の観測 O について
次を与える。

```text
∃ σ, Post(σ) ∧ O(σ ∘ T)
  ↔
∃ ρ, Pre(ρ) ∧ FiberConstant(T,ρ) ∧ O(ρ)
```

`TwoUseExample.constructive_two_use_descent` は前提なしの具体例。
row 2 を row 1 にまとめる非単射 quotient を使い、value/effect 両 kind で、
元 row 1/2 は atom 2、第1 use の 4/5 は atom 0、第2 use の 7/8 は atom 1、
将来 client 9 はその union とする一つの valuation を構成した。
四つの Function port、optional/required record field、tuple、variant と
全12 clause を保持している。

この局所結果を元 principality へ接続する一つの経路は、元 source に由来する
共同戦略から fiber 条件を導くことである。元の `instanceOf` による principality
自体の必要条件と同定したわけではない。「すべての任意の旧 valuation を保存する」
ことも元の要求ではない。現行の immutable birth-level SCC 資格、実際の
retained parent/copy と受け手の対応、`freshenAbove` の reachable copy、
完全 Call/effect/evidence、元 `instanceOf` の順序も接続する必要がある。
有限の use/client family ごとに得た解を、一つの戦略がすべての将来 family
に整合するという量化に無断で強めない。

## 5. Context 走査の停止性

証明は [`OriginalInferenceTermination.lean`](../theory/lean/YulangClosure/OriginalInferenceTermination.lean)。
既存の `NativeContextExpansion.scanStep` の成功する一歩について、
未処理 stack の rank `Σ 3^id` が必ず小さくなる。
二つの子を持つ Replay でも、子 ID が親より小さいため
`3^left + 3^right < 3^parent` となる。
不正な table は既存の guard で拒否されるため、scanner の整礎性に
table acyclicity や成功する有限 transcript を仮定する必要はない。

この減少量から、fuel を引数にしない `scanTotal` を構成し、
`scanRank state ≤ fuel` なら既存の `scanLoop` と結果が等しいことを示した。
単一 root の場合、`3^root` は十分な fuel となり、さらに増やしても結果は
変わらない。成功と拒否の双方を含む有限実行も構成した。
これは証明用の十分な上界であり、実装に追加した実行制限でも最適計算量でもない。

`NativeContextTables.Store` の実 constructor/history から strict child-ID
順序を導き、commit、cancel、数値 ID の再利用でも保存した。
ready marker を使う走査には、未処理 frame を `4^id`、ready frame を 1 と
する別の rank を与え、実装中の二通りの stack 順序と完了済み child の
filter を含む control projection の整礎性を証明した。

**証明した scan は `candidate_zero_word_filters` の stack loop であり、
その後の `consume(self, &filters, residual)` callback の停止を含まない。**
callback は新規 bound や Replay を生成できる。fold/rename の control
projection と Rust の refinement、callback 自体の評価も別の義務として残る。

既存の `NativeDrainOwnership.Step` は任意の `reserveOther` を許すため、
その projection はどの状態でも accessible ではないことも証明した。
これは conservation 用の抽象関係を元推論器の停止関係に転用できない理由であり、
元 Yulang の発散プログラムや推論の非停止反例を発見したという意味ではない。

元 `InferenceTermination` が必要とするのは、すべての supported source の
実初期状態からの、実推論遷移全体の accessibility である。現在の Lean
にはそれを供給する具体的な全言語 `SourceProblem` instance がない。
その構成と、allocation、extrusion、intrusion generation、Replay、capture、
一般化を含む大域的な進捗証明が必要となる。

ここでいう停止性は推論算法の停止性。一般再帰を含む元言語について、
すべてのプログラム実行が停止するという主張はしていない。

## 6. 全体 soundness の最初の未接続点

既存の [`OriginalSourceGeneration.Kernel`](../theory/lean/YulangClosure/OriginalSourceGeneration.lean)
には atom、admission、primitive check、shape、boundary、conversion という
独立した意味の入力がある。
[`OriginalSourceInterpretation`](../theory/lean/YulangClosure/OriginalSourceInterpretation.lean)
は V/W/T/Car の正の作用素と最大不動点を構成する一方、元の domain、
guard、profile、scope、current authority、incidence 等の入力を残す。
今回の由来や代数の証明だけでは、それらすべての真正な解釈は構成されない。

また native success と論理的解の存在の橋には、同じ実 operation/worklist/
frame/rollback 履歴からの accepted-drain と完了の証拠が必要となる。
過去に enqueue されたこと、owner が登録されたこと、scalar model の存在、
Rust の `Ok` だけでは、完全 Call と元 source の同じ scoped witness は得られない。

したがって全体を閉じる順序は、元 source/world/Call の入力を具体化し、
同じ native 履歴の成功・完了から元 source 導出を再構成し、その上で
source strategy・principal ordering と全推論遷移の進捗を証明することになる。
今回の四定理は、その各接続で必要となる具体的な局所義務を減らした。

## 7. 統合と検証

統合対象は [`WholeMetatheory.lean`](../theory/lean/YulangClosure/WholeMetatheory.lean)。
既存の公開 root は変更せず、通常の default target にこの import surface
を追加する。新しい全件監査は
[`AuditWholeMetatheory.lean`](../theory/lean/AuditWholeMetatheory.lean)。
namespace の名前だけで絞り込まず、実際の originating module ID を使い、
private/generated theorem と他 namespace に生成された equation も列挙する。
全型と全公理一覧を出力し、project axiom と標準外の間接公理依存を拒否する。

固定版 Lean **4.35.0**、commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` で、次がともに exit 0。

```sh
cd notes/theory/lean
lake --no-cache build
lake --no-cache env lean -j1 -M1536 AuditWholeMetatheory.lean
```

通常 default build は **105 jobs**、435.8秒。全件監査は7.4秒で完了した。
通常ビルドの `-j1 -M1024` と pin/dependencies は維持し、監査だけに既存の
task-local 1.5 GiB 設定を使った。toolchain の新規 install はしていない。

| 追加モジュール | 実 originating theorem constants |
| --- | ---: |
| `NativeScopeTransformer` | 107 |
| `OriginalEffectHygiene` | 24 |
| `OriginalPrincipality` | 36 |
| `OriginalInferenceTermination` | 75 |
| 合計 | **242** |

242件の BEGIN/END が重複なく同じ順序で対応し、すべてに全型と完全な
axiom report があることを別途照合した。必須の主要18定理も含まれる。
generated/private helper を含む数であり、人手で書いた主張の数や
全言語証明の完成率を表してはいない。証明本体はビルド時に kernel が検査する。

| 依存する公理の正確な集合 | 件数 |
| --- | ---: |
| なし | 74 |
| `propext` | 33 |
| `propext`, `Quot.sound` | 122 |
| `propext`, `Classical.choice`, `Quot.sound` | 13 |

全242件の依存に標準外の公理や `sorryAx` は現れず、unchecked native
evaluation や kernel bypass も用いていない。choice を使う13件は Effect モジュールとその依存からの
もの。今回の証明を「公理なし」とは報告しない。
新規モジュールと全件監査に warning/error はない。
通常ビルドの既存668 warnings は次の9ファイルに属し、全ファイルが
開始点と byte 単位で同じであることを `git show` と比較した。

| 既存 warning の所有ファイル | 件数 |
| --- | ---: |
| `PaperExecutionSyntax.lean` | 23 |
| `PaperExecutionBinderLaws.lean` | 235 |
| `ControlComposition.lean` | 3 |
| `PaperTermSubstitution.lean` | 96 |
| `PaperCoreStep.lean` | 4 |
| `PaperTypeBetaExecution.lean` | 276 |
| `PaperTupleSplitExecution.lean` | 22 |
| `PaperPerformLetExecution.lean` | 2 |
| `NativeIntegerComparison.lean` | 7 |

検証時に列挙した164個の Lean source/config 入力を検証前後で再 hash し、一致を確認した。
新規四モジュールの監査であり、未供給の元 source 前提や別の未接続な
研究 packet まで自動的に証明済みにするものではない。
Rust/compiler コードは変更しておらず、新しい Cargo 検証結果も主張しない。

完全な出力を repository に保持する。

- [通常ビルドの全ログ](evidence/2026-10-26-whole-metatheory/whole-default-build.log)
  — SHA-256 `8943f3a2ac04dbed0511db345124d417ef378c4db5d8358af63948214480552b`
- [全型・全公理の監査ログ](evidence/2026-10-26-whole-metatheory/whole-audit.log)
  — SHA-256 `bae70a7f09b26cea1db092f75561546bb5fe085b8653c666f07a3d777a802ab4`
- [164入力の hash 一覧](evidence/2026-10-26-whole-metatheory/integration-input-hashes.json)
  — SHA-256 `56badefc5d6ad94b1059762fb8810cdae647e2bef9d5501d39d592f3d133d391`
- [定理ごとの origin・公理と検証結果](evidence/2026-10-26-whole-metatheory/verification.json)
  — SHA-256 `bd30db9eb83f971d7c040b1282e5cfb225eb18ea0ceb0cf1db14b9e01a2debf5`

## 8. 独立レビューと checkpoint

| 構成 | 著者 | 独立レビュー | 公開済み checkpoint |
| --- | --- | --- | --- |
| Scope transformer | `/root` | `/root/principality`、ACCEPT | `de313acb2bcfc193596898478caa3ad578b91d8d` |
| Original principality | `/root/principality` | `/root/effect_hygiene`、ACCEPT | `61d78978c3191905fa0cfad6efb3ab5e5c7ddee3` |
| Original Effect hygiene | `/root/effect_hygiene` | `/root/principality`、ACCEPT | `974fa71273ee5c4091b02911f51175493b1eac76` |
| Original inference termination | `/root/termination` | `/root/effect_hygiene`、ACCEPT | `df30b46027c89a07241d5549921016578855aaa0` |

各 ACCEPT は正確な frozen source と明記した局所範囲についてのもの。
全言語の主定理に未供給の前提まで承認したという意味ではない。
生産・レビューの詳細は次に記録する。

- [Scope の handoff](../../tasks/agent-loop/inbox/20261026-whole-scope-transformer.md) と
  [独立レビュー](../../tasks/agent-loop/inbox/20261026-whole-scope-review.md)
- [Effect の handoff](../../tasks/agent-loop/inbox/20261026-whole-effect-hygiene.md) と
  [独立レビュー](../../tasks/agent-loop/inbox/20261026-whole-effect-hygiene-review.md)
- [Principality の handoff](../../tasks/agent-loop/inbox/20261026-whole-principality.md) と
  [独立レビュー](../../tasks/agent-loop/inbox/20261026-whole-principality-review.md)
- [停止性の handoff](../../tasks/agent-loop/inbox/20261026-whole-inference-termination.md) と
  [独立レビュー](../../tasks/agent-loop/inbox/20261026-whole-inference-termination-review.md)

説明文にも別の read-only claim audit を行った。publication lookup だけでは
frame の存在は導けないという指摘を受け、§3 に実 `executionValue` lookup
の成功前提を追記した。§4 も、固定 transport に対する exact factorization
の必要十分条件を、元 `instanceOf` principality 自体の必要条件とは
同定していないことを明記した。受理済み Lean の定理には元から正しい前提が
あり、この修正は説明文だけである。

import surface・監査コード・manifest の限定差分にも、著者以外による
[独立した統合レビュー](../../tasks/agent-loop/inbox/20261026-whole-metatheory-integration-review.md)
を実施し、ACCEPT を得た。receipt の SHA-256 は
`79e8e8c0ebc38fb552a373f58b2cf3c849d3e3f2720ac16ad58930f0b4cc2c88`。
reviewer は全242件の型／公理 record、18 roots、全ログと入力 hash を独立に照合した。
自身が著した停止性の数学的内容はこのレビューから除き、その内容は別の
Effect 担当 reviewer の受理範囲に属する。新たな主定理の前提は導入していない。

元の reserved root、過去の task history と別の scheduling state は保持する。

## 9. 並行更新を保持した最終統合

最終反映の直前、別の作業が
`5030137eb5a0e3eaa49dc28bb590223505a44731` を同じ branch に追加した。
今回の四つの proof checkpoint を祖先に持つ通常の更新であり、
`NativeRelationInterner.lean` とその note／handoff／review、既存 r4 ledger
の5ファイルを変更していた。すべて fast-forward で保持した。

今回 stage した11ファイルの blob は fast-forward 前後で完全に同じであり、
検証済み164入力もすべて同じだった。追加の `NativeRelationInterner` は
検証済み source と今回の default-target globs に import／参照されていない。
このため今回の検証対象に変更はなく、無関係な追加証明をこの242件の
監査結果で再認定したとも扱わない。追加 module の SHA-256 は
`1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a`。
元の164件の inventory とレビュー receipt は、実際に検証した時点の証拠として保持する。

続く `0e1fb99abc8a94a888889e20c2614a68a749461b` も fast-forward で保持した。
これは `NativeValueRelationExecution.lean` と対応する note／handoff／review、
同じ r4 ledger の更新である。この追加にも、検証済み164入力や今回の
stage に変更はなく、追加 module はその source／default target から参照されて
いないことを確認した。二つの並行更新の数学的範囲はそれぞれの独立した
記録に属し、今回の四モジュールの検証範囲を広げて報告してはいない。
