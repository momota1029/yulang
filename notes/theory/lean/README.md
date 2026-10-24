# Yulang closure: Lean root composition

LEAN-ROOT-20261024/r2。**元 Yulang 全体の証明は未完了**。本ディレクトリは guide §3 の有限 prefix 合成を、独立した一段の意味論・型・抽象化 interface に分解した最初の Lean 化である。Lean 4.35.0 による検査済み。独立査読は条件付き合成の範囲を受理した。

## 構成

- `YulangClosure/Contracts.lean`: parameterized machine、現在 world の resume、有限 cell interface、certificate、独立な一段 laws、birth-level induced graph、未具体化の source/inference roots。
- `YulangClosure/CoreComposition.lean`: `initial_invariant`、`step_invariant`、`prefix_invariant`、`finite_prefix_composition`、`run_at_every_time`、`saved_reusable`。

`LocalLaws.typing` は result index を持つ独立 judgment。`laws.result` を全 prefix と resume に固定する。`typed` を safety/reachability と定義していない。具体的型導出はまだパラメータであり、その妥当性をこの抽象証明から得ることはできない。

`Certificate` の seed inclusion、cell edge closure、output inclusion を別々に要求する。`Analysis.index_injective` は有限 cell domain の独立入力。実行長に有限上限を置くものではない。`Invariant` は型証拠と一つの joint concrete/cell witnessを束ねるだけであり、machineの型定義ではない。

## 証明する条件付き命題

独立な初期型付け、initial seed、internal preservation、typed resume formation、各one-step simulation、観測解釈、local progress/noBad が与えられると、任意長の `Prefix (Step m)` の末尾で同じ result typing、Uへの包含、全exposed output契約、Bad除外が成り立つ。末尾は Ret/Req/言語上のFail/次のinternal stepのいずれか。Reqに応答が来ることや、Failから正常復帰することは主張しない。

`Step.resume` は source configuration の suspension、現在 world、独立 admissibility、同じ saved packet へのactual resume relationを使う。現在 worldを保存時worldと等置しない。`saved_reusable` は同じ kを二つの別configuration/world/responseに用いる。kが各時点で利用可能であることは明示した `suspended` 前提であり、この定理がcontinuationを作ったり、寿命を延ばしたりすることはない。元Kのimmutable fieldsをモデル化し、その保持と各時点のavailabilityを実constructorから証明する義務は残る。長いsequenceでは `prefix_invariant` と `run_at_every_time` が任意個のresume stepsを扱う。

全現在観測は `Machine.exposed` に含める必要がある。もし具体的machineがstep-labelにのみeventを記録するなら、その全labelをconfigurationのobservation portに対応させる具体simulationが必要。観測の欠落を抽象定理で正当化しない。

`SourceProblem.native_success_elaborates` は native success、推論 soundness、elaboration の三つの独立義務を接続し、同じ source scope/witness の core judgment まで運ぶ。三義務自体の証明と、その core judgment から具体的 `LocalLaws.initial` を得る接続は未完である。

## 元の証明への concrete instantiation map

| Lean interface | 元ownerと必要な具体証明 |
| --- | --- |
| Machine / Step | corrected coreの全control、七frames、Ret/Req/Fail/Bad、raw resume。追加transitionを漏らさない exact graph/observation対応。 |
| typing/result/initial_typing | V1–V5と元source/evidence typing。保存K/内部codeの型を外部仮定に移さない。 |
| initial_seed / finite Analysis | G1、I1–I6。実instance/type equalityを有限colorと同一視しない。 |
| internal_preservation/progress/no_bad | V5/V6。型不整合と許された言語上のFailを区別する。 |
| internal_simulation | G2–G5、I、CM、H。両query filters、No-current-world rejoin、selected/forwarded handler continuations、release Ret/Req/Failを全caseで具体化する。 |
| resume_formation/resume_simulation | V4/V7、G3、CM rejoin。同じimmutable K、現在L/activity、actual response instance、未完suffix。過去receiptをreplayしない。 |
| observation / cert.outputs | Hと同じcursor/instanceのΦ。別pathの許可を転用しない。 |
| Qualifies | immutable Value birthの各level誘導graph内での双方向path。元cross-level Refは削除せず、pathの全verticesをfilterする。実occurrence/pairsとのsource/native対応は別義務。 |

**最初の欠落**は、具体的な corrected-core configuration/typing/transition/observationを Lean の型として定義し、その独立 judgment を `Machine` と `LocalLaws` に与えること。現時点では paper theoremをaxiomとして登録していない。表の各fieldを実際のconstructor inductionで埋めるまでは、Yulangへの有限prefix適用も条件付きである。

## 別の元root義務

`SourceProblem.Elaboration`、`InferenceSoundness`、`SourceScopedCoverage`、`PrincipalCoverage`、`NativeCorrespondence`、`InferenceTermination` は**命題の定義**であり、証明やaxiomではない。source scopeとwhole共有witnessを保持する `sameScoped` の具体化が必要。これは点ごとの任意native valuation一致や、独立useごとの別hidden witnessを許す関係ではない。principal instance ordering、元のsupported domain、同じ証拠を含む全future familyを元契約通りに具体化する責務が残る。

`supported` は元の対象構文の域であり、型付け可能性ではない。PrincipalCoverage は実 source derivation が存在する入力について principal solution を要求する。型付け不能な全入力にも解を要求する r1 の前提不足を primary が修正した。Terminationは元supported sourceのactual inference initial statesからのalgorithmic accessibility。program評価の停止は主張しない。native successからsource judgmentへのbridgeも独立であり、scalar modelの存在から推測しない。元A/Bの正確なsource-scoped strategy/publication/use量化は frozen source-preservation稿へ戻して定義を具体化する必要がある。

## 再現と検査結果

`lean-toolchain` は `leanprover/lean4:v4.35.0` に固定する。Mathlibなどの追加パッケージ依存はない。Lean/Lake を使用できる環境で、このディレクトリから次を実行する。

```sh
lake build
lake env lean -j1 -M1024 YulangClosure.lean
```

primary は公式 Linux 配布物を task-local directory に展開し、配布 SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` を照合した。Lean は `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。各 module を `lean -j1 -M1024 -o …` で依存順に検査し、続いて `lake build` も exit 0 で完了した。root file の四つの `#print axioms` は、全て `does not depend on any axioms` を返す。これは引数として受け取った `LocalLaws` 等の前提を不要にする表示ではなく、公理宣言への依存がないという意味である。

最初の checker 実行は prefix 帰納で一般化された初期不変条件の引数不足を検出した。primary が帰納仮説へ `hc` を渡すよう修正し、再検査した。具体的 Yulang の各一段則や元 root 義務はまだ parameter なので、上の結果は条件付き合成の検査結果である。

## 依存・検査・handoff

契約 `tasks/agent-loop/sprints/lean-root-20261024.md` SHA-256 `7451ae9aabdd8efe26732903e0fc6a52b7975bcd6a3e7693175f47887dece0b9`。8 frozen input hashesを照合し全一致。main guide §3、G/I/V/CM/Hとbirth-level designを参照。AH/RZの未査読draftは依存にしない。

producer `/root/astra_corrected_machine`、primary の型index/現在worldの監査と停止後修正・source接続定理を含む共同構成。requested inherited Astra/medium、observed model/effort/elapsed UNKNOWN。190秒/3stages、延長なし。primary提供のtask-local Lean4.35.0でproducer STOP後に検査した。本freeze時点でproducerによるLean checker実行はなし。証明termの構築とkernelでの受理を区別する。primaryの限定checkと主要theoremの `#print axioms` は上記に記録し、停止後修正の共著を明記する。sorry/admit/project axiomsは追加していない。

三つのleased files以外のwrite、scratch、compiler implementation、tests/probes/network/Git、descendantsなし。primaryのproject/config/build filesは別lease。**producer writes STOPPED at frozen handoff**。最終hashはhandoff messageに記録する。独立reviewは条件付き合成の範囲を受理した。元whole goalはOPEN。


### 独立査読の受理範囲

`/root/astra_semantics_review` は frozen r2 の全出力 hash と契約を照合し、条件付き合成として受理した。BLOCKING/MAJOR 指摘なし。二つの step case、同じ result index、current world、同じ K の各使用に別々に必要な availability/admissibility、全頂点を filter する birth path、同じ source scope/witness と typable-input principal guard を確認した。レビュー担当は著者ではなく、checker は再実行していない。Lean の実行結果は primary の実 receipt である。受理後の本 README の変更はこの status/receipt のみ。

固定版・producer r1・primary r2・最終 hash、未具体化の義務は [sprint outcome](../../../tasks/agent-loop/sprints/lean-root-20261024-outcome.md) に記録する。
