# Yulang closure: Lean root composition and control

## 2026-10-26 continuation: construct terminal inference evidence

`SimpleSubRegularDecision` constructs a finite certificate directly from the
existing regular graph. `constructed_exact` proves that its members are exactly
the independent all-depth `RegularSub` comparisons; `decideDemands_exact`
includes full graph validity even for empty demands. The history/publication
application uses this computed certificate instead of an externally supplied
pair table. This proof-side reference construction does not replace native
Simple-sub inference or introduce a production checking pass.

The independently reviewed checkpoint passes the default build (68 jobs) and
all 884 originating theorem audits across nine inference modules. See the
[continuation record](../../progress/2026-10-26-inference-evidence-construction.md)
for original scope, remaining native/source premises and subsequent construction.

`SimpleSubRegularGraphExtension` and `SimpleSubRegularCompletion` now construct
missing finite nodes and derive actual decoder success. Existing graph tables
remain literal prefixes, so old cyclic references and first exact-node matches
are preserved. Completion includes all four Function ports, nil/suffix nodes,
record optional bits, and complete tuple/variant payloads. Its explicit inputs
are graph validity and actual variable lookup/row-shape/uniqueness facts, not a
model or decoding equation. The completed publication theorem retains one graph
and one reference assignment for the whole inventory and all clients.

The independently reviewed [native profile restriction proof](../2026-10-26-native-profile-hereditary-restriction.md)
constructs the generated-profile hereditary transport through the actual native
license grammar and applies it to fresh ValueBind/Name Call. The separate
`NativeProfileRestriction` module checks its dependent-record equations. The
original native grammar induction is a paper proof; the companion does not
claim to formalize that grammar or construct a full original Call certificate.

`SimpleSubGrowingInference.completed_growing_publication_with_clients` connects
completion and computed terminal evidence while allowing exact constraint steps
to interleave with literal graph allocation. Earlier steps and decoder results
are transported into one final graph, preserving all original numeric references
and one shared pullback for every use and client. Actual native mutable-row,
activation and source evidence remain separate correspondence obligations.

`SimpleSubLatticeCertificates` extends that structural graph with actual
union/intersection nodes and finite derivations of the existing lattice rules.
Only structural ports may consult the shared recursive relation; lattice and
transitivity premises are finite same-depth derivations. Checked certificates
therefore construct an independent all-depth interpretation for guarded graphs,
including structural cycles through both lattice constructors and both effect
ports. The unchanged regular interpretation embeds one way. `Layer.toSub`
separately proves each finite rule's correspondence under explicit finite
readback equations; no finite readback is asserted for cyclic graphs. Original
unguarded syntax, native extraction, ordinary coalescing and full source/Call
soundness remain outside this component. The accepted
[independent review](../../../tasks/agent-loop/inbox/20261026-inference-lattice-review.md)
covers every originating declaration and the original rule comparison.

`SimpleSubLatticeInference` connects those certificates to every existing
`SimpleSub.Term` constructor, actual graph-indexed extrusion/constraint histories
and the unchanged original scoped-publication theorem. Lawful constructor
completion now creates missing union/intersection, Function, finite row and
payload nodes and derives the joint decoder equation. Final graph validity and
guardedness come from acceptance; prefix retention alone does not establish
them. Old histories and decoder results have proved translations into the
extended graph. Native row formation/width, inventory and metadata coverage,
coalescing and the original jointly scoped source/Call evidence remain open.

`SimpleSubLatticeDecision` now computes the full finite rule-witness certificate
from the graph alone. Both inner saturation and outer pruning have proved
strict-decrease bounds. On valid graphs, `constructed_exact` identifies table
membership with the independent all-depth lattice relation; `regular_unfold`
is derived afterward using the finite shared table. Demand acceptance is
equivalent to validity, the actual guard check and every demanded relation.
This is an exact proof-side reference construction, with no assumed model or
external witness table and no production inference algorithm change.

The [original Call evidence construction](../2026-10-26-original-call-evidence-construction.md)
now gives a reviewed ten-field **unadopted** candidate, tied to the actual
source/phase, independent-arm, native-profile, routing and accounting consumers.
It separates constructor-selected meanings from separately fixed host
interpretations and names their exact required maps. Its local reconstruction
uses the unchanged full `G_call` solution's already supplied original
certificate and the same scoped witness. This is a paper result; it neither
redefines the original certificate nor supplies an all-source Lean instance.

## 2026-10-26: inference constraint soundness and scoped publication

`YulangClosure.InferenceProofs` is included in the default library build.
Its independently reviewed components address the original inference goal:

| Component | Constructed result |
| --- | --- |
| `BirthLevelSCC` | Executable finite/helper graph qualification agrees with the original immutable-birth induced-path predicate. |
| `SimpleSubConstraintSyntax`, `SimpleSubConstraintSoundness` | Directed extrusion links, concrete constraint histories, retained occurrence equalities, and one-valuation quotient reflection. |
| `SimpleSubGeneralizationSoundness` | One transport across finite uses, shared anchors and clients, with exact canonical minima and fresh-coordinate bounds. |
| `SimpleSubRegularSolutions` | A finite graph/certificate check constructs an independent all-depth regular interpretation, including genuine structural cycles. |
| `SimpleSubRegularConstraintSoundness` | Final acceptance reconstructs every original demand through concrete regular histories, with no supplied terminal model. |
| `SimpleSubScopedPublication` | Transported original clauses occur in the retained base or copies of reached local owners; actual capture/current/non-generic guards are distinguished. |
| `SimpleSubRegularPublication` | Executable finite term decoding connects the regular history and scoped-publication results, constructing one regular interpretation for all original uses and clients from terminal certificate acceptance. |

From this directory:

```sh
lake build
lake env lean -j1 -M1024 AuditInferenceProofs.lean
```

The integrated default build passed 67 jobs with pinned Lean 4.35.0. The complete
eight-module audit checked all 847 originating theorem constants, including
private/generated helpers, with only standard `propext` and/or `Quot.sound`,
or no axioms. Independent reviews and their resolved minor findings, exact
source hashes, actual theorem premises, native correspondence and verification
receipts are in the [inference proof record](../../progress/2026-10-26-inference-soundness.md).

The same work corrects the implemented birth-level SCC filter and passes 44
focused Rust tests. **Original whole-source inference soundness remains OPEN.**
Native graph/trace/certificate extraction, all-history publication metadata
closure, complete constructor/coalescing coverage and the original contextual
Call/effect/source witness still need their actual proofs. A full original
`G_call` solution already contains its decorated certificate; the existing fixed
decorated-rule reconstruction may consume it. The initial structural decoder
requires exact existing constructor and finite suffix/payload nodes and rejects
union/intersection. The follow-on construction above supplies lawful completion
and an extended lattice decoder; actual native coverage remains open.
Producing the full original solution
from actual native success and covering all original source constructors are
distinct remaining obligations.

## 2026-10-26: substitution, call entry, allocation and integer arithmetic

Four additional modules advance the original obligations without changing
existing judgments or compiler behavior:

- `PaperTermSubstitutionAlgebra.lean` proves identity/composition and type/term
  commutation for the existing raw operations, exact graph-formal and response
  substitution, and composition of the typed partial APIs.
- `PaperCallEntryFormation.lean` constructs the actual same-owner entry code
  for both lambda modes and arbitrary finite wrapper spines. It also proves the
  exact `Force(View ...)` frontier of the current partial executor.
- `PaperAllocationExecution.lean` derives finite execution and saved-response
  typing across actual fresh allocations, with responses checked in the current
  graph and a concrete reusable-continuation example.
- `NativeIntegerArithmetic.lean` proves the arbitrary-width carry/borrow
  algorithm computes addition/subtraction, including exact String decoding,
  and applies it to the existing completed native-request theorem.

The default library retains its original root and adds the explicit
`YulangClosure.ProofAdvancement` glob. Ordinary `lake build` includes all four
modules; the reserved original root file is unchanged. The integrated default
build passed 58 jobs using Lean 4.35.0. Run the complete new-module audit with:

```sh
lake build
lake env lean -j1 -M1024 AuditProofAdvancement.lean
```

All 538 module-originated theorem constants, including private/generated
helpers, passed type and axiom inspection. Dependencies contain only the
standard `propext`, `Classical.choice`, `Quot.sound`, or none. Non-author review
accepted each stated scope. The [proof record](../../progress/2026-10-26-yulang3-proof-advancement.md)
contains the exact improvements, hashes, evidence and review receipts.

Whole-language progress, full Force/View/scope and nonempty-owner/current-world
execution, guardedness, remaining source/native correspondence, and original
inference A/B remain OPEN. Raw substitution equations preserve the existing
opaque fallback; they do not assert coverage of omitted source constructors.

## 2026-10-26: explicit execution proof extension

`PaperExtendedExecution.lean` connects actual type application, registered
template expansion, repeated empty-owner response/resume, and literal failure
unwinding to one deterministic executor. Its preservation and finite-interaction
theorems retain the same declarations, graph environment, lexical environment
and final result type. Registered bodies are independently typed; foreign
responses are checked against the actual request instance. Internal preservation
is proved from the execution function rather than supplied as a law.

The supporting modules are `PaperTypeApplicationPreservation.lean` (arbitrary
type-binder-block cancellation), `PaperTemplateExecution.lean` (actual lookup,
arity checks and simultaneous expansion), and `PaperCombinedExecution.lean`
(concrete repeated interactions and failure). The explicit paper judgment and
all its substitution/weakening recursors also now include intersection choose
and Bottom elimination; `PaperEliminationExamples.lean` checks polarity, binder
capture and actual execution. False selects left and true selects right.

The default root imports these modules and passed `lake build` with Lean 4.35.0
(49 jobs). From this directory, run the committed complete module audit with:

```sh
lake build
lake env lean -j1 -M1024 AuditExecutionProofs.lean
```

The audit checks all 1,368 theorem constants in the eleven new/changed modules,
including generated/private helpers, and the three new typing constructors.
All actual axiom lists contain only `propext` and/or `Quot.sound`, or are empty.
Independent review accepted the stated scopes; detailed hashes, receipts,
warning accounting and remaining obligations are in the
[proof record](../../progress/2026-10-26-yulang3-execution-proofs.md).

These are concrete preservation results for the represented partial executor.
Full progress, nonempty-owner/current-world resumption, guarded graph canonical
forms, remaining source/native realization and inference A/B are still OPEN.
An open Bottom assumption permits absurd typing but proves no closed-Bottom
impossibility. The historical composition results and their distinct premises
are documented below.

LEAN-ROOT-20261024/r2、LEAN-CONTROL-20261024/r1。**元 Yulang 全体の証明は未完了**。本ディレクトリは guide §3 の有限 prefix 合成を、独立した一段の意味論・型・抽象化 interface に分解した最初の Lean 化である。Lean 4.35.0 による検査済み。独立査読は条件付き合成の範囲を受理した。

## 構成

- `YulangClosure/Contracts.lean`: parameterized machine、現在 world の resume、有限 cell interface、certificate、独立な一段 laws、birth-level induced graph、未具体化の source/inference roots。
- `YulangClosure/CoreComposition.lean`: `initial_invariant`、`step_invariant`、`prefix_invariant`、`finite_prefix_composition`、`run_at_every_time`、`saved_reusable`。
- `YulangClosure/ControlSyntax.lean`: 型証拠を持たない七 frame、順序付き value/operation search、Wait、effectful mapper、Ret/Req/Fail/Bad、current-world resume。
- `YulangClosure/ControlTyping.lean`: 独立した値・frame・stack・K・packet・候補列の型付け、append/capture、run head だけを対象とする `BodyLaws`。
- `YulangClosure/ControlComposition.lean`: 全 control 保存・進行、response plugging、有限 raw trace の failure 吸収、外部 resume を含む全有限 trace の型安全性、既存 root `LocalLaws` への具体的な四つの安全性 field の供給。
- `YulangClosure/CoreSyntax.lean`: 元 constructor 名を持つ raw 木と四つの binder namespace。型付き導出は unit/variable/delay + Ret/Force/let、union/intersection/Top/Bottom の構造規則。
- `YulangClosure/CoreSubstitution.lean`: 全 raw 木に対する代入・改名の合成則、上記範囲の型付き代入、raw embedding との可換性。
- `YulangClosure/CoreExecution.lean`: 実 let/Force と枠の追加/消費、閉じた型付き範囲の進行、全 raw step の逆方向対応、任意有限 raw trace の安全性。

`LocalLaws.typing` は result index を持つ独立 judgment。`laws.result` を全 prefix と resume に固定する。`typed` を safety/reachability と定義していない。root の具体的型導出は instance ごとの責務である。Control instance は extrinsic な型規則を定義したが、元 Yulang の全値型・全 body judgment を具体化したものではない。

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

七 frame の値型制御抽象は `Control.machine` と `Control.localLaws` に接続した。`finite_trace_safety` は任意長の内部/外部 resume trace で同じ型・Bad 排除・進行を証明し、`finite_prefix_control` は既存 root に実適用する。value/operation の順序付き試行、selected/forwarded shallow K、No の現在 world、mapper adapter の通常 Req/Fail を明示的に処理する。

**残る具体化**は、全元値/graph/closure の型と代入、全 principal body 関係と `BodyLaws`、actual metadata/observation と `AnalysisLaws`、source からの初期形成である。`atom Nat Nat` は全 Yulang 値を符号化した証明ではない。terminal request だけの `exposed` も全 View/emission/latent/reentry 観測の実証明ではない。[各 constructor の対応と限界](../2026-10-24-lean-control-correspondence.md)を参照。紙上定理を axiom に登録したり、全出力を許す dummy certificate を作ったりしていない。

## 別の元root義務

`SourceProblem.Elaboration`、`InferenceSoundness`、`SourceScopedCoverage`、`PrincipalCoverage`、`NativeCorrespondence`、`InferenceTermination` は**命題の定義**であり、証明やaxiomではない。source scopeとwhole共有witnessを保持する `sameScoped` の具体化が必要。これは点ごとの任意native valuation一致や、独立useごとの別hidden witnessを許す関係ではない。principal instance ordering、元のsupported domain、同じ証拠を含む全future familyを元契約通りに具体化する責務が残る。

`supported` は元の対象構文の域であり、型付け可能性ではない。PrincipalCoverage は実 source derivation が存在する入力について principal solution を要求する。型付け不能な全入力にも解を要求する r1 の前提不足を primary が修正した。Terminationは元supported sourceのactual inference initial statesからのalgorithmic accessibility。program評価の停止は主張しない。native successからsource judgmentへのbridgeも独立であり、scalar modelの存在から推測しない。元A/Bの正確なsource-scoped strategy/publication/use量化は frozen source-preservation稿へ戻して定義を具体化する必要がある。

## 再現と検査結果

`lean-toolchain` は `leanprover/lean4:v4.35.0` に固定する。Mathlibなどの追加パッケージ依存はない。Lean/Lake を使用できる環境で、このディレクトリから次を実行する。

```sh
lake build
lake env lean -j1 -M1024 YulangClosure.lean
```

primary は公式 Linux 配布物を task-local directory に展開し、配布 SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` を照合した。Lean は `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。各 module を `lean -j1 -M1024 -o …` で依存順に検査し、続いて `lake build` も exit 0 で完了した。root 合成の四つの `#print axioms` は、全て `does not depend on any axioms` を返す。これは引数として受け取った `LocalLaws` 等の前提を不要にする表示ではなく、公理宣言への依存がないという意味である。

最初の checker 実行は prefix 帰納で一般化された初期不変条件の引数不足を検出した。primary が帰納仮説へ `hc` を渡すよう修正し、再検査した。具体的 Yulang の各一段則や元 root 義務はまだ parameter なので、上の結果は条件付き合成の検査結果である。

## 依存・検査・handoff

契約 `tasks/agent-loop/sprints/lean-root-20261024.md` SHA-256 `7451ae9aabdd8efe26732903e0fc6a52b7975bcd6a3e7693175f47887dece0b9`。8 frozen input hashesを照合し全一致。main guide §3、G/I/V/CM/Hとbirth-level designを参照。AH/RZの未査読draftは依存にしない。

producer `/root/astra_corrected_machine`、primary の型index/現在worldの監査と停止後修正・source接続定理を含む共同構成。requested inherited Astra/medium、observed model/effort/elapsed UNKNOWN。190秒/3stages、延長なし。primary提供のtask-local Lean4.35.0でproducer STOP後に検査した。本freeze時点でproducerによるLean checker実行はなし。証明termの構築とkernelでの受理を区別する。primaryの限定checkと主要theoremの `#print axioms` は上記に記録し、停止後修正の共著を明記する。sorry/admit/project axiomsは追加していない。

三つのleased files以外のwrite、scratch、compiler implementation、tests/probes/network/Git、descendantsなし。primaryのproject/config/build filesは別lease。**producer writes STOPPED at frozen handoff**。最終hashはhandoff messageに記録する。独立reviewは条件付き合成の範囲を受理した。元whole goalはOPEN。


### 独立査読の受理範囲

`/root/astra_semantics_review` は frozen r2 の全出力 hash と契約を照合し、条件付き合成として受理した。BLOCKING/MAJOR 指摘なし。二つの step case、同じ result index、current world、同じ K の各使用に別々に必要な availability/admissibility、全頂点を filter する birth path、同じ source scope/witness と typable-input principal guard を確認した。レビュー担当は著者ではなく、checker は再実行していない。Lean の実行結果は primary の実 receipt である。受理後の本 README の変更はこの status/receipt のみ。

固定版・producer r1・primary r2・最終 hash、未具体化の義務は [sprint outcome](../../../tasks/agent-loop/sprints/lean-root-20261024-outcome.md) に記録する。


## 七 frame の全有限 trace への接続

LEAN-CONTROL-20261024/r1。producer の raw/typing/capture/response/failure 草稿を実際の STOP 後に primary が共同構成した。最初のチェックで予約語 `instance` と相互帰納型の単独 induction が拒否されたため、field を `instanceId` にし、有限 frame list の帰納へ修正した。値 pending と operation 候補列を分離し、value 候補列も明示的検索へ展開した。`ControlStep` 全規則の型保存、進行、admissible response formation と all-finite-trace 定理を補った。

`localLaws` の安全性四 field はこの証明から生成する。効果解析の seed/step/resume/observation は `AnalysisLaws`、初期型形成と registered body の保存・進行はそれぞれ別入力として残る。未解決の元 A/B、source/native、SCC の実構成を今回の制御抽象へ置き換えない。

Lean 4.35.0 による module 検査、`lake build`、`lake env lean -j1 -M1024 YulangClosure.lean` は exit 0。`control_preservation` は公理依存なし。`progress` と `prefix_fail_absorbing` は Lean 標準の `propext`、`resume_reusable`・`finite_trace_safety`・`finite_prefix_control` は標準の `propext, Classical.choice, Quot.sound` に依存する。project 独自の axiom や未証明穴はないが、これらを「公理依存なし」とは記さない。具体的な audit と独立査読の固定版は [control outcome](../../../tasks/agent-loop/sprints/lean-control-20261024-outcome.md) に記す。独立査読は、この制御抽象の範囲で受理した。BLOCKING/MAJOR 指摘なし。全元値・body・metadata・観測・source 初期形成が未具体化である境界も確認した。コンパイラ実装・tests/probes は実行していない。


## 元構文・代入と具体的な式本体

LEAN-CORE-20261024/r1。[元構文との対応稿](../2026-10-24-lean-core-correspondence.md)は、全 raw vocabulary と、型付き規則のある範囲を区別する。`substituteRaw_composition` は全 Raw/Forest と四種類の binder に対する代入合成を証明する。raw constructor の正しい arity/sort、全元言語の型規則と型付き代入までは証明しない。

`substComp_typed`、`single_raw`、`raw_step_lifts`、`raw_finite_safety` は、unit/variable/delay + Ret/Force/let の実構文を扱う。空文脈を持つ型付けから、代入による principal step と bind frame の実生成を証明した。raw 側には不正 Force→Bad の規則もあり、逆方向の step 対応がそれを型付き image から排除する。型付き step だけを検査して全 raw execution を推測してはいない。

既存 Control の body dispatch は unchanged-stack のままであり、全元値と syntax-bearing frame を接続する bridge は未完である。今回の小範囲の safety を full V1/BodyLaws や全言語の定理へ読み替えない。次の義務は同じ raw vocabulary の全 constructor typing、full body/principal semantics と control 接続である。独立査読は raw 代入代数と明記した型付き範囲を受理した。全言語への昇格はしていない。検査・固定版は [core outcome](../../../tasks/agent-loop/sprints/lean-core-20261024-outcome.md) に記録する。


## 同じ型安全性定理の構造型への拡張

LEAN-STRUCTURAL-20261024/r1。union injection/case、同じ値への二つの導出を持つ intersection/choose、Top、Bottom elimination を、既存の `Original.raw_finite_safety` に組み込んだ。両 branch の型付き代入、raw embedding、canonical forms、principal 保存、進行、**拡張した RawStep の全 successor** の逆方向対応を検査した。式本体の安全性を新しく仮定していない。

intersection の Prop 型証拠のみを計算表現で消去する `rawProofBoth` と、明示 evidence を保持する `rawBoth` は別である。任意の明示 evidence/runtime View/metadata の消去定理を主張しない。全元型の型付き代入、Control への接続、source/native/SCC の親義務は OPEN のままである。[対応と限界](../2026-10-24-lean-core-correspondence.md)、[検査・査読記録](../../../tasks/agent-loop/sprints/lean-structural-20261024-outcome.md)を参照。


## 抽象 Focus の有限完了

`ForceCompletion.lean` は r7 の抽象 administrative machine に対し、任意の `FocusResult` を、同じ trace と literal な順序付き wrapper を持つ `CountedRun` と同値にする。証明は pending stack の帰納と既存の `observe_run` / `run_backward` を使う。Lean 4.35.0 で検査済み、公理依存は `[propext, Quot.sound]`。独立査読は CLEAN。

これは抽象的な有限成功の zipper 補題であり、O-NORM に再利用できる局所結果である。元 Yulang の source encoding、beta/packet realization、Force/View applicability、O-RESULT、termination、raw error coverage、source/native correspondence は証明しない。O-NORM、O-RESULT、元の意味論・型推論の親義務は OPEN のまま。[r11 outcome](../../../tasks/agent-loop/sprints/force-completion-20261025-r11-outcome.md) に固定ハッシュ、checker receipt、独立査読と残る premise を記録する。

## Force normal-leave source frontier

`2026-10-25-force-local-applicability.md` gives a fresh-reviewed conditional graph theorem: under an explicit fresh finite-DAG leave interface, every route to the result factors through its complete typed frontier; an exact criterion characterizes the all-endpoint/all-finite-suffix route law by frontier soundness and coverage of both the actual body result and the operand's `force.result` subtree. The r10 two-row batch is sufficient, but its exact representation is not required by the criterion.

The pinned operational Force/Flow clauses establish a weaker shape: Force enters the `force.effect` View, carries a distinct result transport and result-path metadata, and each emitted Flow row has a fresh target and permitted finite template. They do not yet derive the actual `t,r,o` endpoint equation, universal suffix coverage or exhaustive frontier soundness. The result is a reviewed obstruction to source application, not an underdetermination theorem. No Lean module is enabled by this candidate. FL12-SOURCE-1 remains OPEN at the d/expose/Force/View normal-leave owner; the native correspondence and original parent remain OPEN. See the [r12.1 outcome](../../../tasks/agent-loop/sprints/force-local-applicability-20261025-r12-outcome.md) and its [source analysis](../../2026-10-25-force-local-applicability.md).

## Paper execution-type substitution algebra

`PaperTypeSubstitution.lean` adds a standalone de Bruijn execution-type syntax with simultaneous substitution, binder lifting under `mu`/`forall`, identity, renaming compatibility and substitution composition. Variadic tuples, records, variants and nominal arguments use explicit sequence constructors in the same inductive tree. `OperationInstance` carries and substitutes its type arguments, payload and response together. The Lean-checked laws are foundational algebra only: sequence formation, type judgments, declarations/environments/plans, and the embedding into existing `HigherOrder.Ty` remain OPEN. It does not prove source typing, executor preservation, native correspondence or any Simple-sub A/B obligation. The exact primary-only candidate and its limits are recorded in [the r1 sprint contract](../../../tasks/agent-loop/sprints/paper-type-substitution-20261025-r1.md).
