# エフェクト・ハンドラ実装：次の実行計画

- 日付: 2026-10-15
- 対象: `research/simple-sub-intrusion`
- 実装基準: `343754251a1e6af057eb0b45be660cb882ea8391`
- 位置付け: 既存の承認事項を実行するための引き継ぎ。新しい言語仕様・実装権限の承認ではない。
- 今回の到達点: 現在の carrier で、保護すべき寄与を残すハンドラ残余を playground から観測できること。
- 現在の実装 checkpoint: `3683ed72d`。象徴的な source introduction の構築・観測だけを実装済み。live context と残余 consumer は未実装。

## 1. 再開時はここから

1. branch、HEAD、差分、`questions/` の未統合回答を確認する。下記の段階表を更新し、完了済みの段階を再開しない。
2. [現在地](../notes/progress/2026-10-14-operation-catch-constraints.md)と
   [実装上の欠落箇所 §6](../notes/theory/2026-10-14-handler-boundary-construction.md#6-concrete-next-owner-handoff-no-third-unchanged-conditional-proof)を読む。
   判断に使う規則・Authoritative な節は各担当へ渡す。古い研究キューの全項目を開始条件にしない。
3. **現在の H1 は source profile incidence の実証待ち。** H1-A/H1-B は凍結・commit 済みで、
   独立 `compiler_referee` が blocking / major なしと判定した。H1 自体は OPEN。
   追加の bounded derivation は
   [`callback profile reconstruction/receipt`](../notes/theory/2026-10-15-callback-profile-reconstruction-receipt.md)
   に凍結され、fresh `compiler_referee` review でも bounded obstruction として採用可能、
   blocking / major なしとなった。minor は、relation のない captured bound にも
   `TransportWitness` が作られるように読めた箇所を条件付きの記述に直し、delta review で閉じた。
   結果は、実際に dispatch された Function 比較が正確な Argument child と FunctionPort
   parent/field incidence を作り、captured Function endpoint も一部の transport provenance
   に残すこと。一方、未注釈 formal の source profile 導入と、同じ profile/view incidence
   をその Argument 対応へ結び付ける判断はまだ native に存在しない。dynamic Receive/Observe、
   earlier extrusion lineage、alias/return の完全な保存も別の OPEN premise。
   当時の source-profile 実装試行は、適用位置表を未確認として差分なしで終了した。
   その後、[directional protection addendum](../notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md)
   §§1–4 の既存決定を architect が照合し、protected omitted formal `f` の元の上位需要
   `f <: A [Ein] -> [Eout] B` では、その上位 occurrence の `Eout` だけを新規保護すると確定した。
   `Ein`、`B` 内、provider/recursive lower への逆流は含めず、独立 inherited protection は保持する。
   全 nested-position matrix の再決定は不要。これは production cutover authority ではない。
   意味を使わない D-only source-incidence certificate は実装・focused verification・delta review
   を完了し、[checkpoint](../notes/progress/2026-10-15-omitted-formal-structural-incidence.md)
   に記録した。認証範囲は captured FreshUse から一つの source Name handoff を通る経路までで、
   earlier extrusion、profile / grant / Receive / Observe / residual evidence は含まない。
   H3/P は有効にしない。

   2026-10-15 の [extrusion / Function consumer frontier](../notes/theory/2026-10-15-omitted-formal-extrusion-consumer-frontier.md)
   は、同じ nested-callback fixture の raw5 が Apply 結果、raw8/raw9 が元の
   formal domain であることを source slot から特定した。`cb x` の要求は
   `V8 <: F-` なので、この段階は Function child を作らず extrusion と bound
   accumulation へ進む。Argument consumer は正負両方の Function endpoint が
   揃った比較でのみできる。この fixture の consumer 数 0 は、incidence の消失を
   示さない。独立 review の小さな raw/canonical endpoint 精度指摘は反映済み。
   同日実施した [receiving-call probe](../notes/progress/2026-10-15-omitted-formal-receiving-call-dispatch.md)
   は exact focused test を2回通過した。受信側 `outer identity` の Argument edge は
   元の `outer/cb` constructor と同じ FunctionPort parent に結び付いた。後続の `cb x`
   比較にも source Apply まで遡る Derived/Transport ancestry が残る一方、現在の
   incidence reader はその Argument child に formal incidence を返さず、extrusion
   Parent は pair key しか保持しない。minor review finding の wrong-parent attribution
   は `incidence.comparison == parent` の確認で閉じた。次は test-only に全
   RelationKey を走査し、Parent の exact pair/source と RelationId が一意かを照合する。
   一致が一意でなければ止まり、copy-time RelationId 観測を自動追加せず、必要な観測点を
   狭く提案する。
   source evidence のみで、profile matrix と H1/H2/U の状態は変えず、H3/P も有効にしない。

   続く [exact pair/source census](../notes/progress/2026-10-15-omitted-formal-copy-relation-uniqueness.md)
   は focused test と fresh M1 review を通過した。同一 State の全 RelationKey を走査し、
   4つの Parent がそれぞれ singleton として `cb x` の checking-origin relation に一致した。
   その source relation から後続の FunctionPort Argument consumer へは immediate Replay
   upper input と明示的な Transport/Derived ancestry が残る。別の [conditional owner bridge](../notes/theory/2026-10-15-extrusion-parent-source-correspondence.md)
   は、対象の structured Value-drain route で Parent の pair と sources が同じ active
   contextual relation から読むことを条件付きで示し、rollback caller を含む review を通過した。
   これは source relation から copy initiation と consumer ancestry への二つの経路で、
   個々の copied row の Function field path は残らない。局所の上位 `ResultEffect` を保護する law は
   すでに選択済みで、source/consumer correspondence が未完了。H1/H2/U は OPEN、H3/P は無効のまま。
   続く [raw Function field observation](../notes/progress/2026-10-15-omitted-formal-copy-field-correspondence.md)
   は exact focused test を2回通過した。4つの Parent は initiating source `RelationId(5)` に
   対応した一方、後続 `cb x` consumer の upper ancestry は `66 --FreshUse--> 13 --Derived--> 5`
   で、そこに qualifying Extrusion Function `TransportWitness` は0件だった。そのため field
   candidate set と exact consumer-input flag は観測されていない。source 上の静的 frontier は
   `Work::Function` の child/output と個別 Parent の結び付き、または `Work::Bound` の selected
   descendant との区別に残るが、この実行はそれが consumer path の最初の切れ目とは示していない。
   1件の minor な報告表現を直し、focused test を再実行した。source-side protection producer はまだ
   実装されず、H1/H2/U は OPEN、H3/P は無効。

   root Function の rewrite/extrusion、relation admission、captured-bound restoration、後続 FreshUse
   を追う [bounded lineage audit](../notes/theory/2026-10-15-root-function-extrusion-bound-lineage-audit.md)
   は fresh M1 review を通過した。続く
   [root output / consumer observation](../notes/progress/2026-10-15-root-function-copy-to-consumer-field-observation.md)
   は exact focused test と fresh M1 review を通過した。source `RelationId(5)` と実際の
   `FreshUse.from = NegativeFunction(term 269)` で既存 `by_output` を引くと、全4件の census
   Parent を含む singleton PairGroup が得られた。4つの raw Parent field は、元の negative
   Function、root output、FreshUse 後の Function の Argument / ArgumentEffect /
   ResultEffect / Result に一意に対応し、後続 Replay upper input `RelationId(66)` まで追えた。
   これは一つの fixture における具体的な field 対応で、`RelationId(13)` の一意な
   enqueue activation、全経路の transport、保護 profile は証明しない。

   独立した [Function field construction identity](../notes/theory/2026-10-15-extrusion-function-field-identity.md)
   は fresh compiler-referee review で blocking / major / minor なし。これは成功した一回の
   extrusion における4 field の同時構成式と、直接コピーされた row の raw ordinal 対応を
   明示した仮定の下で示す。canonicalized key、未変更 raw alias、selected-bound descendant、
   error rollback、全 caller は別責務に残る。

   architect は、
   [directional protection addendum](../notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md)
   に scoped law がすでに選択済みだと確認した。protected omitted formal `f` の元の上位需要
   `f <: A [Ein] -> [Eout] B` は、その upper occurrence の `Eout` だけを新規保護する。`Ein`、
   `B` 内の位置、既存 provider/recursive lower Function への逆流は含まず、独立な inherited protection
   は保持する。全 nested-position matrix の再投票は不要。この意味選択は production cutover authority
   を代替しない。

   M2 source-to-construction correspondence は
   [frozen note](../notes/theory/2026-10-15-directional-protection-source-correspondence.md)
   と [falsifier](../notes/progress/2026-10-15-directional-protection-source-falsifier.md)
   にまとまり、fresh `compiler_referee` と `spec_auditor` は blocking / major / minor なしと判定した。
   actual omission/scope と元の Apply upper demand の fresh `ResultEffect` は各 owner に残るが、
   protected-at-exposure の記号的な source record は private candidate/playground に実装した。
   詳細は [checkpoint](../notes/progress/2026-10-15-directional-introduction-playground.md)。
   元の checking occurrence、全 demand、`ResultEffect` と raw invocation row を結び、provider
   と別 use の負例を focused test で確認した。conformance review は問題なし。semantic review
   が見つけた per-call full binding scan は source registration に scope を保持する修正で除去し、
   focused delta review で binding 数に依存しない scope validation を確認した。
   ただしこの record は executable protection / live context consumer ではなく、H1 を閉じない。
   **次は source record から contextual protection consumer までの構築則と、既存 hygiene proof
   の premises を実コードへ対応づける bounded proof/source gate。** consumer または保護 profile の
   根拠が不足する場合、residual activation は止めて正確な不足点を保持する。late seed、
   capture/freshening、all-path transport は別 gate。`RelationId(13)` の enqueue activation
   も独立した source-provenance 課題のまま。H1/H2/U OPEN、H3/P disabled。

Luna は primary として、担当の分割、結果の採否、次の実行、Git 統合を持つ。
難しい証明は `prover`、承認済み構築は `implementer`、独立した反例・到達性確認は
`researcher`、査読は `compiler_referee` / `spec_auditor` に渡す。
設定の参照先は `.codex/`。この計画はモデル設定を変更しない。

## 2. 固定した現在地

| 完了・確定した事項 | 今後の扱い |
| --- | --- |
| 全分岐の制約生成、Value の出自を保持した extrusion/intrusion、playground | `if true` の事前評価や定数畳み込みへ戻らない。限定された実装・証明の範囲は維持する。 |
| 操作パターンの parser、payload と raw k の単相型制約 | parser/HIR を最初から調査し直さない。既存の `candidate_operation_catch` 12 件を回帰の基準にする。 |
| raw k の応答型 B、元の値 V、entry E / return R | `E <= R`、`S <= R` を保つ。S は保守的な上界であり、実際の suffix と等しいとは主張しない。 |
| native 残余 primitive P | [既存の証明](../notes/theory/2026-10-14-native-handler-residual-cut.md)を使う。新しい watcher や別の解法を作らない。 |
| 衛生性の既存定理 | [統合表 §3](../notes/design/2026-10-10-annotation-effect-hygiene-integration.md#3-existing-results-retained-and-reused)の仮定を実装で供給する。定理を最初から証明し直さない。 |
| 回答済み question | [receipt](../questions/2026-10-13-negative-formal-permission-field-law/receipt.md)を尊重する。回答は例の訂正であり、完全な負位置の field map の選択ではない。 |

**未完了の中心は U**：元の一つの scoped assignment の下で、処理対象の寄与だけが
残余除去へ入り、同じ effect family の保護された寄与、未処理の操作、外側の arm と
raw resumption の寄与が残ること。将来追加される制約と独立した残余の出自も含む。
空の context word、同じ family、型検査の成功だけでは U の根拠にならない。
注釈を省略した callback にも保護が必要である。

## 3. 当面の順序

日数ではなく、以下の実装単位ごとに確認して保存する。各段階の完了は言語全体や
production cutover の完了を意味しない。元の U の主張範囲を狭めて閉じない。

| 段階 | 状態・着手条件 | 実施内容と成果物 | 完了判定 |
| --- | --- | --- | --- |
| **H1: source 境界から live context まで** | OPEN。H1-A/B、bounded reconstruction/Argument correspondence、M2 source join は reviewed。D-only incidence certificate と directional symbolic introduction は限定経路のみ。後者は exact omission/scope/checking/demand/`ResultEffect` を保持するが、live protection context を生成しない。 | 次に occurrence-qualified record から既存 contextual carrier / consumer へ届く構築則を導き、既存 hygiene proof の仮定を source owners へ対応づける。 | record の存在と executable protection を区別する。単一 assignment、正確な位置・lifetime、provider no-backflow と inherited evidence を保つ。late demand、capture/freshening、alias/return、全経路、dynamic Receive/Observe、full Call は別 gate。 |
| **H2: 後から来る制約とコピーへの保存** | H1 の構築と意味が固定されてから、その差分に着手。 | replay、extrusion、capture/freshening、Value-SCC intrusion へ H1 の context を接続する。既存の経路を拡張し、別の配送機構を足さない。 | 後着 lower/upper にも検査が届く。同じ use 内の共有と別 use の独立性を保ち、row の等化で権限や recipe の出自が混ざらない。H1/H2 の証明と source 対応が成立する。 |
| **H3: Catch の残余に接続** | H1/H2 の必要な仮定が実装で成立し、選択・coverage の根拠を確認できた後。 | resolved operation ID と実際の arm coverage を用い、適格な入力に P を適用する。保護された経路は除去を通さず、arm・応答計算・raw k は外側へ流す。 | 直接処理した寄与は消え、未処理操作と保護された同 family の寄与は残る。現在・将来の gamma feedback が働く。playground で成功例と拒否例を観測し、U のうち実装した範囲と未対応の source を明示する。 |
| **H4: 使い方を広げた回帰と衛生性の適用** | H3 の最小例が動いた後。 | nested Catch、local alias、返された callback、複数 use、同 family の再送出、raw suffix の後続操作を source から確認する。既存の衛生性定理の各仮定を code owner に対応させる。 | source から compiler consumer までの対応に穴がない。対応済み範囲の衛生性の結論を適用し、未解決の complete Call / lifecycle 前提を残したまま全体を閉じない。 |

H1 の証明に実装上の証拠が必要な場合、許されるのはその証拠を作る最小の可逆な
計測・構築差分である。反証条件を先に固定し、dependent な通常経路への切替は OPEN
のままにする。「実装がないので証明不能、証明がないので一行も実装不能」という循環を作らない。
逆に、その試作が動いたことだけで H1/H2 の未証明な前提を成立扱いしない。

## 4. 最初に渡すパケット

共通入力は基準 commit、上記の境界記録、
[top-level principles §1.1](../notes/design/2026-10-11-yulang-inference-top-level-principles.md)、
[annotation policy §§1,3–5](../notes/design/2026-10-10-annotation-effect-hygiene-integration.md)、
[context contract §§2–4](../notes/design/2026-10-10-contextual-attachment-admission-design.md)、
[charter §§13–20,24](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)。
各 child は `fork_turns: "none"`、独占する出力パス、安定した読み取り基準、予算を明示して起動する。
H1-A/B/C は完了済み artifact または bounded implementation slice の記録。
H1-D の成果物 path は候補であり、primary が最新差分を確認してから lease を発行する。

### H1-A — 構築則と実コードへの対応（既存 packet 完了）

- 担当: `prover`。最初の区切りは 20 分。元の U は OPEN のまま。
- 前提: charter §24 の receiver role を先に保つ。通常の無注釈 function literal は pure、
  明示的に Function 注釈を持つ literal と callback 位置の literal はそれぞれ選択された
  handler role に従う。すべての invocation を handler 境界とは見なさず、effect port の
  綴りから role を逆算しない。Value / Computation の引数 entry との区別も維持する。
- 問い: `my relay cb = catch cb() { v -> v }` の formal row に対し、選択された role と
  型上の位置で必要になる保護を receiver entry の前に導入し、後続の Function demand
  によって判明する位置へ普通の制約伝播で運べるか。
  型全体の確定を先に要求しない。未知型・alias・返却経路を除外しない。
- 出力候補: `notes/theory/2026-10-14-callback-profile-native-construction.md` 一つ。
  最小の構築則、実際の constructor/consumer、既存定理へ渡す仮定を記す。
  producer が存在すると仮定しただけの条件付き補題を成果にしない。
- 反証条件: 元の保護の消失、別位置への権限の生成、後着 Function bound の取りこぼし。
- 止まる条件: 具体的な構築則が成立しない箇所、または未決定の意味が一つ特定できた時。
  同じ仮定の言い換えを継続せず、その箇所を primary と実装担当へ返す。

### H1-B — 独立した source の反例候補（既存 packet 完了）

- 担当: `researcher`。H1-A と並行、最初の区切りは 15 分。
- 対象: 省略 callback、alias / capture / return、同 family の二操作のうち一操作だけを持つ Catch。
  既存の [boundary note §3](../notes/theory/2026-10-14-handler-boundary-construction.md) の
  relay は source-qualified な候補であり、実行済み・誤除去の反例とは扱わない。
- 出力候補: `notes/progress/2026-10-14-callback-profile-source-falsifier.md` 一つ。
  source、到達した constructor、比較すべき寄与、観測結果／未観測を区別して残す。
- コンパイラの実観測が必要なら、最小の観測箇所を primary に返す。独自の仮想 solver を作らない。
  最初の有効な反例、または判別できる最小組が揃ったら止める。

### H1-C — source introduction certificate（限定 slice 完了）

- 担当: `implementer`。H1-A/B から必要な source 証拠と構築則を受け、primary が対象を限定する。
- source 側: `crates/yu-solver/src/candidate_source.rs` の formal/lambda 形成、
  `candidate_effect.rs::{candidate_formal_pair,candidate_signature_view}`、`lib.rs::admit_lambda_fact`。
- consumer 側: `candidate_context.rs::{candidate_context_seed,candidate_function_port_admit,candidate_context_execute_relation}`。
  必要な HIR/annotation/lifecycle ファイルは個別に lease を追加する。
- inferred Function capture/freshening/reconstruction: `candidate_scheme.rs`; retain the source
  formal/profile incidence and its typed-position map through per-use remapping. This owner is
  required by the H1-A/B result and is not an equality-keyed global lookup.
- 同じファイルの source / consumer を別の writer に同時に渡さない。
  proof・反例担当は凍結した commit を読む。新しい差分を使う時点で明示的に再凍結する。
- H3 の追加テスト候補: `crates/yu-solver/tests/candidate_handler_hygiene.rs`。
  既存 fixture の期待値を現出力に合わせて変更しない。

### H1-D — live contextual consumer と hygiene bridge（bounded characterization complete）

- 基準: `2b95123d644990352ca0a0e4c28c58680c9ffed3`。`prover` と独立 `researcher` の static-only 成果は `notes/theory/2026-10-15-directional-introduction-context-consumer.md` と `notes/progress/2026-10-15-directional-introduction-context-falsifier.md`。fresh `compiler_referee` が blocking/major なしとし、二つの locator 修正を delta review で閉じた。
- 結果: original Apply の Value pair は記録済み `DirectionalIntroduction` があっても `IDENTITY` context を受け、現行 live consumer はその記録を読まない。既存 one-color lemma の active guard 等も未供給。source の誤除去反例・不可能性定理は得ていない。
- 親 H1/H2/U は OPEN、H3/P disabled。late demand、全 source の coverage、lifecycle transport、production gate は別の未解決事項。

### H1-E — source-owned protection schema / context prototype（receiver-entry bridge characterized）

- 根拠: H1-D の exact missing edge と、architect による local semantic authority adjudication。省略 formal の source identity/scope と authenticated original Apply をつなぎ、その upper Function の正確な `ResultEffect` にだけ protection を加える。既存 lower/provider の独立 protection を保存し、backflow を追加しない。この局所法則について追加の user decision は残っていない。
- 目的: 最小の private candidate/playground prototype で、同じ scoped assignment 内の actual live context constructor/consumer を実行し、omitted formal / known provider / separate Apply use の区別を観測する。まず既存の `ContextExpr`、`candidate_context_seed`、`candidate_function_port_admit`、Function dispatch の所有関係を使い、対象 source occurrence と ResultEffect child の対応を保持する。SCC/equality/canonical row だけから権限を導かない。
- 初回 owner inspection は code 変更なしで停止した。existing `LocalWeight` は zero-word Allowance filter、`InferredEntryOriginId` は inert で `EntryCertificateId` と別物、ResultEffect child は既存 context を preserve するだけ。architect は static `(Lambda, formal/root, omission scope, Apply, ResultEffect)` が directional source introduction を識別する一方、activation-sensitive receiver identity と同一視できないと確認した。これは representation/source-correspondence gap で、local law の再投票ではない。
- 二回の bounded implementer inspection は code 変更なしで停止した。現行 `candidate_context_execute_relation` は closed-Allowance membership/bound の consumer だけを持ち、source-owned schema を ContextExpr に格納するだけでは execution でなく metadata になる。`notes/theory/2026-10-15-directional-introduction-live-context-constructor-proof.md` は Function4 field routing と relation-before-enqueue を構成的に示す bounded prefix として、fresh `compiler_referee` の指摘なしで査読済み。この first operational constructor は未供給のまま。
- H1-E の receiver-entry owner map と paired proof/falsifier は完了。`yu-core::shadow_typed_evidence::query_conditionally` に conditional activation classifier があるが、typed-path/Observe/Receive/active-owner roots は caller assumptions で、production caller がない。HIR Lambda/admission は invocation-entry/expiry identity を作らない。reviewed pair は、source constructors が static Lambda/formal/Apply/Function fields を保持する一方、actual receiving occurrence・immutable boundary receiver・matching receipt/observation・normal-return expiry を生成しないと示す。fresh `compiler_referee` は blocking/major なし。§4 locator と approval-gate wording の minor 修正を閉じた。source 上の alpha/beta composition は未実行で、誤動作反例でも不可能性証明でもない。
- 可逆性: H1 の証拠用 candidate slice に限定し、production cutover、Catch residual `P`、Receive/Observe、動的 receipt、Handler role の新規認定を含めない。実際の receiver-entry/lifetime owner、late/capture/return transport、failure atomicity は unresolved のまま。retroactive replay/additional profile positions が必要なら実装を拡張せず止める。
- H1-F は H1-E の code prototype ではなく、source-directed symbolic entry derivation と独立 falsifier。architect は、user-selected typed transport/lifetime principles 内に observable-behavior choice を特定せず、具体的な `Owner/Bind/View` machinery は未承認 Draft と区別した。source `C_in` / Lambda / formal/profile template と各 executing receiver occurrence を別にし、source Call/typed-value operations から immutable boundary、actual received/captured/returned typed paths、matching Receive/Observe/current roots、exact normal-return expiry/re-entry を導けるか調べる。

### H1-F — source-directed symbolic receiver entry derivation（reviewed bounded slice complete）

- 狙い: `relay cb = catch cb() { v -> v }` の source trace と、同一の receiving source Call を alpha が実行して return、後で beta が再実行する discriminator について、source producer → native consumer の対応を導く。alpha の historical profile は alpha を指したまま、beta の live state がそれを再活性化しないことを示す。runtime 実行を constraint generation の前提にはしない。
- 必須 case: original single `sigma`; original formal/profile template と dynamic receiver occurrence の分離; actual argument/capture/result typed paths と matching Receive/Observe; normal return; shallow raw resumption では still-live owner の identity/activity preservation、expired-then-fresh-entry、historical boundary non-rebinding を分ける。borrowed enter/leave は Draft realization candidate と明記する。candidate program の admission/typing/evaluation は根拠がない限り未証明と表示する。
- Result: the pair derives the static original-formal/Apply/ResultEffect/Catch-binder/Function4-Argument prefix and stops before an executing receiver, immutable boundary, typed receipt/observation and exact expiry. Source Call admission, execution, alpha/beta trace and raw native re-entry remain unproved. The selected live-owner identity/activity and current-state requirements are distinct from the unapproved Draft borrowed enter/leave realization.
- Leases closed: `prover` → `notes/theory/2026-10-15-receiver-entry-source-derived-map.md`; independent `researcher` → `notes/progress/2026-10-15-receiver-entry-derived-map-falsifier.md`; baseline `28fd565e7144373ce5cd19d5e8fa6cff673087cf`. The proof note’s 33 pins and falsifier’s 26 pins matched; five Call/source-frame dependencies added during correction were checked separately against the baseline. Both were static-only; Cargo/tests/builds/probes/measurements were 0.
- Review: a `compiler_referee` and `spec_auditor` reviewed the frozen pair. Both identified the same Draft-overstatement boundary; the primary repaired the two rows and the `spec_auditor` confirmed closure. The selected source Call semantics already exists; only its HIR/Gen-Call-0 to native typed evidence/current-root/expiry correspondence remains open. No parent promotion.
- Verification: H1-F changed no code and ran no Cargo/build/test/probe/measurement. `git diff --check` plus focused whitespace/hash checks cover only this record/artifact update. The next code lease, if eventually justified, needs owning focused tests and solver check plus M2 review.
### H1-G — original Call to native receiver correspondence（bounded characterization complete）

- Baseline: `b336999a148eaee7779f80e0a18e9e79e2cd8394`, after H1-F review repair and record sync.
- The `prover` and `researcher` artifacts are frozen at `notes/theory/2026-10-15-call-native-correspondence-construction.md` and `notes/progress/2026-10-15-call-native-correspondence-falsifier.md`; the read-only `explorer` owner map and `architect` route adjudication are returned. Fresh M2 `compiler_referee` and `spec_auditor` reviews found no findings in the paired correspondence artifacts.
- Question: derive or falsify the map from authoritative `OC-CallEff`/`J_call`/`FrameCall`/`C-Inv`/`CallMem` through actual HIR and Gen-Call-0 source construction into native Function4 and typed-evidence consumers under one original assignment. Keep C_in and C_cb distinct; cover actual-provider/result/future/suffix inputs and receiver/profile/event/current-root/expiry fields. Stop at the first missing field, constructor or interface.
- Exclusions: no new Call semantics; no Draft borrowed/owned rule as a premise; no assumption of source admission, full typing, execution, complete native Gen-Call-0, typed receipt, Receive/Observe, or exact expiry; no endpoint reconstruction, new profile positions, new carrier, production code, or parent closure. Preserve original shallow-Catch domain and H1/H2/U OPEN; H3/P disabled.
- Result: selected Call semantics is already settled; actual Apply/native Function4 fields do not construct authentic complete `Gen-Call-0`/`FrameCall`/`Q_e`. The first missing owner is complete interface elaboration at source registration/operators, before receiver activation. This is a source/native correspondence gap, not a source impossibility or execution counterexample. H1-G closes only this static locator and review; H1/H2/U remain OPEN and H3/P disabled.
- Verification: static dependency/locator/hash checks and `git diff --check`; zero Cargo/tests/builds/probes/measurements. No production representation or implementation authority follows.

### H1-H — bounded source-interface graph construction proposal（reviewed; first absent telescope now targeted）

- Baseline: `cb216f7e8e60b3839ac6756308acd021bbd146c8`.
- Packet: `notes/theory/2026-10-15-source-call-interface-native-construction-packet.md`. It narrows the previously reviewed finite dependent Call-graph proposal to source registration/operator elaboration through one Apply record and maps every original `Idx(e)` group to existing or missing source/native owners.
- Proposed invariants: allocate source type variables and constraints before solving; retain a whole dependent contract graph with an open whole-carrier slot; map all native Function4 fields jointly; apply one scoped `sigma` to nodes and edges; keep C_in and C_cb separate. It claims no complete C0, admission, execution receiver, Receive/Observe, expiry, H1/H2/U, production route, or cutover.
- Review: fresh M2 `compiler_referee` (dependent structure and source correspondence) and `spec_auditor` (exact authority and approval boundary) found no blocking, major or minor findings. Static text/source review only; no Cargo/tests/builds/probes/measurements. The packet is non-authoritative and grants no implementation authority.
- Authorization: the user's existing explicit playground instruction covers reversible private evidence work; durable graph adoption and production routing remain gated. The first proposed graph shell would duplicate `PendingCallConstruction` because it cannot yet construct the authentic formal telescope. No code was started.
- Selector adjudication: at baseline `e53493916`, registered `next_action_selector` (configuration requests `gpt-6.1-sol` / medium; runtime-observed model and effort were not exposed) found the first missing producer is the authentic declared dependent interface `T_f` and inferred-contract reference `R_f` at formal registration. The next action must construct or precisely obstruct these at their source owner before IF-Use/Apply consumes them. This changes the method from gap inventory to the actual missing constructor; a conditional receiver proof or larger probe cannot supply it.

### H1-I — formal-registration interface construction（construction artifact reviewed; falsifier unreviewed）

- Baseline: `e5349391660adf7485b7b7757aae2b433f8b1423`; artifacts `notes/theory/2026-10-15-formal-registration-interface-construction.md` and `notes/progress/2026-10-15-formal-registration-interface-falsifier.md`. The `prover` constructed the actual positive prefix: source formal/scope, one recipe and shared symbolic native Value row, distinct lexical Name routes, and retained Apply provenance.
- Result: both methods stop before the original typed registration `reg_f : R_f with declared complete T_f`. The first missing formation input is the generic symbolic Value-interface family at the formal's original dependent context and its lawful native-row interpretation. IF-Use instantiates a registered interface; neither a new node identity, native Value row, later Function4 demand, nor current ValueBind/descriptor constructors supply that formation. This obstructs the attempted forward construction only; it is not a source-impossibility theorem or an H1/H2/U closure.
- Review: primary validated all 30 dependency hashes; 29 match both current files and e534. The H1-H packet matches current HEAD and differs from e534 only by the committed approval/next-gate update. One fresh M2 `compiler_referee` found no blocking, major or minor findings. Static only; zero Rust edits, builds/tests/probes/measurements or Git operations by workers. Effective prover/reviewer runtime model and effort were not exposed.
- Authority result: existing source-interface and inference authority do not derive the generic family from the unannotated formal, source scope and native Value row. The exact independent input is a descriptor-interface basis with its original binders/dependent fields/references and lawful source/native interpretation under one `sigma`. This is not an impossibility result and does not alone force a user decision; a decision is needed only if a proposed formation rule selects new observable meaning or durable representation.
- Review: primary validated all 30 dependency hashes; 29 match both current files and e534. The H1-H packet matches current HEAD and differs from e534 only by the committed approval/next-gate update. Fresh M2 `compiler_referee` found no blocking, major or minor findings on the construction artifact only. The paired falsifier remains unreviewed. The construction header and commit packet now record that exact scope; its argument and dependencies are unchanged.
- Authority result: existing source-interface and inference authority do not derive the generic family from the unannotated formal, source scope and native Value row. The exact independent input is a descriptor-interface basis with its original binders/dependent fields/references and lawful source/native interpretation under one `sigma`. This is not an impossibility result and does not alone force a user decision; a decision is needed only if a proposed formation rule selects new observable meaning or durable representation.
- H1-I closes only as a bounded construction obstruction. No source impossibility or parent theorem follows.

### H1-J — symbolic Value-interface basis candidate（reviewed bounded derivation/obstruction）

- Baseline: `e3a91db04f9d63028434a74bdc971236133536cc`. Exclusive outputs: prover `notes/theory/2026-10-15-symbolic-value-interface-basis-construction.md`; independent researcher `notes/progress/2026-10-15-symbolic-value-interface-basis-falsifier.md`.
- Claim: construct the original descriptor-interface basis, complete dependent telescope `T_f`, registration `R_f`, semantic field/evidence/reference owners and lawful joint action from an unannotated source formal before IF-Use, preserving ordinary unsolved variables and all original alternatives; or isolate the exact independent input/new observable choice.
- Result: same-`sigma` specialization is derived only conditionally. The first missing premise remains the original local Value-descriptor domain, its dependent field interpretation and lawful scoped action at ParameterOrigin, with correspondence to the shared native row. The researcher found no source-qualified counterexample; same-shape/different-contract cases refute shape-only reconstruction but permit a family retaining both providers. This is a bounded derivation/obstruction, not a theorem, impossibility result, semantic decision or production premise.
- Review/checks: primary validated 49 H1-J dependency hashes; 48 repository dependencies match current and e3a, with one external skill file matching current but unavailable for Git-baseline comparison. Both frozen artifact hashes were validated before review. Fresh M2 `compiler_referee` and `spec_auditor` found no blocking, major or minor findings on the pair. Static only; zero tests/builds/probes/measurements. No new code or production route. Parent H1/H2/U remain OPEN; H3/P disabled.

### H1-K — original Value-descriptor kernel audit（reviewed bounded obstruction）

- Baseline: `8d629a54bbf1d9c279699406e4ba55674d15cb63` plus the frozen H1-I/H1-J artifacts and current selected sources. Read-only `architect`, at most 20 minutes; no write lease, child delegation, tests, builds, probes or measurements.
- Start from original descriptor-kernel introduction/elimination clauses and their independently licensed contracts. Work forward through callable/noncallable alternatives, actual-provider decomposition, challenge/observation fields, output-dependent futures and lawful joint substitution at ParameterOrigin. Do not start from the native row or another generic element.
- Result: the direct callable constructor takes an independently interpreted whole-carrier entry interface `I` at `ParameterOrigin`. Native parameter/Function construction retains source identity, a shared row and polarized handles but not `I`, complete admission/observation meaning or its lawful scoped action. The first concrete fields needing independent interpretation are initial/pre-receipt and pending observations, including typed paths, request/response/raw-handle correspondence and current-world/phase guards. No impossibility or semantic decision follows. The exact two-closure simultaneous constructor is a selected local interpretation; this audit does not extend it to arbitrary formal registration.
- Review/evidence: read-only architect report `notes/theory/2026-10-15-original-value-descriptor-kernel-audit.md`; fresh M2 `compiler_referee` found no blocking, major or minor findings. Primary verified named native source files unchanged from `8d629a54b` through review baseline `0bab425f8`. Zero tests/builds/probes/measurements or code edits. H1/H2/U OPEN; H3/P disabled.

### H1-L — original Entry-Value interface to native parameter bridge（reviewed bounded obstruction）

- Frozen pair: `notes/theory/2026-10-15-entry-interface-native-bridge-construction.md` and `notes/progress/2026-10-15-entry-interface-native-bridge-falsifier.md`, baseline `8e7f249cf94c06fb15c3e8da94d41f57c3f8ed65`; both are committed and pushed.
- Result: actual formal registration/shared Value row, Lambda entry-effect accumulation, and Apply argument/value-effect endpoints form a positive native prefix. Both methods stop at the original Entry-Value designated entry's initial/pre-receipt interpretation and lawful dependent action at `ParameterOrigin`, including current-world/phase guards. The selected two-closure constructor assumes independently interpreted `I_x/I_y`; it does not bridge arbitrary formal registration to the native pair. This is a bounded source/native obstruction, not source impossibility, a runtime failure, or a parent theorem.
- Review: fresh M2 `compiler_referee` reviewed the pair with no findings. Parent H1/H2/U remain OPEN; H3/P disabled. Keep later pending/raw-handle obligations distinct and do not repeat another shape-only or equivalent initial-interface reconstruction.

### H2 current copied-Allowance activation — active evidence slice

- Reviewed input: `notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md`. Fresh M2 `compiler_referee` found no findings on its bounded structural derivation. Distinct view IDs, per-use `(old view, mapped tail)` sharing, capture incidence and qualifying intrusion replay are established for the named successful native routes. The current-pair activation bridge at `Work::IncomingAllowance` / `Work::Bound` remains OPEN; bound storage and origin transfer alone prove neither activation nor loss.
- At baseline `d8a6209c1`, the `prover` derivation at `notes/theory/2026-10-15-extrusion-current-cut-activation-construction.md` and independent `researcher` falsifier at `notes/progress/2026-10-15-extrusion-current-cut-activation-falsifier.md` froze as a bounded pair. A fresh M2 `compiler_referee` found no findings. Both preserve the original quantifiers, reject an already-forwarded atomic Contribution as a false witness, and leave current symbolic/context activation OPEN.
- The test-only observer is at `crates/yu-solver/src/candidate_context_tests.rs::observe_structural_value_extrusion_current_and_late_allowance_pairs`; the primary's runtime evidence is recorded in `notes/progress/2026-10-15-extrusion-current-cut-activation-observation.md`. It reaches extrusion through structural Value dispatch, admits distinct views with the same source/tail rows, records a copied symbolic lower without a current Replay dependency, and confirms a later direct lower replays to both copied cuts and the tail. It does not manually enqueue the replay under investigation. The exact focused test passed after one test-only compile repair; a fresh M2 `spec_auditor` found no findings.
- The static owner audit at `notes/progress/2026-10-15-copied-symbolic-cut-continuation-owner-audit.md` is reviewed by a fresh M2 `compiler_referee` with no findings. Completed original symbolic admission registers incoming incidence before the gamma snapshot; positive traversal reconstructs copied cuts on reused `x`, and later ordinary lower admission replays them through the typed drain. The genuinely remapped and pending case, including arbitrary ordered contexts, remains unsupported. No source counterexample or H2/U closure follows.
- The constructive application and independent falsifier at `notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md` and `notes/progress/2026-10-15-pending-symbolic-cut-continuation-falsifier.md` were reviewed together by a fresh M2 `compiler_referee` with no findings. The completed-scan/reused-row/plain-later-lower case is derived. The remapped trace is conditional on a pending original cut during copy and later direct use of x'; its source schedule and consumer remain unauthenticated. No source counterexample or H2/U closure follows.
- Next action: authenticate or refute that combined pending-order/direct-remapped-consumer premise at source Function dispatch and typed-drain owners, retaining all repair operations and source cases under one scoped assignment. No Cargo budget remains; H1/H2/U stay OPEN, H3/P disabled, production/F5 separate.

## 5. 判定に使う最小の確認

これは将来の実装時の実行候補であり、この計画作成時に実行したものではない。
primary 一人が Cargo を直列実行し、`CARGO_BUILD_JOBS=2 timeout 300s` と
`--test-threads=1` を使う。各段階では変更した owner の filter を先に選ぶ。

| 対象 | 既存の入口・filter | 証明していないこと |
| --- | --- | --- |
| source と raw k | `--test candidate_operation_catch`、HIR `--test catch_local_source`、playground `--test cli operation_catch_` | 現在の成功は残余除去を示さない。 |
| source PUSH | `--lib candidate_context::tests::source_unit_push_preparation_` | 現在は detached algebra の確認。live な保護の完成ではない。 |
| Function の文脈 | `--lib candidate_context::tests::function_port_context_` と `function_port_incidence_` | source callback profile の生成は別途必要。 |
| P と後着制約 | `--lib candidate_effect::tests::union_tail_preserves_flow_and_cached_effect_and_function_roots_replay_future_conflicts` | P の入力が source 上で適格かは別途必要。 |
| copy / intrusion | `--lib candidate_effect::tests::positive_extrusion_retains_mixed_allowance_before_capture_and_late_lower`、`raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion` | 既存の plain 経路の証拠を、新しい非零 context 全体の証明に拡張しない。 |

solver は `-p yu-solver --features shadow-f5,shadow-apply-candidate`、HIR は
`-p yu-hir --features shadow`、playground は `-p yu-playground` を指定する。
新しい source controls は direct / omitted callback / partial operation coverage /
same-family outside arm / raw suffix / alias の順で最小化し、未実行の予想を確定値にしない。
H3/H4 のまとまった境界で一度 `cargo check -q --workspace` を実行する。
記録だけの更新で再実行しない。性能測定は具体的なリスクが出た時に既存予算で行う。

## 6. この先の準備と、判断が必要な場合

**汎用操作の rigid opening** は独立した準備が可能。charter §§19–20 に従い、
`echo : 'a -> 'a` の一様な arm と、`sink::put` の局所型を Int に固定する禁止例を対にする。
payload・response・raw k・依存する返却値を同じ existential package として保つ構築を
`prover` に渡す。余力があり H1 の統合を妨げない時だけ並行する。現在の柔軟な変数生成で
generic arm を有効にしない。実装は独立査読した構築と必要な実装承認が揃ってから開始する。

**負位置の具体 annotation** の正確な field map が必要になった場合は、元の
annotation 位置、実装 field、異なる結果になる source を具体化する。既存の承認から
導ける対応は実装へ渡し、本当に残る意味の選択だけを質問する。回答済みの旧例を再掲して
同じ選択を求めない。止めるのはその対応に依存する作業だけとする。

guards・labels・tuple patterns、完全な Call、型推論全体の性質、backend/F5 切替は
この計画で完了扱いにしない。H3/H4 の証拠が揃った時点で、実際の未対応 source から
次の小さな実装順を決める。現時点で未知の順序や完了日を固定しない。

## 7. Luna の進行判定

- child の最初の区切りは報告点であり、元の gate の終了ではない。
  結果を受けたら、証明を適用する／具体的な未充足前提を owner に渡す／反例を採否判断する。
  ノートの追加件数で進捗を数えない。同じ前提が残ったら構築か調査方法を変える。
- 新しい core 構築の A/B 不変条件は大きな依存実装より先に証明・反証する。
  H1-C の最小試作だけは、その証拠を得る目的で限定して許可する。
- 通常の実装は M2 を起点に意味と仕様の二観点で査読する。新しい広範な不変条件や
  certification は M3 を選ぶ。人数・修正の収束条件は既存の `rules/orchestration-budget.md` に従う。
- 有用な独立 packet を並行させ、writer の重なりと重い build だけを直列化する。
  `prover` を実際に起動できなければ既存の `rules/agent-orchestration.md` の fallback を使う。
  設定調査を証明の代替成果にしない。
- 各 coherent slice で対象テスト、必要な査読、`tasks/current.md`・`tasks/research-lab.md`・
  progress を同期し、明示したパスを commit、outbound 全体を確認して push する。
  未承認 question は混ぜず、未完了 gate は理由と owner を残す。

### 再開用の短い指示

> `tasks/effects-handler-next.md` と `tasks/current.md` を実行入口として、現在の HEAD と
> 最新 checkpoint を照合する。Luna は primary を継続する。H1-L の reviewed bounded
> obstructionと H2 の reviewed structural/activation slice を繰り返さない。今は
> `notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md` と
> `notes/progress/2026-10-15-pending-symbolic-cut-continuation-falsifier.md` を使い、
> source Function dispatch / typed-drain で combined pending-order/direct-remapped-use
> premise を認証または反証する。
> Cargo budget は observer の二回で消費済み。H1/H2/U を早期に閉じず、既存の衛生性 proof
> と P は premises をソースへ対応づけてから使う。H3/P と production/F5 は必要条件が
> 満たされるまで無効のままにする。
> 完成済みの parser・payload/raw-k 制約・回答済み question は再開しない。
> 新しい言語上の選択だけを user に返し、独立した承認済み作業は続ける。

## 8. 計画作成・レビュー記録

この変更は M0 の引き継ぎ記録。`task_decomposer` が依存関係と開始 packet、
`explorer` が実在する owner・test filter・既存 fixture の証拠を読み取り専用で確認した。
独立した `compiler_referee` 一名が権限、proof/implementation の順序、U の範囲、
source 到達性の扱いを査読し、blocking / major finding なし。
軽微な明確化として §24 の receiver role を H1-A に追記した。

記録・参照・owner 対応と `git diff --check` のみを検査した。compiler code、設定、
テスト期待値は変更せず、build/test/benchmark は実行していない。
本計画と `tasks/current.md`・`tasks/research-lab.md` を同期する。
新しい設計決定や theorem status の変更がないため design index の更新は不要。
将来の H1〜H4 の worker はまだ起動していない。
