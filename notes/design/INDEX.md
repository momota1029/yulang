# Design documents

Navigation aid. Each document is authoritative only for its own text and scope; read its Status line.

- [要求駆動計算と B2/B3/B5 の今回の結果](../handoff/2026-11-07-common-demand-and-foundations-results.md) — 全量化した主要 theorem、元 §7 の未閉契約、B/C の到達、実根一覧、最終検証と次の着手。

- [共通 Core.infer の構文拡張](2026-11-07-core-common-coverage.md) — 部分言語を実装・証明。literal/structural data/strictApp/単一 bind case/leaf を公開 principal・全 parameter・拒否完全性へ接続し、旧 PresenceOnly 入口を保存。一般署名・B1〜B6 全体の残りを明示。

- [Common nominal head と ground cast の基礎](2026-11-07-common-nominal-head-ground-foundations.md) — 任意 Common 型/行引数の不変性、共有 slot の有限比較、外側の根の旧順序保存、明示した scalar/nominal ground 文法の実 compatibility。全 carrier・site・pure plan の残りを区別。

- [Common signed row 解釈の基礎](2026-11-07-common-signed-row-foundations.md) — 任意 scope 数で包含を保存・反映し protect/release/residual と可換。任意 Common row の可逆 transport と有限 row 式の一致を証明。全 effect 生成・solver は未完。

- [Common pattern の環境・実照合への橋](2026-11-07-common-pattern-environment.md) — 順序・共有・単相の環境拡張と default 入力の有限生成、実 lookup と構造 matcher の型保存。外部の default 成功契約と、全生成・部分正当性・行・coverage の未完を明示。

- [Common role と全公開 interface の残る境界](2026-11-07-common-role-canonical-boundaries.md) — 実 checker が受理する規則の regular goal 列が要求同値でも再訪しないことを証明。B4 の停止手続きと A2 の全 family canonicalizer の不足を元の量化で記録。

- [Common の有限 operation 宣言と request 生成](2026-11-07-common-effect-request-generation.md) — 有限 table、局所型変数、kind 検査と request 一段の生成 iff。再帰的 effect、全称 handler、見える effect、全 solver の未完を明示。

- [A1 の全旧 source 共有 witness に残る構成](2026-11-07-common-legacy-shared-witness-gap.md) — 全 supported source の元 statement と、共有 constructor・負位置・行・旧出力を同時回収する不足を記録。既存の envelope/erasure 反例を A1 の反証とは扱わない。

- [Common への effect・role・nominal 統合: 残る契約](2026-11-07-common-effect-role-nominal-contracts.md) — Draft。有限 verified declaration と任意の意味関数を分けた B3/B4/B5 の原契約。後続で閉じた signed row 解釈と request/nominal の独立基礎は各メモへリンクし、未完の公開統合契約は量化を維持。

- [共通推論の高速化と参照実装からの refinement](2026-11-07-common-inference-refinement.md) — Draft。実 clause の要求根と逆向き bound 計算、任意 snapshot の要求同値、全検査後の solveAll / Core.infer との一致を実装・証明。要求した成分の飽和、関数/SCC の実行前検査、memo と費用評価は未完。速度は未測定。

**2026-11-04:** the 2026-10 inference-proof sprint documents were removed from the working tree.
They remain in tag `archive/proof-sprint-2026-11-04`. What remains here is the
parser, syntax, Yumark and declaration designs from 2026-08 and 2026-09, plus `oracles/`.
The type-inference core calculus will be written in Lean and a companion document; add its entry here when it exists.

- [Presence 型と required-field 主型推論の統合](2026-11-06-presence-inference-integration.md) — Draft。有限data型の意味と全parameterの一方向の橋、presence layer、旧regular graphの全有限data観測とblock closureの保存・反映を実装。関数/行意味、presence制約の飽和・coalescing、全source instance同値は残る。
- [M1 solver の内部契約と局所更新](2026-11-07-m1-solver-and-locality.md) — Draft。要求モデル・具体 tail/mask 解・全 contextual constructor 解・旧 supported source の主型性、SCC selection と増分 build、selection/具体化/簡約の費用上界、完全な標準形との未接続境界。
- [共通 presence carrier と全 source の M1 残契約](2026-11-07-m1-remaining-contracts.md) — Draft。exactEmpty/required/whole default、関数・行・同深さ tail/mask を統合した具体モデル、全入力 presence solver、統合 Core.infer と旧結果型の埋込みについて、未実装の定理を量化・前提つきで記録する。
- [M1 の具体共通 carrier と残る compiler 境界](2026-11-07-m1-common-model.md) — Draft。独立構文・要求意味・strict data image、guarded 子と同深さ record/default tail の regular 解、行との simultaneous family、全 source compiler と完全標準形の残契約。
- [Scoped pattern defaults と joint payload coverage](2026-11-06-scoped-pattern-defaults.md) — 解決済みkernelの設計。Q4の累積環境、Q5〜Q7の順序・名前検査、Q8と同じ具体evaluatorへの型付き網羅性契約、source接続の残る境界。
- [Rust AST oracle の段階的導入計画](2026-11-06-rust-oracle-plan.md) — Draft。Lean data evaluatorとの値・訪問列の差分試験から始め、関数・handler・辞書・cast・推論、Perceus/evidence passing/Craneliftの導入境界を分ける。§6はcache・let選言・疎な飽和・行判定・scheme共有、§7はarena/path intern・依存収集・module量化・SCC単位のselectionとrole索引・三つの初期benchmarkの設計。
- [Postfix `if` parser addendum](2026-11-08-postfix-if-addendum.md) — Authoritative semantics; proposed CST and recovery.
- [Parser gap closure: forms promised by `spec/` that yu-syntax does not yet read](2026-11-04-parser-gap-closure-addendum.md) — Authoritative (approved 2026-11-04)
- [Parser gap closure, part 2: lambda record parameter, brace spread, scrutinee-less `case:`](2026-11-07-parser-gap-closure-addendum-2.md) — Authoritative (approved 2026-11-07)
- [Phase 2 parser compatibility fixture schema](2026-08-20-phase2-parser-fixture-schema.md) — Authoritative。実 fixture case の投入と population 前の Open questions の解消は、次スライス以降で進める。
- [`yu-syntax` chasa-based parsing architecture](2026-08-20-yu-syntax-chasa-architecture.md) — Proposal。実装、dependency 追加、grammar の拡張はこの文書の scope 外とする。
- [Declaration companion Gate 2 semantic-work performance amendment](2026-08-30-declaration-companion-gate2-performance-amendment.md) — Authoritative
- [Declaration companion Gate 2 canonical recovery amendment](2026-08-30-declaration-companion-gate2-recovery-amendment.md) — Authoritative
- [Declaration companion `with:` grammar addendum](2026-08-30-declaration-companion-with-addendum.md) — Authoritative
- [`declaration.rs` production code のモジュール分割計画](2026-08-30-declaration-module-split-plan.md) — Authoritative（ユーザ承認済み、2026-08-30）。open question 1〜3・5はユーザ選択によりそれぞれ
- [Declaration companion Gate 3 speculative NUD sink amendment](2026-08-31-declaration-companion-gate3-nud-sink-amendment.md) — Authoritative
- [Authoritative: standalone doc-comment declaration and structured Yumark](2026-09-01-doc-comment-yumark-addendum.md) — Authoritative
- [Authoritative: Yumark frame transaction storage](2026-09-01-yumark-frame-transaction-storage-addendum.md) — Authoritative
- [Authoritative: Yumark Gate 3 embedded-Yulang bridge and committed state allocation](2026-09-01-yumark-gate3-embedded-yulang-allocation-amendment.md) — Authoritative
- [Authoritative: yu-syntax の式 tail 引き渡し追補](2026-09-02-yu-syntax-expression-tail-handoff-addendum.md) — Authoritative
- [Authoritative: yu-syntax recursive-descent parser rewrite](2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md) — Authoritative
- [Authoritative: Yumark Gate 3b canonical recovery episodes](2026-09-02-yumark-gate3b-canonical-recovery-episode-amendment.md) — Authoritative
- [Authoritative: Yumark Gate 3b recovery adoption matrix](2026-09-02-yumark-gate3b-recovery-adoption-matrix.md) — Authoritative
- [Authoritative: G4b E5 index-call control correction](2026-09-03-yu-syntax-g4b-e5-index-call-correction.md) — Authoritative
- [Authoritative: G4b E5 index ML-application control correction](2026-09-03-yu-syntax-g4b-e5-index-ml-application-correction.md) — Authoritative
- [Draft: yu-syntax Gate 3 fixed-tail pilot](2026-09-03-yu-syntax-gate3-fixed-tail-pilot.md) — Authoritative
- [yu-syntax Gate 4–6 dependency-SCC and operator-evidence amendment](2026-09-03-yu-syntax-gate4-6-scc-amendment.md) — Authoritative
- [Authoritative: minimal successor rewrite and token transaction amendment](2026-09-03-yu-syntax-minimal-rewrite-token-transaction-amendment.md) — Authoritative
- [Authoritative: successor rewrite direct functions and no-`IsCut` correction](2026-09-03-yu-syntax-rewrite-direct-functions-no-iscut-amendment.md) — Authoritative; outer-state `check` bridge superseded
- [Authoritative: polymorphic-variant NT-8 same-slot retry trivia ownership](2026-09-04-yu-syntax-pv-nt8-same-slot-trivia-amendment.md) — Authoritative
- [Direct expression and statement owner fence-entry addendum](2026-09-05-direct-expression-successor-acquisition-addendum.md) — Authoritative
- [Direct literal cone for the recursive-descent rewrite](2026-09-05-direct-literal-cone-addendum.md) — Authoritative
- [Direct TND statement-line handoff amendment](2026-09-05-direct-tnd-statement-line-handoff-amendment.md) — Authoritative
- [Direct Type derives episode-boundary amendment](2026-09-05-direct-type-derives-episode-boundary-amendment.md) — Authoritative
- [Fenced current-Item normalization addendum](2026-09-05-fenced-current-item-normalization-addendum.md) — Authoritative
- [Item emission-ownership frontier amendment](2026-09-05-item-emission-ownership-frontier-amendment.md) — Authoritative
- [Fenced block-comment lexical capability amendment](2026-09-05-yumark-fenced-block-comment-lexer-amendment.md) — Authoritative
- [Authoritative: parsed Yulang code fences in Yumark](2026-09-05-yumark-parsed-yulang-fence-addendum.md) — Authoritative
- [Direct declaration-companion vertical-slices amendment](2026-09-06-direct-declaration-companion-vertical-slices-amendment.md) — Authoritative
- [Direct Enum/Error companion trailing-close amendment](2026-09-06-direct-enum-error-companion-trailing-close-amendment.md) — Authoritative
- [Direct Struct companion trailing-close amendment](2026-09-06-direct-struct-companion-trailing-close-amendment.md) — Authoritative
- [Successor typed output and recovery amendment](2026-09-06-successor-typed-output-recovery-amendment.md) — Authoritative
- [Yumark active-prefix trailing-whitespace amendment](2026-09-06-yumark-prefix-trailing-whitespace-amendment.md) — Authoritative, implemented**
- [Successor ambient-claim context prerequisite amendment](2026-09-07-successor-ambient-claim-context-prerequisite-amendment.md) — Authoritative; ordinary-only construction/proof pass complete
- [Successor shared delimited boundary-priority correction](2026-09-07-successor-delimited-boundary-priority-correction.md) — Authoritative; bounded private construction complete
- [Successor delimited PV EffectRow structured-Error extent addendum](2026-09-07-successor-delimited-pv-effect-row-extent-addendum.md) — Authoritative; bounded private construction complete
- [Successor delimited PV structured-Error extent correction addendum](2026-09-07-successor-delimited-pv-extent-correction-addendum.md) — Authoritative; bounded private construction complete
- [Successor PV payload-admission capability amendment](2026-09-07-successor-pv-payload-admission-capability-amendment.md) — Draft; architecture re-entry required
- [Successor PV scalar-frontier evidence plan](2026-09-07-successor-pv-scalar-frontier-evidence-plan.md) — Superseded as a construction prerequisite; historical evidence retained
- [Successor PV wrong-kind primary-completion amendment](2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md) — Superseded; primary-completion proposal not implemented
- [Successor retry-leading diagnostic-extent amendment](2026-09-07-successor-retry-leading-diagnostic-extent-amendment.md) — Authoritative
- [Structured-recovery extent-validation addendum](2026-09-07-successor-structured-recovery-extent-validation-addendum.md) — Authoritative
- [Structured-recovery prerequisite-ordering addendum](2026-09-07-successor-structured-recovery-prerequisite-ordering-addendum.md) — Authoritative
- [Successor structured-recovery reservation amendment](2026-09-07-successor-structured-recovery-reservation-amendment.md) — Authoritative
- [Successor T2a embedded CST-topology amendment](2026-09-07-successor-t2a-embedded-cst-topology-amendment.md) — Authoritative
- [Successor T2a Yumark evidence-timing correction](2026-09-07-successor-t2a-yumark-evidence-timing-correction.md) — Authoritative
- [Successor T2b PathSegment recovery amendment](2026-09-07-successor-t2b-pathsegment-recovery-amendment.md) — Authoritative
- [Successor T3 TypeCall recovery amendment](2026-09-07-successor-t3-typecall-recovery-amendment.md) — Authoritative; T3 core and shared horizontal private construction complete
- [Successor T4 delimited recovery register correction amendment](2026-09-07-successor-t4-delimited-register-correction-amendment.md) — Authoritative in retained scope; P/E provenance and recovery machinery
- [Successor T4 inherited type-ML correction amendment](2026-09-07-successor-t4-inherited-type-ml-correction-amendment.md) — Authoritative for inherited Type-ML provenance; shared horizontal
- [Act current-Item typed recovery](2026-09-08-successor-act-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Binding current-Item typed recovery](2026-09-08-successor-binding-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Braced canonical Statement sequence current-Item recovery](2026-09-08-successor-braced-statement-sequence-current-item-recovery.md) — Authoritative; private O3b construction complete
- [BracketRowArrow current-Item recovery](2026-09-08-successor-bracket-arrow-current-item-recovery.md) — Authoritative; private BracketRowArrow construction complete
- [BracketRow current-Item recovery](2026-09-08-successor-bracket-row-current-item-recovery.md) — Authoritative; private BracketRow-owned construction complete
- [CaseLike Arrow/Body current-Item recovery](2026-09-08-successor-case-like-arrow-body-current-item-recovery.md) — Authoritative; private O3b construction complete
- [CaseLike structural current-Item recovery](2026-09-08-successor-case-like-structural-current-item-recovery.md) — Authoritative; private O3b construction complete
- [D4e required-Type malformed role correction](2026-09-08-successor-d4e-required-type-role-correction.md) — Authoritative conformance clarification
- [Declaration companion current-Item typed recovery](2026-09-08-successor-declaration-companion-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Declaration variant current-Item typed recovery](2026-09-08-successor-declaration-variant-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Derives current-Item typed recovery](2026-09-08-successor-derives-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Expression Colon current-depth layout-sequence context](2026-09-08-successor-expression-colon-layout-sequence-context.md) — Authoritative; private O3b construction complete
- [Expression Colon/With inline current-Item recovery](2026-09-08-successor-expression-colon-with-inline-current-item-recovery.md) — Authoritative; private O3b inline construction complete
- [Expression shared-delimited current-Item recovery](2026-09-08-successor-expression-delimited-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Expression fixed-tail current-Item recovery](2026-09-08-successor-expression-fixed-tail-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Expression indented Statement recovery-role transport](2026-09-08-successor-expression-indented-statement-role-transport.md) — Authoritative; private O3b construction complete
- [Expression required-operand current-Item recovery](2026-09-08-successor-expression-operand-current-item-recovery.md) — Authoritative; private O3b construction complete; joint certification
- [Forall current-Item recovery](2026-09-08-successor-forall-current-item-recovery.md) — Authoritative; private Forall-owned construction complete
- [If current-Item typed recovery](2026-09-08-successor-if-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Impl current-Item typed recovery](2026-09-08-successor-impl-current-item-recovery.md) — Authoritative; private O3b construction complete
- [LeadingEffectTypeHead current-Item recovery](2026-09-08-successor-leading-row-head-current-item-recovery.md) — Authoritative; private LeadingEffectTypeHead construction complete
- [Mod current-Item typed recovery](2026-09-08-successor-mod-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Pattern default-Expression Missing publication](2026-09-08-successor-pattern-default-expression-publication.md) — Authoritative; private O3b substep complete
- [Pattern delimiter Missing and delegated slot publication](2026-09-08-successor-pattern-delimited-slot-publication.md) — Authoritative; private O3b substep complete
- [Pattern primary and tail-slot current-Item recovery](2026-09-08-successor-pattern-primary-current-item-recovery.md) — Authoritative; private O3b substep complete
- [Pattern sequence current-Item recovery](2026-09-08-successor-pattern-sequence-current-item-recovery.md) — Authoritative; private O3b substep complete
- [Parenthesized and EffectRow current-Item recovery](2026-09-08-successor-pe-current-item-recovery.md) — Authoritative; private P/E-owned construction complete
- [Successor public cutover priority](2026-09-08-successor-public-cutover-priority-amendment.md) — Authoritative; public cutover complete; deferred owner work remains
- [Successor polymorphic-variant current-Item recovery](2026-09-08-successor-pv-current-item-recovery.md) — Authoritative; private PV-owned construction complete
- [Named-record field-internal current-Item recovery](2026-09-08-successor-record-field-current-item-recovery.md) — Authoritative; private field-internal construction complete
- [Named-record sequence and close current-Item recovery](2026-09-08-successor-record-sequence-current-item-recovery.md) — Authoritative; private construction complete
- [Accepted-input compatibility and successor recovery authority](2026-09-08-successor-recovery-authority-amendment.md) — Authoritative; §4 private delimiter integration complete
- [Required-Type equals ownership and field forward progress](2026-09-08-successor-required-type-equals-ownership.md) — Authoritative; private ownership/progress correction complete
- [Caller-owned required-Type Missing roles](2026-09-08-successor-required-type-missing-roles.md) — Authoritative; private helper publication and caller controls complete
- [Role current-Item typed recovery](2026-09-08-successor-role-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Rule ExpressionList current-Item typed recovery](2026-09-08-successor-rule-expression-list-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Rule DSL literal current-Item typed recovery](2026-09-08-successor-rule-literal-current-item-recovery.md) — Authoritative; private O3b construction complete
- [StringLiteral current-Item typed recovery](2026-09-08-successor-string-literal-current-item-recovery.md) — Authoritative; private O3b construction pending
- [Struct header current-Item typed recovery](2026-09-08-successor-struct-header-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Type caller conformance after owner-local recovery migration](2026-09-08-successor-type-caller-conformance.md) — Authoritative conformance clarification; private caller controls complete
- [Successor Type contextual-boundary correction](2026-09-08-successor-type-contextual-boundary-correction.md) — Authoritative; private correction complete
- [VirtualStatementBlock current-Item typed recovery](2026-09-08-successor-virtual-statement-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Operator compilation topology](2026-09-09-operator-compilation-topology.md) — Authoritative; private construction complete
- [Source-root statement topology](2026-09-09-root-statement-topology.md) — Authoritative; private construction complete
- [Draft: canonical AST/direct-CST materialization seam](2026-09-09-successor-canonical-materialization-seam-draft.md) — Superseded by `2026-09-09-successor-rowan-cst-only-amendment-draft.md`
- [Draft: canonical successor syntax products](2026-09-09-successor-canonical-syntax-products-draft.md) — Superseded by `2026-09-09-successor-rowan-cst-only-amendment-draft.md`
- [CaseLike Separator and Catch-close current-Item recovery](2026-09-09-successor-case-like-separator-close-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Cast Body current-Item recovery](2026-09-09-successor-cast-body-current-item-recovery.md) — Authoritative; private construction complete
- [Cast BodyIntroducer current-Item recovery](2026-09-09-successor-cast-body-introducer-current-item-recovery.md) — Authoritative; private construction complete
- [Cast Pattern close current-Item recovery](2026-09-09-successor-cast-pattern-close-current-item-recovery.md) — Authoritative; private construction complete
- [Cast Pattern current-Item recovery](2026-09-09-successor-cast-pattern-current-item-recovery.md) — Authoritative; private construction complete
- [Cast PatternIntroducer current-Item recovery](2026-09-09-successor-cast-pattern-introducer-current-item-recovery.md) — Authoritative; private construction complete
- [Cast TargetIntroducer current-Item recovery](2026-09-09-successor-cast-target-introducer-current-item-recovery.md) — Authoritative; private construction complete
- [CST-derived syntax diagnostics successor amendment](2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md) — Authoritative
- [Declaration field sequence current-Item recovery](2026-09-09-successor-declaration-field-sequence-current-item-recovery.md) — Authoritative; private construction complete
- [Declaration named-field current-Item recovery](2026-09-09-successor-declaration-named-field-current-item-recovery.md) — Authoritative; private construction complete
- [Enum/Error header current-Item recovery](2026-09-09-successor-enum-error-header-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Error-admission schema clarification](2026-09-09-successor-error-admission-schema-clarification.md) — Draft
- [Error-token and Invalid-node topology ordering addendum](2026-09-09-successor-error-invalid-topology-ordering-addendum.md) — Authoritative
- [Expression assignment and type-annotation tails](2026-09-09-successor-expression-structural-tails-draft.md) — Authoritative; private construction complete
- [For structural current-Item recovery](2026-09-09-successor-for-structural-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Draft: successor literal syntax products](2026-09-09-successor-literal-syntax-product-draft.md) — Superseded by `2026-09-09-successor-rowan-cst-only-amendment-draft.md`
- [Rowan CST-only successor amendment](2026-09-09-successor-rowan-cst-only-amendment-draft.md) — Authoritative
- [Rowan CST notation text-attribute escaping addendum](2026-09-09-successor-rowan-text-attribute-escaping-addendum.md) — Authoritative
- [TypeDeclaration header current-Item recovery](2026-09-09-successor-type-declaration-header-current-item-recovery.md) — Authoritative; private O3b construction complete
- [Syntax-phase public topology](2026-09-09-syntax-phase-topology.md) — Authoritative; private construction complete
- [BracedStatementBlock recovery-slot CST draft](2026-09-10-successor-braced-statement-slot-draft.md) — Rejected as unnecessary; bounded ordered-CST decoder proved; no
- [Successor CST slot-schema catalog](2026-09-10-successor-cst-slot-schema-catalog.md) — Draft
- [Expression-delimited raw-slot CST draft](2026-09-10-successor-expression-delimited-raw-slot-draft.md) — Authoritative; private construction complete
- [NamedRecordType recovery-slot CST draft](2026-09-10-successor-named-record-type-slot-draft.md) — Authoritative; private M2 construction complete
- [PolymorphicVariantType foreign-close CST slot draft](2026-09-10-successor-pv-foreign-close-slot-draft.md) — Authoritative; private M2 construction complete
- [RecordPattern foreign-close CST slot draft](2026-09-10-successor-record-pattern-foreign-close-slot-draft.md) — Authoritative; private construction complete
- [RecordPattern structured separator-slot discriminator](2026-09-10-successor-record-pattern-separator-slot.md) — Authoritative; private construction complete
- [TypeCall post-argument residual close recovery](2026-09-10-successor-typecall-close-residual-policy.md) — Authoritative; private construction complete
- [TypeCall close-slot structural boundary](2026-09-10-successor-typecall-close-slot-node.md) — Authoritative; private construction complete
- [Declaration field foreign-close CST topology](2026-09-11-successor-declaration-field-foreign-close-topology.md) — Authoritative; construction complete
- [ML separator-leading ownership](2026-09-12-successor-ml-separator-leading-ownership.md) — Authoritative; M2 construction complete
- [Parenthesized/EffectRow foreign-close CST topology](2026-09-12-successor-type-delimited-foreign-close-topology.md) — Authoritative; private M2 construction complete
- [Use group foreign-close CST topology](2026-09-12-successor-use-group-foreign-close-topology.md) — Authoritative; private M2 construction complete
- [Syntax freeze and vertical-implementation completion-policy amendment](2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md) — Authoritative
- [First HIR slice: operator-chain association](2026-09-18-hir-operator-association-first-slice-draft.md) — Authoritative
- [HIR type attachment — open questions memo](2026-09-18-hir-type-attachment-open-questions.md) — Draft (exploratory memo; records no decision)
- [AssociatedChains ownership amendment](2026-09-19-hir-associated-chains-ownership-amendment.md) — Authoritative
- [First HIR module resolution slice](2026-09-19-hir-simple-module-resolution-first-slice-draft.md) — Authoritative
- [HIR direct-root expression slice](2026-09-20-hir-direct-root-expression-slice.md) — Authoritative; construction complete (2026-09-20)
- [BracketRow close-error CST topology supersession](2026-09-20-successor-bracket-row-close-topology-supersession.md) — Authoritative; construction complete (2026-09-20)
- [B4 outer interval resolver](2026-11-08-b4-outermost-resolver.md) — Draft; conditional fixed-frontier recursion only, source propagation and descent bridges open

- [Cycle12 finite source positions](2026-11-08-cycle12-source-positions.md) — Draft; finite unary structural provenance, not full B4

- [Cycle13 materialized domain](2026-11-08-cycle13-materialized-domain.md): Draft; int-only state-dependent source template closure, not general B4.

- [Cycle14 child templates](2026-11-08-cycle14-child-templates.md): Draft; source-preserving captures and state-independent child-creation descent.

- [Cycle15 source-template closure](2026-11-08-cycle15-source-template-closure.md): Draft; computed source domain and all-state rematerialization, not saturation.

- [Cycle25: ancestor-correlated candidate paths](2026-11-09-cycle25-correlated-path-carrier.md) (Draft; metadata exactness, not B4).

- [Cycle26 global choices](2026-11-09-cycle26-global-choices.md) — Draft; finite correlated diagnostic certificates and model-family iff.

- [Cycle27: own-output stable global certificates](2026-11-09-cycle27-stable-feedback.md) — diagnostic finite search; no language driver claim.

- [Cycle28 diagnostic tree](2026-11-09-cycle28-diagnostic-tree.md): child-preserving finite certificates; no language classification.

- [Cycle29 ordered diagnostic representation](2026-11-09-cycle29-ordered-diagnostic.md) (Draft; finite fragment and explicit decoder boundary)

- [Cycle30: finite scalar evidence saturation](2026-11-09-cycle30-evidence-saturation.md) — Draft, reciprocal-variable fragment.

- [Cycle31 normalized diagnostic](2026-11-09-cycle31-normalized-diagnostic.md)

- [Cycle32 directed scalar-bound closure (Draft)](2026-11-09-cycle32-directed-bounds.md)

- [Cycle33 directed self-output diagnostic search](2026-11-09-cycle33-directed-self-output.md) — bounded certificate/model bridge, not whole B4.

- [Cycle34 directed conflict certificates](2026-11-09-cycle34-directed-conflicts.md) — Draft, sound pruning and complete model-family preservation.

- [Cycle35 structural head certificates](2026-11-09-cycle35-structural-conflict.md) — Draft; executable finite certificates and model-preserving pruning.

- [Cycle36 structural directed-path certificates](2026-11-09-cycle36-structural-paths.md)
- [Cycle37 recursive structural refutation](2026-11-09-cycle37-recursive-structural.md) — Draft, same-head recursive certificates and model-preserving filtering.

- [Cycle39 finite structural closure](2026-11-09-cycle39-structural-closure.md) — Draft, finite-rule exactness rather than unrestricted ordinary completeness.

- [Cycle40 structural carrier coverage](2026-11-09-cycle40-carrier.md): supported-rule completeness and membership fixed point.

- [Cycle47 slot equality feedback](2026-11-09-cycle47-index-equality.md): finite str evidence transport and actual producer execution.

- [Cycle48 finite source semantic completeness](2026-11-09-cycle48-semantic-source.md)

- [Cycle49 finite string source semantic bridge](2026-11-09-cycle49-source-semantic-bridge.md) — Draft; independent source clauses, semantic forcing, and checked readout, not general B4.

- [Cycle50 residual source preservation](2026-11-09-cycle50-residual-source.md) — Draft; exact complete models with retained conditional requests.

- [Cycle51 finite residual batches](2026-11-09-cycle51-residual-batches.md) — Draft; incremental seeds, equalities, and obligations preserve all source models.

- [Cycle52 residual frontier](2026-11-09-cycle52-residual-frontier.md) — Draft: exact pending membership after finite update batches.

- [Cycle53 occurrence diagnostics](2026-11-09-cycle53-occurrence-diagnostics.md) — Draft; preserve original batch/request order, duplicates and missing names, with independent source meaning.

- [Cycle54 scalar-preserving endpoints](2026-11-09-cycle54-scalar-endpoints.md) — Draft; ordinary scalar identity, finite observations, and original source meaning connected to the existing graph inspector.

- [Cycle56: canonical source-alias graph references](2026-11-09-cycle56-source-alias-graph.md) — Draft. Exact finite source identity, unknown alias captures, and original-source scalar inspection; general B4 remains open.

- [Cycle57: canonical source allocation](2026-11-09-cycle57-canonical-source-growth.md) — Draft. Incremental root allocation equals rebuilding; old roots/captures and source models are retained.

- [Cycle58: allocated graph edges](2026-11-09-cycle58-allocated-graph.md) — Draft; exact finite observations, paths and direct cycles under source allocation.

- [Cycle59: generated child source allocation](2026-11-10-cycle59-child-source-allocation.md) — Draft; computed child dependency names, root provenance and exact canonical inspection.
- [Closure-wide source occurrence allocation](2026-11-10-cycle60-closure-source-allocation.md) — Draft; one finite allocation domain for all structurally reachable child dependencies in the unary/int adapter.

- [Allocated graph updates](2026-11-10-cycle61-allocated-graph-updates.md) — Draft; finite old-node edit commutation and ordinary source-model readout through shared child allocation.

- [Source-named interval batches](2026-11-10-cycle62-source-interval-batches.md) — Draft; exact cross-batch reconciliation of arbitrary original endpoints and shared source names.

- [Cycle63 declaration capture and independent head models](2026-11-10-cycle63-declaration-capture-models.md) — Draft; source interval generation bridge, general B4 incomplete.

- [Cycle64: original where source models](2026-11-10-cycle64-where-source-models.md) — Draft; actual capture preserves all where-template models and original endpoint provenance, without selecting a centre.

- [Cycle65: actual where source allocation](2026-11-10-cycle65-where-source-allocation.md) — Draft; computed finite parent owners, no new failure, and exact arbitrary-graph snapshot preservation.

- [One root source table across actual recursive captures](2026-11-10-cycle66-root-source-history.md) — Draft。実where生成の任意有限履歴からroot source閉包、capture endpoint登録、正準ownerの同一性とgraph保持を導く。一般飽和は未達。

- [Computed fresh capture demand names](2026-11-10-cycle67-fresh-capture-demand-names.md) — Draft; collision-free local binder maps and independent original-model exactness across arbitrary actual finite selected paths. Persistent invocation sharing and B4 remain open.
- [Persistent keyed capture registry](2026-11-10-cycle68-persistent-capture-registry.md): Draft; explicit invocation/binder allocation, stable reuse and arbitrary finite original shared-model exactness.

- [Structural addressed capture models](2026-11-10-cycle69-addressed-capture-models.md): Draft; computed finite invocation identities, real where provenance, resumable prefixes and original shared-model exactness.

- [Boundary inputs ledger](2026-11-10-boundary-inputs-ledger.md): Draft; I-13 first through fourth passes across capture, graph, annotations, concrete Protocols, DynamicIndex residual diagnostics, interval expansion/dictionaries, and Main boundaries. Two scoped questions; whole-model input audit remains incomplete.

- [Boundary import inventory](2026-11-10-boundary-input-coverage.tsv): Source hashes and Main/Audit import reachability for 242 CommonRole modules; reproducible with `tools/boundary-input-inventory.py`. Name mentions are not completed input audits.
- [Finite associated source factorization](2026-11-10-cycle76-finite-source-factorization.md): Draft; ordinary source equality before finite associated saturation, independent declaration-model exactness, and the remaining caller inputs. General B4 remains open.
- [Computed named associated-source models](2026-11-10-cycle77-named-associated-source-models.md): Draft; computed table and endpoint slots, independent source-name derivations, concrete evidence and shared-model exactness. General source/template adequacy and B4 remain open.

- [Structural associated goal templates](2026-11-10-cycle78-structural-associated-templates.md): Draft; checked first-order template generation and independent structural source derivations; full source adequacy remains open.

- [Cycle79: checked associated programs](2026-11-10-cycle79-checked-associated-programs.md) — Draft: computed whole-list scope/arity/name validation, exact erasure and existing source-model contracts.

- [Cycle80: associated clause extraction](2026-11-10-cycle80-associated-clause-extraction.md) — Draft: exact grouped equation extraction, source occurrence provenance, and independent derivation correspondence; parser and bare obligations remain outside.

- [Cycle81 source role obligations](2026-11-10-cycle81-source-role-obligations.md): Draft. Lossless finite clause checking and independent role discharge; scalar heads remain explicit.

- [Cycle82 source state role discharge](2026-11-10-cycle82-source-state-role-discharge.md) — Draft: computed joint allocation and evidence-backed all-role readiness.

- [Cycle83 named source entry](2026-11-10-cycle83-named-source-entry.md) — Draft: checked finite source, named scalar assumptions, independent source readiness.

- [Cycle84 source renaming](2026-11-10-cycle84-source-renaming.md): Draft; capture-avoiding finite source names, independent derivations/models, and readiness invariance.

- [Finite-support source renaming](2026-11-10-cycle85-finite-source-renaming.md) — Draft, cycle85 executable collision boundary.

- [Computed source-name allocation](2026-11-10-cycle86-computed-source-allocation.md) — cycle86 proof interface: finite capacity, exact evidence/models/readiness, canonical safe-renaming invariance and idempotence; declaration lowering still open.

- [Checked annotated-literal inputs](2026-11-10-cycle87-annotated-literal-inputs.md) — Draft; literal typing and explicit scalar annotations produce checked source inputs, with independent finite readiness exactness.

- [Checked scalar expression inputs](2026-11-10-cycle88-scalar-expression-inputs.md) — Draft; structural evaluator, existing let/variable typing and independent finite source readiness. Full source lowering remains open.

- [Generated where closure](2026-11-10-cycle89-generated-where-closure.md) — Draft: actual first-order recursive child closure, independent provenance and root success preservation.

- [Interval work closure](2026-11-10-cycle90-interval-work-closure.md) — Draft: real recursive interval where work, explicit outside boundaries, and computed original-source allocation.

- [Guarded recursive interval plans](2026-11-10-cycle91-guarded-interval-plans.md) — finite candidate alternatives, conjunctive children and one shared-source ordinary model; fixed-syntax boundary.

- [Retained interval diagnostic frontier](2026-11-10-cycle92-guarded-interval-frontier.md) — Draft; incomplete child retention and exact guarded-plan erasure; fixed syntax only.

- [Cycle94 frontier ordinary graph family](2026-11-10-cycle94-frontier-ordinary-graphs.md) — Draft; all-model graph integration and replay boundary.

- [State-materialized interval frontiers](2026-11-10-cycle95-state-materialized-frontiers.md) — Draft; ordinary int evidence, all-model Form preservation and finite regenerated work.

- [Cycle96: finite actual materialization changes](2026-11-10-cycle96-materialization-progress.md) — Draft; source-computed progress bound and entire public diagnostic-tree connection; not saturation.

- [Cycle97 diagnostic replay](2026-11-10-cycle97-frontier-replay.md) — Draft, executable tree reuse and source-derived rebuild/visit bounds.

- [Cycle98 checked ordinary replay](2026-11-10-cycle98-checked-ordinary-replay.md) — Draft; executable cumulative solver checks, shared models and internally derived replay Chain.

- [Cycle99 evidence replay](2026-11-10-cycle99-evidence-replay.md) — Draft; internally generated finite scalar batches, exact model preservation/fixedpoint and checked replay.
- [Cycle100 mixed associated/ordinary closure](2026-11-10-cycle100-mixed-evidence-closure.md): Draft finite mixed derivation, fixedpoint and checked replay boundary; full B4 remains open.

- [Cycle101: checked structural source and mixed closure](2026-11-10-cycle101-structural-mixed-source.md) — Draft, finite named-source correspondence and remaining B4 boundaries.
- [Cycle102: ordinary-only variables in structural mixed allocation](2026-11-10-cycle102-ambient-mixed-source.md) — Computed extra slots and exact source-model correspondence; finite scope-resolved name list remains input.

- [Cycle103: named ordinary constraints compute allocation and state](2026-11-10-cycle103-named-ordinary-inputs.md) (Draft implementation contract).

- [Cycle104: checked grouped clauses and named ordinary input](2026-11-11-cycle104-checked-mixed-source.md) (Draft, 2026-11-11). Independent source-model exactness through the actual mixed closure; full B4 remains open.

- [Cycle105: computed evidence discharges retained source roles](2026-11-11-cycle105-evidence-role-discharge.md) — 有限sourceの実mixed evidenceから全role義務へ接続。caller head mapを除去。ordinary整合性とrole dischargeを分離し、B4全体の未達を維持。

- [Cycle106: source evidence and recursive diagnostic forests](2026-11-11-cycle106-source-diagnostic-forest.md) — Draft; Paterson-generated failure-preserving trees and arbitrary-depth source-to-child exactness, without caller fuel or work tables.

- [Cycle107: diagnostic trees and ordered dictionary plans](2026-11-11-cycle107-diagnostic-dictionary-projection.md) — Draft; complete payload equality, failure-preserving enrichment and source-to-dictionary path exactness.

- [Cycle108: source environment and diagnostic order](2026-11-11-cycle108-source-environment-congruence.md) — Draft; equal visible declarations preserve mixed source evidence, full dictionary payloads and all retained failed diagnostic structure.

- [Cycle110: structural ordinary / associated finite feedback](2026-11-11-cycle110-structural-role-feedback.md) — computed carrier, independent schedules, actual solver, and named structural input boundary.

- [Cycle111: independent named structural derivations](2026-11-11-cycle111-named-derivations.md) — Draft implementation, source-name allocation/readback and ordinary solver exactness.
- [Ordinary-state scalar registry bridge](2026-11-11-cycle114-scalar-registry.md) — Draft. Independent four-way fragment classification, actual declaration identities, and all-model dictionary evidence; general B4 remains open.

- [Cycle118 scalar registry exactness and all-model dictionaries](2026-11-11-cycle118-scalar-registry.md) (Draft).

- [Cycle118 annotated expressions to scalar registry dictionaries](2026-11-11-cycle118-expression-registry.md) (Draft).

- [Cycle118 source saturation to scalar registry classification](2026-11-11-cycle118-saturated-registry.md) (Draft).

- [Cycle118 concrete source witness for old B4 target overlap](2026-11-11-cycle118-target-obstruction.md) (Draft, supervisor review).

- [General B4 source boundary inventory](2026-11-11-astra-general-boundary.md) — Draft; concrete ordinary components, field-by-field missing source bridges, and frozen-target addendum mismatch.

- [B4 target V2](2026-11-11-cycle119-b4-target-v2.md) — I-17 guarded rejection, diagnostic trees, independent functionality and revised bridge obligations.

- [General dictionaries and registry order, cycles121–122](2026-11-11-cycle122-general-dictionaries.md) — Partial I-18 item 5 and remaining model/readback boundary.

- [I-19 inspection-pending and local totality](2026-11-11-cycle123-inspection-pending.md) — V3 target repair; deterministic-child boundary remains explicit.

- [Cycle124 dictionary recording and RHS provenance](2026-11-11-cycle124-equation-recording.md) — Draft; exact equation transaction, explicit/default source obligations, and the remaining term interpretation boundary.

- [Cycle125 output-only RHS terms](2026-11-12-cycle125-output-binder-terms.md) — actual source binder interpretation, producer linkage, and retained general boundary.
- [Checked computed output transactions](2026-11-11-cycle126-computed-output-plans.md) — Draft. One visible declaration supplies plans and computed binder outputs; head interpretation and general B4 remain open.

- [Cycle127 headless dictionary recipes](2026-11-11-cycle127-headless-dictionaries.md) — Draft actual-head and whole-tree evidence bridge, item5.

- [Cycle128: raw dictionary source reconstruction](2026-11-12-cycle128-payload-reconstruction.md) — Draft implementation contract for I-18 item5; exact raw-payload/readback fidelity and all-model evidence composition.

- [Cycle128 next bridges: typed slot coverage and computed-frame order](2026-11-12-cycle128-next-bridges.md) — Proposed decomposition; no new proof or implementation claim.

- [Cycle129 dictionary order and typed transport](2026-11-12-cycle129-dictionary-transport.md) — Draft, item5; preserves fixed-context boundaries.

- [Cycle130 recursive source evidence](2026-11-12-cycle130-recursive-evidence.md) — Draft, I-21; per-model equations, exact readback and the original-state universal-model boundary.

- [Cycle131 stable-state skeleton](2026-11-12-b4-stable-evidence-skeleton.md) — Draft, I-23; target-preserving V4 with explicit generation bridge.
- [Cycle131 dictionary policy](2026-11-12-cycle131-dictionary-policy.md) — Draft; K2 guards for completed source trees.

- [Committed evidence and journal obligations](2026-11-12-cycle131-committed-evidence.md)
- [Stale journal choice obstruction](2026-11-12-b4-journal-choice-obstruction.md)

- [Feedback journal source Evidence](2026-11-12-cycle133-feedback-source-evidence.md): source-formed recorded packets, explicit current-selection residual.

- [Cycle136 ordinary source-evidence transport](2026-11-12-cycle136-ordinary-evidence-transport.md) (Draft).

- [Cycles131–136 dictionary module guide](2026-11-12-cycle131-136-module-guide.md)

- [Item 4f nominal support module guide](2026-11-12-general-nominal-support-module-guide.md) — Partial; provenance-retaining guarded expansion, with termination still open.

- [2026-11-12 General nominal guarded installation order](2026-11-12-general-nominal-support-order-module-guide.md) — Item 4g administrative accessibility and the remaining installation-order obligation.
## Cycle150 dictionary Evidence work (2026-11-12, partial)

- [dots-cycle150-alias-mixed-locality](dots-cycle150-alias-mixed-locality.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-alias-recorded-locality](dots-cycle150-alias-recorded-locality.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-binary-branch-leaf](dots-cycle150-binary-branch-leaf.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-branch-coverage](dots-cycle150-branch-coverage.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-finite-joint-example](dots-cycle150-finite-joint-example.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-general-evidence-residual](dots-cycle150-general-evidence-residual.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-named-locality](dots-cycle150-named-locality.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-ordinary-structural-coverage](dots-cycle150-ordinary-structural-coverage.md) — partial structural proof/review; general V5 remains8/14 unresolved.

- [2026-11-13 Termination proof plan](2026-11-13-termination-proof-plan.md) — Item 4h; finite-signature measure, lemma ledger, and the unresolved sibling-output counterexecution analysis.
- [dots-cycle150-alias-tree-locality](dots-cycle150-alias-tree-locality.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-module-guide](dots-cycle150-module-guide.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-recursive-binary-tree](dots-cycle150-recursive-binary-tree.md) — partial structural proof/review; general V5 remains8/14 unresolved.
- [dots-cycle150-tree-coverage](dots-cycle150-tree-coverage.md) — partial structural proof/review; general V5 remains8/14 unresolved.

## Cycle151 variable where Evidence (partial)

- [dots-cycle151-unrecorded-alias-joint](dots-cycle151-unrecorded-alias-joint.md) — partial soundness, general V5 remains8/14unresolved.
- [dots-cycle151-variable-nonterminal-evidence](dots-cycle151-variable-nonterminal-evidence.md) — partial soundness, general V5 remains8/14unresolved.
- [dots-cycle151-variable-where-coverage](dots-cycle151-variable-where-coverage.md) — partial soundness, general V5 remains8/14unresolved.
- [dots-cycle151-real-alias-leaf-regression](dots-cycle151-real-alias-leaf-regression.md) — partial theorem/regression, not unrestricted V5.
- [dots-cycle151-stable-two-alias-dictionary](dots-cycle151-stable-two-alias-dictionary.md) — partial theorem/regression, not unrestricted V5.
- [dots-cycle151-disjoint-output-alias-residual](dots-cycle151-disjoint-output-alias-residual.md) — partial theorem/regression, not unrestricted V5.
- [dots-cycle151-observed-named-output](dots-cycle151-observed-named-output.md) — partial theorem/regression, not unrestricted V5.
- [Item 4i downstream output support](2026-11-13-general-nominal-downstream-support.md) — Partial implementation; independent support guard, snapshot-depth proof, and remaining termination obligations.
- [Item 4i downstream module guide](2026-11-13-general-nominal-downstream-module-guide.md) — Additive guard, boundary, regressions, order contract, and audit.

- [Item 4j: general nominal generation-budget checks](2026-11-13-general-nominal-budget.md) — Partial: actual Container and P/C/W installations, observation-depth transport, bounded measure obstructions; L5–L7 and progress remain open.
- [General nominal budget module guide](2026-11-13-general-nominal-budget-module-guide.md) — Five additive modules and their separate audit part.
- [Cycle152 observed recursive evidence](2026-11-12-cycle152-observed-recursive-evidence.md) — conditional soundness.
- [Cycle152 observed initial example](2026-11-12-cycle152-observed-initial.md) — actual InitialSource.
- [Cycle152 observed request transport](2026-11-12-cycle152-observed-request-transport.md) — ordinary-only trace.

- [Cycle152 named output complete example](2026-11-12-cycle152-observed-complete.md) — exact stated scope.
- [Cycle152 alias installation obstruction](2026-11-12-cycle152-alias-install-obstruction.md) — necessary condition only.
- [Cycle152 module guide](dots-cycle152-module-guide.md).

- [Cycle152 closed observed requests](2026-11-12-cycle152-closed-observed-requests.md) — conditional non-scalar materialization.

- [Cycle152 arbitrary finite arity requests](2026-11-12-cycle152-finite-arity-observed-requests.md) — materialization only.

- [Item 4k: captured-value provenance](2026-11-13-general-nominal-value-provenance.md) — Partial: exact checked/source fixture, additive child-value guard, all-Step depth-zero preservation; stress execution and budget remain open.
- [Captured-value provenance module guide](2026-11-13-general-nominal-value-provenance-module-guide.md) — Ten additive modules and their audit part.

- [Item 4l: concrete provenance checkpoint](2026-11-13-general-nominal-provenance-checkpoint.md) — Partial: actual four-Step P/ExtractA prefix and concrete paired exclusion; the full source checkpoint bridge and L5–L7 remain open.
- [Provenance checkpoint module guide](2026-11-13-general-nominal-provenance-checkpoint-module-guide.md) — Eight additive modules and a separate audit part.
- [2026-11-13-cycle154-finite-observed-example](2026-11-13-cycle154-finite-observed-example.md) — cycle154 条件付き辞書健全性・検証例。

- [2026-11-13-cycle154-historical-request-models](2026-11-13-cycle154-historical-request-models.md) — cycle154 条件付き辞書健全性・検証例。
- [2026-11-13-cycle154-historical-tree-branch](2026-11-13-cycle154-historical-tree-branch.md) — cycle154 条件付き辞書健全性・検証例。
- [2026-11-13-cycle154-historical-value-requests](2026-11-13-cycle154-historical-value-requests.md) — cycle154 条件付き辞書健全性・検証例。
- [2026-11-13-cycle154-value-evidence](2026-11-13-cycle154-value-evidence.md) — cycle154 条件付き辞書健全性・検証例。
- [2026-11-13-cycle154-module-guide](2026-11-13-cycle154-module-guide.md) — cycle154 条件付き辞書健全性・検証例。
- [2026-11-13-cycle154-recorded-requests](2026-11-13-cycle154-recorded-requests.md) — cycle154 条件付き辞書健全性・検証例。
- [Fresh termination analysis](2026-11-13-termination-fresh-analysis.md) — Draft acyclic accumulator counterexample; checked algebraic core and infinite-installation necessity, full Lean trace still open.
- [Unsettled output deferral](2026-11-13-unsettled-output-deferral.md) — Additive head-provenance guard and B4 boundary; conditional pump exclusion and finite-signature accessibility, source budget and concrete prefix certificate remain open.

- [Settled-cover obstruction](2026-11-13-settled-cover-obstruction.md) — Two-role interval-sharing counterexecution on paper; checked declarations/source and exact leaf branch models, complete Step trace and SourceBudget remain open.
- [Shared origins and lazy nonpoint readback](2026-11-13-nonpoint-provenance.md) — Additive provenance guard and emitter, concrete first-round deferral, finite symbolic settled readback, bounded term enumeration, and conditional accessibility; source refinement and SourceBudget remain open.
- [Hole elimination, observations, and interval facets](2026-11-13-hole-elimination.md) — Source-formed cyclic refresh, computed endpoint provenance, fixed-basis readback composition and conditional elimination budget; the actual source-to-elimination bridge and SourceBudget remain open.

- [Source frontier and point identity leaves](2026-11-13-source-frontier.md) — Finite direct K2 paths and source-derived singleton signature cover with actual guarded installation and Acc for the explicit identity-leaf restriction; general SourceBudget remains open.

- [Point-class termination: finite covers from invocation ancestry](2026-11-13-point-class-invocation-budget.md) — Draft proof companion. Exact actual-Step signature cover and Acc from one invocation-depth bound; unconditional reachable-role-hierarchy Acc with a real Wrap installation. Arbitrary recursive Class P source producers remain open.

- [Class P producer: recursive nominal peeling](2026-11-13-classp-recursive-peeling.md) — Draft proof companion. Dynamic inherited paths, fixed finite input readbacks, and unconditional actual-Step Acc for recursive unary peeling on finite ground spines; real Display installation and arbitrary-depth point sources. General ClassPProducer remains open.

- [Class P: compound input producers and a larger recursive class](2026-11-14-classp-compound-inputs.md) — Unconditional actual-Step Acc for multi-argument recursion with a distinguished finite input, checked compound/output/binder source families, and actual nominal compound emission/readback/recovery; general ClassPProducer remains open.

- [Ground-root Class P: finite input production](2026-11-14-ground-root-production.md) — Actual structural containment, shared capture and emitted-child meanings, recovered-input readback, and actual-Step Acc conditional on one local finite-capture factorization; inhabited branching Show source. Unconditional ground-root Acc remains open.

- [Ground capture factorization: actual paths and closed branching Acc](2026-11-14-ground-factorization-progress.md) — Actual nested nominal/pair capture paths, simultaneous finite values, application-fragment counted substitution, and unconditional Show (pair (list int) int) accessibility; general GroundCaptureFactorization remains open.
- [Cycle169 構造的辞書証明書の通常継続](2026-11-13-cycle169-certificate-persistence.md)
- [Cycle169 選択された辞書節点](2026-11-13-cycle169-selected-evidence.md)
- [Cycle169 有限局所coverage](2026-11-13-cycle169-finite-coverage.md)
- [Cycle169 実際のShared安定例](2026-11-13-cycle169-shared-stable.md)
- [Cycle169 名前付きleaf](2026-11-13-cycle169-named-leaf.md)
- [Cycle169 coverage阻害](2026-11-13-cycle169-named-coverage-gap.md)
- [Cycle169 名前付き混合木](2026-11-13-cycle169-named-tree.md)
- [Cycle169 名前付き証明書の通常継続](2026-11-13-cycle169-named-persistence.md)
- [Cycle169 有限journalの子accessibility](2026-11-13-cycle169-journal-accessibility.md)
- [Cycle169 ground productionへの次の橋](2026-11-13-cycle169-next-ground.md)

- [Ground capture readback: recovery, source syntax, and record mass](2026-11-14-ground-capture-readback.md) — Actual missing-root recovery produces finite endpoint forests; source-key-preserving closed reification, record/variant projection inversion, exact checker mass, and reachable-only factorization reduction. General ground-root Acc remains conditional.

- [Cycle170 local coverage and bounded assembly](2026-11-13-cycle170-local-assembly.md) — Draft auxiliary proof progress.

- [Cycle170 next observation bridge](2026-11-13-cycle170-next-observation-bridge.md) — Draft; physical snapshot and semantic source readback obligations.
- [Ground capture assembly after full-report readback (2026-11-14)](2026-11-14-ground-capture-assembly.md) — actual fallback readbacks, simultaneous source labels, normalized descent; general Acc remains conditional.

- [Cycle171 recursive named-spine coverage](2026-11-13-cycle171-spine-coverage.md) — Draft: recursive certificate and ordinary transport.
- [Actual-inspection B4 boundary and fixed-hole phases](2026-11-14-actual-boundary-hole-phases.md) — Six operational V5 transfers, ground progress/terminal existence, source-indexed root readback, snapshot enumeration and conditional phase Acc; general unknown-hole readback remains open.
- [Actual-inspection boundary agreement](2026-11-14-actual-boundary-agreement.md) — Draft owner-decision audit; known-head missing-provenance deferral needs a decision before defining an agreed local boundary. No new boundary or bridge theorem is claimed.
- [Actual boundary agreement with provenance parameters](2026-11-14-actual-boundary-agreement-parameters.md) — Both local policies, six V5 transfers, policy-scoped generated children, conditional execution/where accessibility, and model-preserving recovery repair; semantic completeness and general provenance remain open.

- [Cycle172: conservative checker exactness](2026-11-13-cycle172-checker-exact.md) — exact physical-slot certificate, not language completeness.
- [Cycle172: nested input discovery](2026-11-13-cycle172-nested-input-discovery.md) — actual finished inspection yields finite unary input certificate.
- [Cycle173 actual-inspection evidence and ground composition](2026-11-13-cycle173-actual-evidence.md)
- Cycle173 actual ground witness, concrete branching run and selected-edge schema: `2026-11-13-cycle173-actual-evidence.md` (conditional dictionary bridges; not full B4).

- [Explicit centers at the actual-inspection boundary](2026-11-14-centered-actual-boundary.md) — Center ledger, model equations, centered transition kernel, six V5 structural fields, and conditional compatibility/K2 bridges; full simulation and trigger execution remain open.

- [Centered point-source bridges](2026-11-14-centered-point-bridges.md) — Exact initial agreement, a reachable ground counterexample to literal erasure with a matching raw execution, and selected inspection guards; unrestricted simulation and full installation availability remain open.

- [Direct centered ground-root accessibility](2026-11-14-centered-direct-accessibility.md) — Unrestricted centered Step accessibility from ground point roots, actual terminal executions, six structural V5 transfers, namespace/nested-use invariants, and conditional selected-plan/where bridges; full guard availability and the P/W trace remain open.
- [2026-11-14 Centered ground composition](2026-11-14-centered-ground-composition.md) — ten V5 fields, a reachable selection/installation obstruction, general center model extension, and conditional P/W ledger rejection; source execution remains open.

- [Centered administrative ground composition](2026-11-14-centered-administrative-composition.md) — merge-aware Local, eleven unconditional V5 fields, all-state where accessibility, fixed-snapshot reordering, and explicit production/final-observation residuals.

- [Centered production and terminal observation limits](2026-11-14-centered-terminal-production.md) — persistent packet commitment, exact selected-frame completion residual, same-center merge availability, and an actual ground terminal fork refuting full primitive-observation confluence; the two V5 fields remain open.

- [Centered completion and registered terminal confluence](2026-11-14-centered-completion-registered-confluence.md) — initial Joint/value-support proofs, exact generated/unregistered Local split, and actual inhabited terminal executions refuting literal Local confluence at a generated root; semantic child inputs agree and general production remains open.

- [Centered final Local agreement: fixed choice](2026-11-14-centered-final-local-agreement.md) — exact exit-choice normalization, packet-free order residual, concrete unequal exit predicates under reordered registries, and reachable packet-free Joint; fixed-executor order remains open.

- [Centered canonical executor](2026-11-14-centered-canonical-executor.md) — invariant registry representative, actual packet-free trace transport, packet/center/emitter rebasing, and an original-registry executor retaining eleven bridges; canonical order remains conditional on exit lifting or concrete permutation simulation.

- [Centered reachable permutation: correspondence and installation obligation](2026-11-14-centered-reachable-permutation.md) — concrete coherent packet pairing, reachable packet-free initialization, administrative/refresh/merge transport, trusted ledgers and value support; full installation transport and final Local agreement remain open.

- [Centered permutation simulation and canonical local order](2026-11-14-centered-permutation-simulation.md) — complete reversible installation transport, coherent table extension, fixed-target Local correspondence, and unconditional canonical executor order; V5 composition has only evidenceNode and generatedChildren as inputs.

- [Centered completion: reachable alias-class obstruction](2026-11-14-centered-completion-alias-obstruction.md) — actual inhabited ground installation/merge trace with merge-closed G′ selection and impossible Joint; stability and the general generatedChildren field remain open.

- [Centered class-wide applicability and the unchanged installation guard](2026-11-14-centered-class-local.md) — G″ filters candidates by joint alias-class requests and retains twelve V5 fields; the earlier snapshot enables equality feedback, and a new reachable feasible class selection is blocked by the frozen per-occurrence uniqueness guard. Stable child production remains conditional.

- [Centered output conflicts: head selection, failed equations, and V5](2026-11-14-centered-output-conflict.md) — corrects G″'s output-based candidate filtering, locates installation consistency gates and the missing error contract, distinguishes the nonstable fixture from its unclassified stable extension, and proposes an additive head/effect split with field-by-field proof impact.

- [Centered head choice and post-choice output errors: V6](2026-11-14-centered-head-output-v6.md) — head-only candidates, retained alias-class requests, covered post-choice output conflicts, V6 local laws and seven structural/local bridge analogues; complete effect interpretation, installation and V6 composition remain open.

- [Centered head-only installation and class effects](2026-11-14-centered-head-step.md) — successor Step and live class-effect ledger, V6 installation agreement, model restriction, stable closure, unrestricted ground-point progress and terminal traces, preserved output coverage and all-state local child accessibility; schema/default, feedback, merge-error and final composition obligations remain.

- [Centered V6 availability and canonical execution](2026-11-14-centered-head-availability-order.md) — complete head-step/effect-ledger permutation simulation and unconditional V6 canonical executor order, execution and exactness; selected availability reduced to explicit extension obligations, a source-formed defaults gap and positional schema interface, and the empty-model conflict limitation.

- [Centered V6: stable selection without child materialization](2026-11-14-centered-head-materialization-obstruction.md) — checked inhabited ground InitialSource with V6 selection, positive chosen effects, and stability, but no enabled installation or generated child; constructor-interpretation coverage is absent from the source contract.
