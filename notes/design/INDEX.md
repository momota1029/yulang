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
