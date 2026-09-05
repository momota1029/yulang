# 現在のタスク: yu-syntax parser構築の継続とgrammar/CST正規化サイトの起票

更新: 2026-09-06（Item emission-ownership frontier amendmentのN0a–N0b完了、N0cは既存grammar test 3件でblock）→
2026-09-02（`syntax-reference/`サイト完成→standalone `role`宣言10 gate完走→
standalone `act`宣言11 gate完走に続き、standalone `enum`宣言addendumの12 gate実装も完了）→
2026-08-29（standalone `error`宣言 Gate 6完了、Gate 7へ→Gate 7〜10も完了、10 gate完走→
standalone `for`文も全10 gate完走→Act-derives attachment addendumも両gate完走→
Type-attached `impl` addendumも全6 gate完走）

このファイルは、着手中または直ちに着手できる作業だけを置く。完了履歴はGit、設計判断は
`notes/design/`が正本。yulang3branchでは`tasks/`・`notes/progress/`を一旦削除してまっさらに
したため、このファイルが最初の再作成。

## 現在地

`crates/yu-syntax`はchasaベースのrecursive-descent parserとして、2026-08-20の
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`を正本に構築中。

- 2026-09-05: fenced current-Itemの旧N0候補は、physical prefix/carrierを保持した
  `Item`と既存direct grammarの破壊的leading/payload移送が両立しないため、統合前の
  specification/regression reviewで不採用となった。ユーザ承認済み
  `2026-09-05-item-emission-ownership-frontier-amendment.md`がこれを置換する。
  `Item`内の唯一のmutable値は`first_unemitted_leading: usize`だけであり、carrierの
  active範囲は保存せず毎回これから導出する。N0aは完了: atomic `Item::finish`、sealed
  physical ownership、`LeadingView`/借用`PayloadView`、central phased emission、Ruleの
  partial separatorとcarrier/boundary/payload-owning siteの恒久移行を実施した。ordinary
  prefix-free whole-leading compatibility operationは不要となり、そのcallerはzeroである。
  terminal adapterはopen `YmYulangCodeCell`下でaccepted body-leadingだけをemitし、
  Yumarkへはunchanged pending factsだけを返す。layoutは`Item` 104→112 bytes（許可済み
  frontier一つ）、`LeadingTrivia` 16→16 bytes。N0a focused controls（prefix placement、
  partial→remaining→payload、Rule repeated newline、terminal close/transition/EOF、
  accepted construction failure）はgreen。N0b inventoryも完了: compatibility caller、`with_fragments`、raw Item
  leading/payload mutation、detached Item-owned emitter、manual fragment walkerはいずれもzero。
  `emit_leading_trivia`の42 call / 15 filesはopaque ordinary `LeadingTrivia`だけを受け、
  physical prefix/carrierを表現できないためN0b対象ではない。したがってN0bはmigration batch
  なしで完了した。既知L5a failure
  `decimal_integer_core_keeps_its_direct_tail_chain`も、ordinary fixed ownerが誤ってL5a
  `*_with` ownerへ入ったことを原因として修復済み。ordinaryは既存scanner/recovery ownerへ、
  L5aはcomplete-Item/`Deferred` ownerへ分岐する。N0c full candidateはさらに`if` conditionの
  旧leading-clearをfrontier consumeへ置換してdirect-rewrite群をgreenにしたが、full
  `cargo test -p yu-syntax`は独立した旧`grammar/`の3 testで失敗した（903 passed, 3 failed,
  2 ignored）。失敗は`grammar::declaration::companion::tests::gate3_isolated_companion_form_recovery_and_state_table`、
  `grammar::declaration::tests::struct_named_field_sequence_owns_leading_and_repeated_empty_comma_slots`、
  `grammar::expression::tests::if_and_braced_mandatory_rejections_restore_error_sink`。現行direct-rewrite
  diffとは独立であり、N0c full certificationはこの既存grammar failuresの原因分離・修復または承認済み隔離までblock。
- tuple・演算子CST・colon application・if/elsif/else・brace statement block・pattern文法・
  case/catch・list/record pattern・call/field/path/ML-application・generic-expression
  WithBodyTail・canonical Statementのbinding/use拡張・`mod`宣言、が実装・push済み。
- standalone `TypeExpression`文法(pattern.rsと同じ立ち位置の独立grammar、`OperatorTable`
  非依存)が着地し、core grammarに加えて5つのexotic primary形式
  ——named record型・forall型・effect row型・多相variant型・bracket row grammar——
  全部Authoritative(ユーザ承認済み)。
- `Pattern : TypeExpression`型注釈wiring(最初のuse-site)がAuthoritative設計どおり実装・
  push済み。実装レビュー中に発覚したTypeExpression共有malformed recovery scannerの
  newline境界バグを発端に、`TMN-B/P/C/S`(newline owner policy)追補と、その実装の
  owner-boundary-safety配線漏れ(3巡連続で発見)を根本解決する`positional fence`追補
  (`ParseLocal`-scoped ambient state、bool手渡し方式を完全に置換)を設計・実装・多重レビュー
  済み。全12 implementation gate完走、390 tests green。
- 多相variant型は設計10巡・実装7巡を要した。教訓は
  `/home/momota1029/.claude/projects/-home-momota1029-rust-yulang/memory/feedback-two-level-judge-needs-shared-driver.md`
  に記録済み(二層judgeはAST/direct-CST両pathを別々に手書きせず、最初から共有driver+薄い
  adapterで書く)。
- `StructDeclaration`/`TypeDeclaration`共有の`derives`clause attachment文法(DRV-G/J/T/R、
  9 gate)がAuthoritative設計どおり実装・push済み。Gate 1a(neutral TypeExpression episode
  infrastructure)は後続addendumからも再利用可能な形で切り出した。Gate 8(実dispatch
  promotion)でCatch-inline文脈のambient newline所有権バグを発見・修正。
- standalone `impl`宣言shell文法(IMD-G/J/T/R、9 gate)がAuthoritative設計どおり実装・
  push済み。derivesのGate 1aに依存。Gate 6(recovery matrix)で4件、Gate 7
  (state-restoration matrix)で2件、実バグを発見・修正(いずれもisolated adapter局所、
  共有TypeExpression episode機構自体は無傷)。Type-attached `impl`・`with:` companion・
  Type colon/brace role-like body・Impl-specific `via`は別addendumへ明示的にdefer。
- standalone `cast`宣言文法(CAST-G/J/T/R、13 gate計画)がAuthoritative化済み(2026-08-27)、
  同日中に全13 gate(1・2・3a-i/ii/iii・3b・4a/4b・5・6・7・8・9)を実装・push完了、511
  tests green。yulang2の`cast(x: from_ty): to_ty = body`構文を土台に設計。設計レビューは
  11巡を要した(derives 5巡・impl-shell 3巡より大幅に多い)——CastのPattern-slot recovery
  がPattern annotation・nested delimiter・arm-sequence newline authorityと絡む部分が
  難所で、round 4〜7は既知residualの正確な境界線を閉じた表からcondition-based記述へ
  転換する過程、round 8〜10はGate 3の実装契約(shared driver・outer_stops伝播範囲)の
  精密化だった。実装でもGate 3bが7回の委譲(Terra 5回連続非収束→Sol xhighへエスカレーション)
  を要した最難関gateで、`cast((x @): B;`のようなnested Parenthesized回復後にCast自身の
  target colonがPattern本体の型注釈へ誤飲込まれる本質的な合成バグを発見・解決
  (`PatternMandatorySlotPolicy`に`recovered_primary_tail_stops`フィールドを追加)。
  副産物でPattern本体の既存バグ(`ParenthesizedPattern`のAST/direct不一致、`c852d878`
  まで遡る既存gap)も発見し、Gate 3a-iiで修正。Gate 4aでBinding-style body layout
  decisionを`classify_binding_style_body_layout`/`parse_binding_style_body`/
  `commit_binding_style_body`として中立化、derives/implに続く3例目の共有infra切り出し。
  Gate 8(atomic dispatch promotion)は`recognize_statement_intro`のImpl後/Binding前へ
  挿入、既存non-Cast優先順位・fixtureは無傷。Cast-specific `via`・rule登録・暗黙変換適用・
  expected-type境界処理・coherence・HIR/resolver/inference/formatterは明示的にscope外
  (Gate 9でworkspace全体grepにより未実装を確認済み)。既知residual(caller boundary hidden
  behind a missing Cast-contained Pattern/TypeExpression delimiter、four-condition
  predicate)はGate 8/9で6件のrepresentative fixtureとしてcharacterize済み・未解決のまま
  残す方針(closed tableではなくcondition-based)。
- standalone `role`宣言shell文法(RLD-G/J/T/R、10 gate計画)がAuthoritative設計どおり
  実装完了。Gate 1のvocabularyからGate 8のpre-promotion state matrix、Gate 9のType後/
  Impl前atomic dispatch promotion、Gate 10のfinal contextual-word/scope gateまで完走し、
  520 tests green。role bodyはordinary canonical Statement compositionであり、
  RoleSignature / member semantics / inheritance / where / via / HIR / resolver / inference /
  formatterは未実装をworkspace-wide grepで確認済み。Y2 role methodのdotted Binding targetが
  Patternの未実装DotField continuationへ依存するgapはGate 5で発見し、Role内へ推測実装せず
  plain identifier worked exampleへ訂正したうえでPattern別addendumへdeferした。
- standalone `act`宣言shell文法(ACT-G/J/T/R、11 gate計画)がAuthoritative設計どおり
  実装完了。Gate 1のvocabularyからGate 7のACT-R recovery matrix、Gate 8のbody
  composition matrix、Gate 9のstate-restoration matrix、Gate 10のCast後/Binding前
  atomic dispatch promotion、Gate 11のfinal contextual-word/scope gateまで完走し、
  530 tests green。roleと違い、Actは三段slot(Head→Source→BodyIntroducer)の
  no-cascade recoveryと、`my act = 1`(Binding target)対`my act A = B`(Act intro)を
  raw head candidate lookaheadで区別する非対称`my`衝突規則、および明示tail-nothing時の
  implicit boundary bodyless success(Missing化しない)という3点でroleより複雑だった。
  設計レビューは誤りゼロで着地(role Gate 10の教訓——contextual-word例を検証せず
  書いた自分自身の誤り——を実装側で確実に踏襲)。host act tier・operation
  registration・derives attachment拡張・`with:` companionは別addendumへ明示的にdefer。
- standalone `enum`宣言文法(ENUM-G/J/T/R、12 gate計画)がAuthoritative設計どおり
  実装完了。Gate 1のvocabularyからGate 5の4形態(brace/colon/equals-inline/
  equals-indented)共通variant-sequence driver、Gate 6のvariant payload driver
  (Unit/From/Named/Tuple/Positional、Struct field-loop抽出込み)、Gate 9の
  ENUM-R recovery matrix、Gate 11のStruct後/Enum/Mod前atomic dispatch
  promotion、Gate 12のfinal contextual-word/scope gateまで完走し、542 tests
  green。role/actと違い、headはfull TypeExpressionでなくoracle通りraw Name +
  DeclarationTypeParameter list、bodyは4形態(brace/colon-indented/equals
  inline/equals-indented)、variantはUnit/from/named/tuple/positionalの5payload
  形。Gate 8で実装中に発見した実バグ(variant名直後の隣接`(`/`{`がpayload
  優先判定から漏れていた)を修正、Gate 11のatomic promotion後にderives
  clause既存Gate 9 fixtureの"`enum E derives Eq`はderivesを持たない"という
  旧前提がEnum実装完了で不成立になった(Enumが正式なderives header owner
  になったため)ことをClaudeが直接特定・修正。designレビューはoracle
  citation13箇所・worked example3件のbyte range手計算含め誤りゼロ。`error`
  宣言をvariant-sequence/payload core再利用前提でdeferred scopeへ明記済み。
- standalone `error`宣言addendum(ERROR-G/J/T/R、10 gate計画)は2026-08-28に
  Authoritative化(ユーザ承認済み、Codex gpt-5.6-sol起草・Claude Sonnet 5査読/finalize、
  Fable-5-absent substitute procedure)され、Enumのvariant-sequence/payload coreを
  Gate 5で再利用する計画。Gate 1 vocabulary scaffold(`63edb5ac`)・Gate 2 intro
  recognizer(`3eb199b4`)・Gate 3 header adapter(`3894ec98`)・Gate 4 derives
  integration(`b6b8f4d4`)・Gate 5 neutral variant owner core extraction(`0b64aaa7`、
  `VariantDeclarationOwnerSpec`/`drive_variant_declaration_sequence`をEnum/Error共有へ
  抽出)を完了。Gate 6(`6402ec00`)でisolated AST/direct-CST adapterを実装——
  `parse_error_declaration_isolated`/
  `commit_error_declaration_isolated`が新規Error固有body/variant型を作らず既存
  `EnumBody`/`EnumVariant`/`EnumVariantPayload`および`EnumVariant`/`StructField`/`FromKw`
  direct-CST node kindを再利用する。`error fs_err:`(positional variants)、`error io_err:`
  (from variant)、`my error E:`(contextual form)の3 worked exampleをbyte-exact/lossless/
  zero-recoveryかつAST/direct-CST parityで固定し、`cargo test -p yu-syntax`は546→547
  passed、0 failed。Gate 7(`142ae7a0`)でError outer roleの`ERROR-R` recovery matrix全行を
  修正し、Enumの`ENUM-R` variant/payload recovery rowsがError自身のouter roleで正しく
  importされることを確認、`emit_error_variant_item_missing`・
  `emit_error_declaration_error`・`error_body_introducer_error_retry`を追加して548 tests
  green。Gate 8(`41f95997`)はisolated adapterのfull boundary/ambient/state-restoration
  matrix(root/indented/braced/inline/catch-inline/depth-2-If ambient context、caller
  boundary、payload form、recovery role)を閉じ、実gapなしのverificationとして549 tests
  green。Gate 9(`f7d760f2`、`b5269e01`)でErrorをisolated adapterからREAL PUBLIC DISPATCHへ
  atomic promotion——Enum後/Mod・Type前の優先順位で
  shared statement-intro dispatch・direct root-loop candidate(`unreachable!()` placeholderを
  置換)・AST canonical Statement・AST root Declaration・direct-CST canonical Statementへ挿入し、
  他familyの相対順序は不変、Gate 6 adapterの不要になった`#[allow(dead_code)]`も除去した。
  全other familyのregressionなし・workspace build greenで550 tests green。Gate 10(`37f6b8b5`)は
  real public dispatch経由のfinal matrixとして、全visibility form、`my error`とBindingの衝突、
  全body/payload form、header/trailing derives、Gate 7の全malformed/recovery row、
  declaration-intro外でのordinary wordとしての`error`/`from`を確認し、実gapなしで551 tests
  green。Gate 6〜10を通じ、Codex sandboxとreview hostのrustfmt version/toolchain差による
  pre-existingな`declaration.rs`/`expression.rs`のformat driftはlogic変更と混ぜず
  `1704ba4a`/`f7d760f2`へ分離した。workspace-wide grepでyu-syntax外にError internalsの参照が
  ないことも確認済みで、HIR/resolver/inference/formatter/semantic error effectsはrole/act/enum/castと
  同じくsyntax-only scope外。Enumのvariant-sequence/payload coreを共有するstandalone `error`宣言は
  全10 gate完走、551 tests green——role(10)・act(11)・enum(12)に続く5番目の完了family
  (cast(13)は先行完了)。
- standalone `for`文addendum(FOR-G/J/T/R、10 gate計画)はClaude (Fable 5)起草、
  2026-08-29にユーザ承認済みAuthoritative化(`1df4abbc`)。既存Pattern/OperatorChain/
  statement-block machineryを再利用し、新規sub-parserなしで`for [label] pattern in iterable:
  body`/`for [label] pattern in iterable { body }`を扱う。Gate 1 vocabulary scaffold
  (`3bbcddcc`)で`ForStatement`/`ForLabel`/`ForIterable`/`InKw`、AST・Statement/Declaration
  variant・recovery role・`StopKind::In`を追加(551 tests、Gate 0とbyte-identical)。Gate 2
  (`a868ce3b`)はisolated intro recognizer——exact `for`のみを受理し`forall`/`fork`/`format`
  を拒否、visibility formなし、`for_base`をcapture(552 tests)。Gate 3(`8fb8373c`)はcase/catch
  と共通の`probe_apostrophe_sigil_word`を抽出してoptional apostrophe-sigil labelを扱い、
  For固有の`in` lookahead rejectionにより`'x in xs`の`x`を通常Patternへ残し、`'[`/`'{`/
  `~"`との非衝突も固定(553 tests)。Gate 4(`a5516fc8`)は既存word-stop 3箇所へ
  `StopKind::In`をpure additionで配線し、fresh-primaryがColon/LeftBrace/Inで止まるmandatory
  Pattern slotを実装(554 tests)。Gate 5(`00787903`)はisolated `in` keyword judgeと
  OperatorChain再利用のiterable slotを実装、catch scrutinee precedentと同じ
  Colon/LeftBrace scoped stop frameを用い、missing-in+missing-iterableはちょうど1件の
  Missing InKeywordへcollapse(555 tests)。Gate 6(`75f15734`)は4 body form(inline
  OperatorChain/indented/braced delegated-to-Mod pattern/labelled-indented)のadapterを実装、
  shared colon-layout primitiveを`ArmBodyLayout`から`IntroducedBodyLayout`へpure renameし、
  if/case/catch/withでzero behavior changeを確認(556 tests)。Gate 7(`31aa766c`)は既存
  `parse_for_statement_isolated`/`commit_for_statement_isolated` composerでFOR-R recovery
  matrixを閉じ、missing iterable後のBodyIntroducer cascade抑止とmalformed iterable retryの
  AST/direct-CST一致という実gap 2件を修正(557 tests)。Gate 8(`19f785af`)はroot/indented/
  braced/inline/depth-2-If companion ambient contextの全boundary、normal/recovery/rollback
  pathを検証し、実gapなし(558 tests)。Gate 9(`bd59d870`)はAct後/Binding前の優先順位で
  shared statement-intro dispatch・direct root loop・AST canonical Statement/root
  Declaration・direct-CST canonical Statementへreal public dispatchとしてatomic promotion、
  他familyの相対順序不変・workspace build greenを確認し、inline/labelled-indented/braced/
  colon-inlineの4 worked exampleを追加(559 tests)。Gate 10(`81003c7a`)はreal public
  dispatch経由でlabel collision・全body form・if/role/act body内を含むnested For・root sibling
  non-consumption・全FOR-R malformed form・public/direct-CST parity・ForKwとForallTypeの共有に
  よる非汚染・grammar position外での`for`/`in`のordinary wordを確認、実gapなしで560 tests
  green。Gate 1/4/6〜10を通じ、Codex sandboxとreview hostのrustfmt version/toolchain差による
  pre-existing format driftはbehavioral changeと混ぜず`8d3026f5`/`3193cf94`へ分離した。
  workspace-wide grepでyu-syntax外にFor-statement internalsの参照がないことも確認済みで、
  loop execution semantics/HIR/resolver/inferenceはsyntax-only scope外。standalone `for`文は
  全10 gate完走、560 tests green——role(10)・act(11)・enum(12)・cast(13)・error(10)に続く
  6番目の完了declaration/statement family。
- Act-derives attachment addendum(ACTDRV)は、Claude (Fable 5)起草・2026-08-29ユーザ承認済み
  Authoritative化(`261f3e9f`)された共有`DerivesClause` driverの小規模拡張。Fable 5は
  yulang2 oracleを照合し、「Y2にAct-derivesのprecedentはない」という初期前提を訂正——
  `act_decl.rs:29-38`にliveなname-adjacent header derives pathがあり、scanner-stopにshadow
  されたpost-source pathも構造上は存在した。Gate 1(`d84bd3df`)はdriver側だけにAct owner・
  header/trailing classifier・tail/spec・episode-stopを追加し、560 testsで不変。Gate 2
  (`713d383e`)はAct実parserへHead後・actual Source後(ともに既存`Header`)・braced close後
  (新規`Trailing`)の3 attachment point、`ActDeclaration.derives`、必要なepisode stopと
  braced-close completeness accessorを配線し、fresh-primary local ownershipも維持した。3 worked
  exampleとACTDRV-R recovery tableをreal `parse_file`で固定し、562 tests green・workspace build
  greenで両gate完走。これは既存shared mechanismへの第5 owner追加であり、standalone
  declaration/statement familyの追加ではない。
- Type-attached `impl` form addendum(TAI、`type Name impl ...`)は、Fable 5がセッション途中で
  rate limitに達したためFable-5-absent substitute procedureによりCodex gpt-5.6-sol (xhigh)が
  起草し、Claude Sonnet 5が査読・finalizeした設計(`8268a182`)を実装。`TypeDeclarationForm`
  の第3 form `AttachedImpl`として、standalone Impl全体ではなく`impl` keyword後の
  head/description/bodyだけを既存tailと共有し、wrapper nodeなしでflat emitする。Gate 1
  (`7d4291ba`)はinert vocabulary scaffold、Gate 2(`4b36550c`)はstandalone Implの
  post-keyword tailをowner-parameterized shared core
  (`ImplTailOwnerSpec`/`parse_impl_tail_ast`/`commit_impl_tail`)へ純粋抽出して既存Implを
  byte-identicalに維持、Gate 3(`f4bcf125`)はpost-header decisionと
  `DerivesOwnerTailClassifier::TypeHeaderAttachedImpl`/tail owner specをproduction未接続で
  分離、Gate 4(`5202b438`)はType-owned AST/direct-CST adapterでbodyless・description+
  bodyless・brace・colon-inline・colon-indentedの5形をbyte-exactかつnested
  `ImplDeclaration`なしで固定。Gate 5(`660eab42`)はTAI-R recovery/state matrixを閉じ、共有tail
  coreのerrors checkpoint rollback欠落とmissing-Head時にMissing recordを出さない実gap 2件を
  修正（standalone Implの18関連testは不変確認）。Gate 6(`2d04232a`)はHeader derives後、
  Nominal/Equality前のreal Type AST/direct dispatchへatomic promotionし、production TypeHeader
  RoleRefもscoped classifierへ切替——deferredとして両方でpinされていたblocking sourceを
  standalone Impl Gate 9のnegative loopと別scope-gate testの2箇所から新しいpositive
  production-path testへ移し、`with:`/Type colon-brace role-like bodyのdeferred rowsは保持した。
  dispatch slotはHeader derives → AttachedImpl → (future With) → Equality → (future role-like body)
  → Nominal/recoveryとして将来addendum用に予約。568 tests green・zero regressions・workspace
  build green、new SyntaxKind・attached trailing derives・`with:`/role-like body・`via`・
  semantics/HIR/resolver/formatterの追加なし。なお本gateでは56,000行超の`declaration.rs`に新testを
  含めるとsandboxのrustfmtが12.4GB allocation failureでcrashする既知のfile-size limitationを
  patch splitで再現確認したため、当該commitだけはClaudeが新規codeのformatを目視検証した
  (`cargo check`/testはclean)。新grammar surfaceを持つため2 gateのACTDRVより大きいが、既存Type/
  Impl machineryを再利用し新しいintro/root-nested dispatchやCST vocabularyを増やさない、
  declaration family未満のmedium-sized addendumとして全6 gate完走。
- `declaration.rs` module split計画
  (`notes/design/2026-08-30-declaration-module-split-plan.md`、Status: Authoritative、
  2026-08-30ユーザ承認済み)は全17 phaseを完走し、完了・close out。P1〜P14のうち
  P7・P10・P13をそれぞれP7-1/P7-2・P10-1/P10-2・P13-1/P13-2へ分割し、計画外の
  follow-up 1 commitを含む全18 commitで実施した。開始時の`declaration.rs`は56,500行。
  commit `dfc213f9`でtest module 33,683行を`declaration/tests.rs`へ抽出した時点で、
  production-code bodyは22,812行だった。最終的に`declaration.rs`は、module doc comment、
  mod declarations、private glob imports、consolidated facade re-export block、shared vocabulary
  types、root dispatch entrypointsを担う1,519行のhubとなり、実装を
  `crates/yu-syntax/src/grammar/declaration/`以下の16 child module——
  `binding_style_body.rs`、`derives.rs`、`for_statement.rs`、`use_decl.rs`、
  `operator_header.rs`、`cast_decl.rs`、`role_decl.rs`、`act_decl.rs`、`impl_decl.rs`、
  `variant_core.rs`、`enum_decl.rs`、`error_decl.rs`、`type_decl.rs`、`struct_decl.rs`、
  `mod_decl.rs`、`binding_decl.rs`——へ分割した。これに加えて、先に抽出した
  `declaration/tests.rs` 33,683行がある。設計はhub-and-spoke + bidirectional glob meshで、
  各childが`use super::*;`、hubがchildごとのprivate `use child::*;`を持ち、
  `expression.rs`など`declaration.rs`外から参照されるitemにはnamed facade re-export blockを
  集約した。P14 cross-checkで見つかったEnum/Error専用のstray helper 6 itemは、計画外の
  follow-up commit `159c4976`で`variant_core.rs`へ移動。最終P14 commitは`a4b98643`で、
  `origin/yulang3`へ`159c4976..a4b98643`をpush済み。全phase boundaryと最終時点で568 tests
  green、全期間を通じてbehavior changeなし。split前の巨大fileで発生していたrustfmtの
  12.4GB allocation failureは完全に解消し、残るgrammar fileに同規模へ近づくものはない。

## 既知の未修正バグ

なし。旧「多相variant複数tag+active newline境界バグ」(`classify_tag_boundary`が
`active_stop_set(i).contains(StopKind::Newline)`を無条件にownerへのyield理由として
扱ってた件)は、commit `f4332308`(2026-08-26)で修正・回帰test
(`qualifying_tag_newline_remains_local_under_an_active_newline_stop`)化済み。

## 確定メモ: Yumark 内 Yulang code cell (2026-09-04)

ユーザ決定: `yulang` fence 本文はraw textだけでなく構文解析・色付け・doctest実行対象として認識する。各 fence は
**独立した code cell**であり、他の fence が作ったbinding / execution stateを見ない。一方でテスト実行時に渡された
外部環境は参照できる。`our`を含むroot-level declarationはcell内で許すため、ordinary `{ ... }` blockではなく
root-style statement entryを使う。syntax phase自身は実行せず、後段doctest runnerが各cellを独立に評価する。

outer Yumark frameはquote prefix・fence opener / close・source offsetをstreamingに所有し続け、nested Yulang parserは
fence bodyだけを読む。non-Yulang fenceはrawのまま流し、将来のlanguage adapterを妨げない。現行
`2026-09-01-doc-comment-yumark-addendum.md`はparsed-Yulang fenceを明示的scope外にしており、現実装も
`YmCodeFenceText`へraw textを置くだけである。実装前にこのdecisionをscopeとgateへ展開する後続
Authoritative addendumを作ること。command/apply argument用の既存embedded-Yulang delimiter bridgeとは別責務であり、
fenceのouter delimiter / quote streaming ownershipを崩したりpublic parser再帰で本文を再parseしたりしない。

2026-09-05: 後続addendum
`notes/design/2026-09-05-yumark-parsed-yulang-fence-addendum.md`は、M3
compiler/recovery・specification・regression・performance査読とscoped deltaを終え、user approvalで`Authoritative`。
先頭info atomのexact `yulang`選択、`&str`を保つborrowed fence boundary、quoted multiline lexical
itemのcurrent-item fragment carrier、outer quoteへ戻すdequote/greater-depth規則、direct
`YmYulangCodeCell`、Gate 4--9の依存順を定めた。Gate 1 authority closureとinert Gate 2は完了。
Gate 2はdirect private vocabulary・pure selector/physical-line judge・coordinate-preserving pending
boundary・item-wide move-only fragment carrierだけを追加し、legacy Yumark/session/production dispatchは
未接続のまま維持した。fragment carrierはquoted multiline lexical itemの全leading-trivia/payload text
partsを一つのordered split列で覆い、通常scannerはcarrierを作らない。rareなfence close/transition facts
だけをbox化し、ordinary Payload sizeを既存OperatorToken envelope内に保つ。focused direct tests、
`cargo check -p yu-syntax`、fmt/diff checkはgreenで、static allocation reviewは計測不要と結論した。
isolated Gate 3 cell-construction witnessも完了した。一つのcaller-owned builderでroot-style
`Statement*`を`YmYulangCodeCell`に構成し、borrowed close / transition / EOF boundaryを
leading trivia・fragment carrierごと未消費で返すtest-only witnessを固定した。accepted segmented
identifierは同じcellの`Statement > IdentifierExpression`でordinary textと`YmQuotePrefix`を物理順に
emitし、その直後のborrowed closeも返す。lexer、legacy/public dispatch、session、operator state、
production Yumarkは未接続である。full cell closureはrewrite Gates 4--7以後、Yumark integrationは
Gate 8、production cutoverはGate 9まで待つ。

2026-09-05: user approvalとM2 compiler/recovery・specification reviewにより
`2026-09-05-yumark-fenced-block-comment-lexer-amendment.md`をAuthoritativeとし、isolated fenced
`BlockComment` lexical ownerも完了した。ordinary scannerは変えず、immediate
`part_origin`、`FenceBoundary`、current-Itemが所有するlazy split accumulatorだけを渡し、whole-Itemの
`item_origin`と全constituent lengthでcarrierを一回だけfinishする。equivalent prefixはstrict close
判定後にだけsplitとして記録・消費し、close / transition / EOF lineはuntouched boundaryとして返す。
opener後はtotal、`None`/later rollbackに外部accumulatorをまたがせない。nested comment depth、prior trivia
envelope、CRLF/UTF-8、`/x` non-matchもfocused controlに含む。lexer/public/legacy/Yumark production bridgeは
scope外である。次のmultiline lexical ownerであるstring/rule literalは、user-approved
`notes/design/2026-09-05-direct-literal-cone-addendum.md`がnormal/heredoc String、`%` interpolation、
`rule {}`、`~"..."`、Pattern route、typed recovery、one-current-Item fence handoffをAuthoritative化した。
isolated L0はpublic vocabulary/fragmented emitterだけを完了し、L1はliteral lexical Item scannerと
fence transition primitive、L2はnormal/heredoc text・escape・terminator・non-interpolation recovery、L3は
StringInterpolationのpercent/format/open-braceとmissing-open-brace path、L4はnormally compiled private
RuleSequenceCore witnessを完了した。L4はRuleBody/alternation/sequence/item、core atom、quantifier、capture、
field/path recovery、paren ownership、fragmented introducer openerをproduction dispatchなしで固定した。次の
authorized sliceはL5のRuleAtom string/bracketとRule call/indexである。`%{ Statement* }`はGate 6
statement/declaration construction checkpoint後のL6、complete literal/Pattern deltaはL7とjoint Gate 4--6
barrierまで完了扱いにしない。Gate 4 expression/recovery、Gate 5--7、Yumark integration/cutoverも未完である。

2026-09-05: L5 Rule `ExpressionList` の成功 child 後の fence handoff を調査した結果、complete-Item
scanner一つを braced statement/declaration まで貫通させると、header/Type/Pattern/raw probe を表す大域
request/context機構が必要になると確定した。user-approved `2026-09-05-direct-expression-successor-acquisition-
addendum.md` はこれを拒否し、L5a（closed direct Item cone と private `Deferred` frontier）→ L6a（compound
expression・canonical statement/declaration・Pattern/Type/derives/raw probe の owner-local fenced entry）→ L5b
（full Rule ExpressionList）の順序をAuthoritative化した。fenced pathは消費だけでなくphysical lineを越える
lookahead前にもjudgeし、child callごとにsuffix pointer/length差でimmediate originを同期する。fence、cursor、
source、callback、contextをRecover/Rowan/Item/persistent frameへ置かず、close/transition Itemとleading trivia/
fragment carrierはunchanged handoffする。L5 repairのisolated WIPはN0a Item ownership migrationと
同じdirect-rewrite commitに載るが、L5/L6/L7/public integrationの完了を意味しない。L5aの
frontier ledgerとclosed-cone proof、L5/L6/L7/public integrationは未完である。

2026-09-05: L5a seam の実装調査で、ordinary identifier/operator 前の accepted Yumark prefix が既存
`Item` constituent を持てず、`ForeignSplit` validation と `Whitespace` 偽装禁止が両立しないこと、さらに
operator/contextual/layout raw probe が fence 後の outer source を読むことを確認した。user-approved
`notes/design/2026-09-05-fenced-current-item-normalization-addendum.md` は旧 owner-local L5a/L6a/L5b
mechanism をその範囲だけ supersede し、private `TriviaKind::YmQuotePrefix` physical part、one direct
ordinary/fenced current-Item body、pure fenced source observation、transient line-entry handoff、有限の
temporary `Deferred` frontier ledger をAuthoritative化した。architecture/compiler-recovery/specification
review と scoped delta review は全てclosed。N0a（physical-prefix representation、sealed
grammar-inert LeadingTrivia predicates、fragment-aware accepted-Item emission）は完了し、scanner/grammar/
public reachabilityを変えていない。次はN0b detached-owner inventory、その後N0c certificationである。N1--N3、
L5/L6/L7/public integrationは未完である。

## 次の候補(優先順位未確定、着手時に選ぶ)

2026-08-30: 次sliceとしてshared declaration companion `with:`を選定した。
`notes/design/2026-08-30-declaration-companion-with-addendum.md`へ、Struct/Type/Enum/Error/Actの
5 owner、companion-only Derives item、owner/episode handoff、typed recovery、static-specialized
sequence core、10 gateを記録した。独立compiler/spec/performance査読のblockerを反映し、
2026-08-30にユーザ承認を受けて`Status: Authoritative`へ移行。Gate 1(`77be1bdd`)は、2つの
SyntaxKind、companion AST/recovery/ConstructRole vocabulary、5 ownerのinert field、unreachable
`StructBody::CompanionIntroduced`を追加した。recognizer/dispatch/StopKind/production reachabilityは
変更せず、compiler/spec/regressionの独立査読は全て承認可、568 tests green。現在のactive stepは
Gate 2。最初のzero-sized static specialization案はsemantic/compiler/spec/regression上は閉じたが、
CPU-pinned・order-balanced 24-round計測で10k indented AST/directのpeak RSS one-sided 95% lower
boundがそれぞれ`+8 KiB`/`+10 KiB`となり、§§9/14のzero-effect rollback条件を越えたため、
uncommitted codeをGate 1 HEADへbyte-identicalにrollbackした。生データと判定は
`notes/progress/daily/2026-08-30.md`および
`notes/progress/evidence/2026-08-30-gate2-pinned-measured.tsv`に記録済み。Gate 2は未完了、Gate 3は
未認可。duplicated thin loop実装査読で、既存ordinary `statement_sequence_error_retry`自体が
comment内のdelimiter/identifierを誤認するraw-character scannerであり、comment-atomic共有scanner
とordinary recovery byte-identical条件が両立しないfalse premiseを発見した。ユーザは2026-08-30に
option 1——この既存ordinary comment recoveryだけをowning canonical responsibilityで修正し、
ordinary/companion共通のsink-free scannerへ集約する——を承認。正本は
`notes/design/2026-08-30-declaration-companion-gate2-recovery-amendment.md`。duplicated thin-loop案は、
共有scanner・既存separator/boundary judge再利用、full state/CST/recovery matrix、独立
compiler/spec/regression/performance査読まで閉じ、581 tests greenとなった。しかしCPU-pinned・
order-balanced 24-round最終計測では、8つのordinary caseすべてでwall/RSSのone-sided 95% lower
boundがzero-effect閾値を越えた（wall LB `+0.055%`〜`+2.819%`、RSS LB `+12`〜`+140 KiB`）。
そのため3 code fileを`2bdaeba0`へbyte-identicalにrollbackし、192 accepted pairs、54
candidate-only samples、統計・除外ログ・driverを`notes/progress/evidence/`へ保存した。Gate 2は
未完了、Gate 3は未認可。static specializationとduplicated thin loopの両Authoritative形が性能
gateでrollback済みのため、現在のactive stepは新たな実装ではなくarchitecture re-entry。
ユーザはwhole-process zero-effectを通常hot pathのzero-added-work proofへ置換し、テスト・計測を
現行budgetへ収めるoption 1を選択した。performance/specの2査読をfindingなしで閉じ、exact clauseも
2026-08-30にユーザ承認済み。Authoritative正本は
`notes/design/2026-08-30-declaration-companion-gate2-performance-amendment.md`。現在のactive stepは
Gate 2完了後のGate 3。Gate 2はduplicated companion-only thin loopをzero-added-work proof付きで
再実装し、protected ordinary body 6件の同一性、accepted-path operation ledger、production edge不在を
独立performance/spec査読で閉じた。bounded診断は`indented_direct` 10k ×8だけをwarm-up pair 1組+
measured pair 3組、計8 process/約349秒で実施し、追加ordinary workなしを再確認。最終
`cargo test -p yu-syntax`は規定どおり1回だけで570 passed / 1 ignored。証拠は
`notes/progress/evidence/2026-08-30-gate2-semantic-work-proof.md`と同階層のraw archiveに保存した。
Gate 2は完了。Gate 3 isolated companion formも完了した。初回実装で
`expression_nud_candidate_input`がinput/ParseLocalだけをrollbackし、companion-owned `}`の
speculative ErrorSinkを漏らす既存generic defectを発見した。Gate 2のzero-added-work条件と原因修正が
衝突したためarchitecture re-entryし、ユーザは2026-08-31にoption 1——同helperへexactly one
ErrorSink checkpoint/rollback pairを追加するowning fix——を承認。Authoritative正本は
`notes/design/2026-08-31-declaration-companion-gate3-nud-sink-amendment.md`。修正はexactly 2 operations/
existing call、focused table 1組とfinal `cargo test -p yu-syntax` 1回（571 passed / 1 ignored）、独立
compiler/performance査読で閉じ、workspace suite/既定timingは行わなかった。Gate 4 companion-only
Derives item priorityも完了した。shared Derives driverをattachment metadataとneutral companion contextへ
分離し、adjacent DerivesClause runを1 companion itemへまとめ、direct CSTではStatement/attachment wrapper
なしにDerivesClauseをstreamする。standalone Statement、既存5 owner、owner production wiringは不変。
focused table 1件（1 passed / 572 filtered）とscoped format/diff check、独立compiler/spec/regression査読で
閉じ、package/workspace suiteとtimingは行わなかった。現在のactive stepはGate 5 typed episode handoffs。
Gate 5はM2の初回実装とbundled repair後、isolated variant payloadの`A @with:`が後続の`:`を二つ目の
variantとして誤回復する具体的な残存原因をfocused tableで確認した。2026-08-31にユーザは、この一点を
companion-only continuation factで閉じるための例外的な追加repair roundを明示承認した。これはGate 6以降の
owner wiringや新たな文法判断を認可せず、AST/directの一variant/no-tail/`:` retained remainderを回復する
原因修正だけを解決対象とする。再修正後は同じfocused table、scoped format/diff check、既存M2 reviewerの
delta reviewだけを行い、package suiteはgateが閉じた場合に一回だけとする。
そのcontinuation修正は二variant回復を閉じたが、同tableに新設した`A @with:`のTypeExpression range期待値が
`2..7`（malformed `@`を含む）となっていた。`@`のType Primary Error範囲`2..3`とretryされた`with`の
TypeExpression範囲`3..7`を混同した可能性だけを対象に、2026-08-31にユーザはpre-write spec auditと
expectation-only修正、同focused table一回の再実行を例外承認した。reviewがrange以外のownership/recovery
契約の揺れを示すなら修正を止め、ad hoc patchを重ねずarchitecture re-entryへ戻す。
pre-write spec auditは`A @with:`のretry TypeExpressionを`3..7`と確定し、同一helper・同一契約の
`A from @with:`にも隠れた誤期待値`7..12`（正しくは`8..12`）を発見した。2026-08-31にユーザは
このpaired assertionも同じexpectation-only例外へ含めることを明示承認した。parser codeやrecovery/CST
期待、focused table以外のtestは変更しない。
Gate 5は完了。isolated handoffだけでDerives owner tail、Act Head/Source、Type Equality、Enum/Error
equals-inline yieldをtypedに表現し、既存owner adapterはproduction-unreachableのまま維持した。隣接
`@with`のrecovered payloadは一variantとして完結し、retained `:`を二つ目のvariant回復へ流さない。
最終focused tableは1 passed / 573 filtered、`cargo test -p yu-syntax`は573 passed / 1 ignored、scoped
rustfmtとdiff checkもgreen。workspace suiteとtimingは行わなかった。Gate 6も完了。Type Header/Equality
だけをproduction ownerへwireし、Header derives→AttachedImpl→companion→EqualityとEquality RHS→trailing
Derives→companionの順序、前駆Missing recovery、outer-only Withを保った。focused tableは1 passed / 574
filtered、scoped rustfmt/diff checkと独立compiler delta reviewはgreen、package/workspace suiteとtimingは
行わなかった。Gate 7も完了。Struct Headerとactual-complete named-brace/tuple trailingだけをproduction
ownerへwireし、bare Struct・bodyless semicolon・named-indent・missing/mismatched closeの拒否を保った。
Struct companion内のCanonical Statementへ既存operator tableを渡すnarrow entrypointを追加し、focused tableは
1 passed / 575 filtered、scoped rustfmt/diff checkと独立compiler delta reviewはgreen。package/workspace suiteと
timingは行わなかった。Gate 8も完了。EnumはHeader・actual-complete brace trailing・equals-inlineのtyped tailを
singular companionへattachし、ErrorはHeader・actual-complete brace trailingだけをattach、equals-inlineの同じtailは
outer Statementへyieldする意図的な非対称を保った。Enum/Error companion内のCanonical Statementにも既存operator
tableをtable-aware wrapper経由で渡し、tableless wrapperは互換のため残した。M2 focused tableは1 passed / 576
filtered、scoped rustfmt/diff checkとcompiler/spec delta reviewはgreen。package/workspace suiteとtimingは行わなかった。
Gate 9も完了。Act Head/Sourceだけをcompanion-aware TypeExpression tailへ接続し、Header derivesの後で
companionを選ぶとSource/body判定を終端する。`act A with {} = B with {}`は最初のcompanionだけをActの
singular AST/CST fieldとして所有し、以降の`=`以下をouter Statementへ返す。actual braced close後のtrailing
derivesは意図どおり通常driverのままなので、`act A {} derives Eq with: ...`の`with`はraw RoleReferenceの
Type ML applicationでありcompanionにはならない。focused tableはAST/directのremainder・recovery・CST topologyと
owner rangeを固定し、1 passed / 577 filtered、scoped rustfmt/diff checkとcompiler/spec reviewはgreen。package/
workspace suiteとtimingは行わなかった。Gate 10も完了。public rootの最終matrixでType Header/Equality、Struct
Header/actual-close trailing、Enum Header/trailing/equals-inline、Error Header/trailing/outer-yield、Act
post-Head/post-Sourceの12 owner positionをAST・`parse_file`・direct rootで固定した。各rowはrange/remainder、
direct owner-child/WithKw、derives順序、recovery role/range/source order、public/direct recovery-node parity、
default ParseLocal stateを検証する。Error equals-inlineの`with`はError companionを作らずroot Statementの
TrailingInput Errorとして残る。`type box 'e 'a with:\n  struct self:`は正本に従い古いdeferred negativeから
Type Headerのindented canonical-Statement positiveへ移し、receiver/member semanticsを導入せず
`DeclarationCompanionIndentedBody`内のStruct declarationだけを固定した。最終packageで発見した
`act A derives Eq via ;`はGate 5のcompanion-aware Via malformed scannerがordinary owner-tailを見落とす
原因defectであり、shared `DerivesDriverSpec`へ委譲する一点修正でActのbodyless semicolonをownerへ返した。
この回復-only修正はaccepted normal path・loop・allocationを変えないため追加timingは不要とし、compiler/spec/
regression delta reviewで閉じた。focused Act fixtureとGate 10 matrixはいずれも1 passed / 579 filtered、
scoped rustfmt/diff checkはgreen、最終`cargo test -p yu-syntax`は578 passed / 2 ignored。workspace suiteは
行わなかった。Gate 10のcandidate-only public production measurementは10k braced Struct companionを8 parse/run、
fresh warm-up 1 + measured 3で記録し、kernel median 86.740094588 s、whole-process RSS median 24,484 KiBだった。
invalid 2件を含む6 process/459.18 sは8 process/10-minute budget内であり、baseline非互換のため比較/回帰率は
主張しない。証拠は`notes/progress/evidence/2026-09-01-gate10-public-companion-{measurement,raw}.md`に保存した。
shared declaration companion `with:`のGates 1–10は完了した。

2026-09-01: 次sliceとしてstandalone doc-comment declarationを選定した。ユーザはtemporary opaque bodyを
却下し、written Yumark文書仕様をsurface authorityとしてfull structured Yumark（documented commandを含む）を
採ること、block close `---`はstrictにして`---x`を本文として扱うこと、深い入れ子は人工上限なしのexplicit
Yumark frame stackで扱うことを選択した。fenceは文書仕様どおりraw textのままとし、Yulangはcommand/applyの
argument位置だけで扱う。`do`はcommandのlocal `:`/`{}` bodyと別に、そのcommand段落より後のsibling blockを
captureする。Yumark文書に未記載だったblock opener/list middle indent/link-image destination/quote-fence close/
heading/if-chainのcompletion rowsもユーザが選択した。`do`はexact sole `(do)`だけで通常Yulang argumentとのmixを
rejectするが、local Doc bodyは併用できる。`\use UseTree;`はparenthesized written formと共存し、bare
`\my f x`はYumark-local binding headとして受理する。`\my f x = expr;`と`=\n` indented expressionは式、
`\my f x:\n` indented documentはbraced Doc bodyの略記である。written oracleは
`notes/design/oracles/2026-09-01-yumark-draft.md`へfrozen copy済み。Draft正本は
`notes/design/2026-09-01-doc-comment-yumark-addendum.md`。M3設計reviewはYumark AST/CST vocabulary、typed
recovery、frame/terminator owner、Yulang boundary bridge、performance no-rescan条件を閉じ、2026-09-01にユーザ承認で
`Authoritative`化した。active gateはGate 1（inert syntax/AST/recovery vocabularyとtest-only full-state snapshot）であり、
root/canonical dispatchはGate 6まで未認可。

Gate 1の実装査読で、Authoritative §4のundo-log watermark表現がcommit後のframe mutationを文書長ぶん保持し、
同じ正本のO(structural nesting)制約と矛盾するfalse premiseを発見した。ユーザは2026-09-01に狭い
`notes/design/2026-09-01-yumark-frame-transaction-storage-addendum.md`を承認した。Yumarkだけをpersistent `Arc`
frame chain/root-swap checkpoint/iterative releaseへ替え、generic `RollbackStack`とordinary parser hot pathは不変に
保った。nested/cloned checkpoint rollback・superseded branchの解放・full snapshot、`YumarkUse`の`Recovered<UseTree>`
型をfocused testで確認し、compiler/performance delta reviewもgreen。Gate 1は完了。次はGate 2のisolated
marker/strict-close/line-doc/chunk/frame-stack judgesであり、root/canonical dispatchはGate 6まで未認可。

Gate 2も完了。`grammar/yumark/`だけにsink-free marker/strict-close/line-doc/chunk judgesを置き、`---`の
strict failureが`--`へfallbackしないこと、LF/CRLFだけのphysical newline、close suffix非消費、raw fenceの
arbitrary info、explicit quoteのbase column、canonical XID identifier start、frame transactionを一つのfocused
tableで固定した。AST/CST adapter・scanner・Declaration/Statement/root/canonical dispatchは未接続のままである。
focused test 1件、scoped rustfmt/diff check、compiler/spec delta reviewはgreen。package/workspace suite・timingは
行わなかった。次はGate 3のisolated inline/paragraph/section/list/quote/raw-fence grammarとlocal recovery/state/CST table。

Gate 3の着手前に、§5.4が選択済みとする`\ident(args)`/`[doc]:ident(args)`のouter delimiter bridgeを
Gate 3へ置くか、Gate 4へ後回しにするかというgate allocation矛盾を発見した。compiler/spec reviewは、inline
surfaceを完結させてsecond parserを作らないため、shared bridgeと二つのinline adapterをGate 3へ置き、Gate 4は
command/`my`/`use`/`if`のpayload policyとして再利用する案を支持した。同時に、Gate 3がYumark-owned consumed bytesの
`LineState`を一度だけ更新する責務を持つ。Draft
`notes/design/2026-09-01-yumark-gate3-embedded-yulang-allocation-amendment.md`はこの狭いallocationだけを変更し、
承認待ちである。承認まではGate 3 implementationへ進まない。

ユーザは2026-09-01にこのallocation追補を承認した。Gate 3はshared embedded-Yulang bridgeとinline
reference/apply adapter、committed Yumark `LineState` advanceを含むisolated structural grammarとして着手可能である。
Gate 4はcommand/`my`/`use`/`if`用のpayload policyとlayout/recoveryを同bridgeへ追加する。root/canonical dispatchは
引き続きGate 6まで未認可。

Gate 3は実装・M3 review/repairを開始したが、未完了のままarchitecture re-entryで停止している。isolated
`grammar/yumark/` driver、typed delimiter-floor bridge、canonical CallArgument interior/borrowed-close settlement、
direct NUD candidateのErrorSink rollbackを実装し、ordinary `CallTail`のcontrolとYumark AST/direct recovery・state
tableを追加した。reviewで、raw-fence/paragraphの二重走査、深いframe走査、active-ownerを見ないbridge boundary、
ordinary CallTailのtrivia順序、close evidence、word extent、inactive closerのcanonical close-slot recoveryを発見し、
single-forward `DocumentDriverState`/streaming consumerとshared canonical settlementへ原因修正した。直近の
`cargo test -p yu-syntax yumark_gate3_ --no-fail-fast`は、4096-byte plain paragraphのtest-only
`paragraph_bytes` counterが未配線で`0`になり失敗した。architecture auditはproductionのpre-scan/replayを否定し、
raw-inline consumerでのみbyte lengthを数える`cfg(test)` hookの欠落と判定した。M3 repair上限に達したため、
counter hookの狭い修復とfocused再検証は次の承認済みrepair枠まで保留する。Gate 3は未完了、Gate 4以降と
Declaration/Statement/root dispatchは未認可である。package/workspace suite・timing・stage/commit/pushは行わなかった。

ユーザは2026-09-02にこのcounter hookだけのexceptional repairを承認した。hookはASCII/multibyte paragraph、
fixed-end zero、raw fenceのcounterを正しく通したが、同じfocused tableで`a\r\n  b`のraw-inline consumerが
CRLFを`\r`/`\n`へ分割してadvanceし、`LineState::last_newline`を`1..3`ではなく`2..3`と記録する既存production
defectを発見した。Yumark-local source-unit classifier（CRLF=2、それ以外はUTF-8 scalar、lone CR=scalar）と
shared committed advance primitiveへの収束で、CRLF/LF/lone-CR/line-doc/raw-fence rowはgreenになった。最終delta
reviewはさらに、range validationが全rangeを二度decodeするP0、release hot loopに残るtest counter call、canonical
inner call recovery factをASTが捨ててdirectと不一致になること、borrowed-close malformed scannerがYumark hard
boundaryを跨いでcanonical byteのLineStateを壊すこと、hard-boundary/quote suffix evidence不足を発見した。
architectureはこれを単一のM2 exceptional repair——O(1) endpoint validation+完全`cfg(test)` counter elision、
shared canonical recovery-fact observer、boundary-aware borrowed malformed step、compact boundary table——として定義した。
これはcounter/CRLFだけの前許可を越えるため、追加の明示workflow許可待ちである。Gate 3は未完了、Gate 4以降と
Declaration/Statement/root dispatchは未認可である。package/workspace suite・timing・stage/commit/pushは行わなかった。

2026-09-02: exceptional repairのfocused Gate 3 tableを進める過程で、embedded canonical payloadのAST/direct
recovery parityに関するGate 3 allocationのfalse premiseを発見した。persistent embedded recovery logそのもの、
QuoteForm、nested quote、raw fence、single-forward LineState修正は局所的に成立したが、`parse_operator_chain`
はbraced/indented Statementを経てPattern/TypeExpressionと全declaration/For recovery ownerへ到達する。AST内で
direct parserを`HeaderOutput`で影走行してrecordを集める試作はone-forward/no-replayとdiagnostic transactionを
破るため破棄し、compiler baselineへ戻した。ユーザはfull canonical payload parityを延期せず、owner-local
shared recovery episodeを導入する方針を選択した。承認済み追補は
`notes/design/2026-09-02-yumark-gate3b-canonical-recovery-episode-amendment.md`である。Gate 3bは
`LegacyAst | EmbeddedObservedAst | Direct`のconceptual modeで各recovery ownerが一度だけ判断し、active
EmbeddedYulang時だけpersistent logへprimary recovery factをpublishする。ordinary AST/directの既存contract、
root/public dispatch、shadow parse、CST/AST walk、source replayは不変/禁止である。次はGate 3bのtransitive
owner adoptionとfocused matrixであり、Gate 3は引き続き未完了。package/workspace suite・timing・stage/commit/pushは
行わなかった。

Gate 3b追補のspec auditは「transitive owner」を動的な語のままにせず、有限のowner/witness/rollback matrixへ
固定することを要求した。`notes/design/2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`はExpression、Pattern、
TypeExpression/polymorphic variant、canonical StatementとBinding/Use/Mod/Struct/Enum/Error/Type/Role/Impl/Cast/Act/
For/Derives/companion、Enum/Error shared variant cross-productを列挙し、既存ordinary malformed witness、primary
role/expected/range/kind/order、rollback layerを対応付ける。また、recovery済みfirst adapterがframe pop後にclean
reference/applyへfactを漏らさない連続sourceを必須証拠にした。このmatrixはGate 3b追補§4/§6のAuthoritative appendixである。

2026-09-02: Gate 3bのordinary-primary preparationで既存owner contractを実測し、Case/Catchのfresh missing
Patternを`CaseLike(Pattern/Handler)`へ正しくrouteした。non-empty malformed Patternは引き続きinner
`Pattern(Primary)`である。さらに`ENUM-T`の未完extractを発見・修正した。Struct、Enum、Errorのbrace named
field payloadは`variant_core`のone owner-parameterized post-opener sequence driverを共有し、Struct baseまたは
Enum/Error declaration base、field recovery role、neutral close ownerだけをspecで渡す。従ってsame-line
`a: A b: B`はfirst TypeExpressionが`b:`の前でyieldし、one Missing FieldSeparatorの後に同positionからsecond
fieldをretryする。comma、implicit newline、semicolon、local/outer mismatched close、trailing comma、layout stateも
single driverが一度だけ裁定する。`A B`はvariant separator missingではなくPositional payloadでzero recoveryなので、
matrixの矛盾したV5はV1–V4 cross productから削除し、NV1 no-recovery exclusionへ訂正した。P7g record nested
Patternのnon-empty `@` Error後にsame-slot Missingを重ねる既存cascadeも修正した。

focused evidenceは`cargo test -p yu-syntax gate3b_ --no-fail-fast`で6 passed、0 failed、591 filtered（既存warning
33件）。compiler/spec/regression独立reviewはapproved。tableはStruct indented/tuple/TypeApply non-split、Enum/Error
V3 exact field/recovery/topology、NV1、outer `]` non-consumeとprefix CST、P7gのone Error nodeまで固定する。format、
diff check、package/workspace suite、timing、stage/commit/pushはこのfocused bundleでは行わなかった。Gate 3bの全
transitive canonical recovery episode adoption、Gate 4 command grammar、Gate 5 envelope、Gate 6 dispatchは未完了・未認可である。

2026-09-02: Gate 3bの最初の有限 adoption sliceとしてE2 fixed `.` / `::` tailを完了した。
`fixed_tail_recovery_episode`がFieldName/PathSegmentのmaximal invalid runまたはzero-width Missingを一度だけ
裁定し、ordinary ASTは従来どおりfactを外へ出さず、active EmbeddedYulang ASTだけpersistent recovery logへ
publishし、directは同じneutral factからone CommittedRecoveryRecordとone generic Missing/Error nodeをemitする。
`::`後のmaximal triviaはepisodeより前にPathTailが所有する。ordinary controlは`x.`、`x.@`、`x::`、`x::123`の
selected primaryをIdentifierとして固定し、`x:: $name`でPathTailの`ColonColon`・Whitespace・SigilIdentifier childと
zero recoveryを確認した。embedded controlsは`\\ref(x.)`、`\\ref(x::123)`、`\\ref(x:: 123)`の
role/range/kind/primary/order、node topology、range/remainder、frame popとdirect diagnostic-id deltaを確認した。
actual owner RB-E probeはpreseeded sink/persistent factを含むinput/local/output/cut rollbackを確認する。
`cargo test -p yu-syntax yumark_gate3_ --no-fail-fast`は1 passed、596 filtered、
`cargo test -p yu-syntax fixed_tail_recovery --no-fail-fast`は1 passed、596 filtered（いずれも既存warning 33件）。
compiler/spec M2 reviewはapproved、`git diff --check`はgreen。scoped rustfmt checkはsession/expression/yumark testsの
並行・既存領域を含むformat deltaで失敗したため、format editは行わなかった。package/workspace suite、timing、
stage/commit/pushは未実施で、Gate 3bの残る有限owner inventoryは引き続き未完了である。

2026-09-02: 次の有限 slice D11b `Declaration(Derives(ViaTarget))`を完了した。ordinary derives-viaと
companion-handoff derives-viaのAST/direct四adapterは、boundary-parameterizedなsingle
`derives_via_target_episode`を共有する。episodeはIdentifier primaryのMissing/Error factと
RetrySameSlot/StopAtBoundaryを返し、`with:` handoff、CR/LF、close、EOFは未消費のまま親ownerへ残す。malformed
runの後にraw identifierがあるときだけtargetをretryする。embedded ASTのみpersistent logへpublishし、directは
generic Missing/Error nodeをDerivesClause直下にemitする。D11a RoleReferenceは未変更である。
focused evidenceはMissing/Error+retry/clean embedded row、companion `with:` retention、one node topology、
outer brace/paren ownershipとreal candidate RB-DRVを含む。RB-DRVはsynthetic episode helperではなく
`recognize_derives_attachment_start -> parse_derives_attachments_isolated`をactual transaction下で走らせ、
ViaTarget Error `15..17`と`key` retryを観測してからinput/local/error sink/output/cutをrollbackする。
`cargo test -p yu-syntax --no-fail-fast gate3b_derives_via_target_episode`は2 passed、597 filtered
（既存warning 33件）。compiler/spec M2 reviewはapproved。Gate 3bの残る有限inventory、Gate 4 command grammar、
Gate 5 envelope、Gate 6 dispatchは未完了である。

2026-09-02: 次の有限 slice D12a `Declaration(Companion(Introducer))`を完了した。
`scan_declaration_companion_introducer_retry`の既存one-pass scannerを
`DeclarationCompanionIntroducerEpisode`へ収束し、AST/directが同じ`Open(Brace)` primary factから
Missing/ErrorとRetrySameSlot/StopAtBoundaryを決める。directの既存`Colon` auxiliary expectationと
primary index 0は保持した。embedded AST outcomeがfactの`unexpected`を落としていた局所transport gapも
同時に修正し、Yumark自身のrecoveryは`None`、embedded canonical factは値をそのまま保つ。
`with]tail`、`with\nnext`、`with item`のactive-frame controlでboundary非消費、LineState、inline retryを、
full Yumark shellでouter braceとborrowed parenthesisのownerを固定した。actual RB-CMPはpreseeded fact/sinkを
含むinput/local/output/cut rollbackを確認する。`cargo test -p yu-syntax
gate3b_declaration_companion_introducer_episode --no-fail-fast`は3 passed、599 filtered（既存warning 33件）。
compiler/spec M2 delta reviewはapproved。`notes/design/2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`の
§5a historical stagingもnon-normativeに明確化し、旧D12a `:` primary記述をactual ordinary producerの`{` primary
（`:` はauxiliary）へ訂正した。次はmatrixの次の依存なし有限ownerを選定する。D12b–f、D11a、Gate 4 command
grammar、Gate 5 envelope、Gate 6 dispatchは未完了・未認可である。

2026-09-02: 将来のparser architecture re-entryに備え、ユーザ承認のもとbreakingな
`chasa-recover 0.2` core prototypeをworkspace member `crates/chasa-recover`へ追加した。
`ParserOnce<I, R, S> -> Option<Output>`、`None`のinput-nonconsumption契約、`R`の
passive snapshot rollback、`&str` suffix pointerだけを比較する`Input::Index`、
unit-state tuple transaction、transactional `choice`を固定した。`In`はchasa 0.5と同じ
`reborrow_generic`の`#[derive(Reborrow)]` / `R::Target<'a>` / `S::Target<'a>`を使い、
recoverはstatic `Recover: Rb` capabilityとconcrete state用`Recoverable`の`&mut T` bridgeで
短いtargetを得る。`In::map(p, f)`はoutput-only、`In::then(p, f)`と`ParserOnce::then`は
inner grammarを必ず`check`してから`In`を渡すcommitted continuation、通常の
`map_once`/`map_mut`/`map`はstate-free output transformである。`S = ()` callbackは
後戻り不能なprocedural escape hatchとして意図的に残す。これはYulang production parserの
移行・CST/AST/diagnostic authorityの変更を認可しない。M3のcompiler/spec/regression delta
reviewはapproved、`cargo fmt --check -p chasa-recover`とfocused
`cargo test -p chasa-recover --no-fail-fast`は9 passedでgreen。production候補に進むには、既存
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`の契約を満たす別のAuthoritative
migration designと、owner-aware boundary/typed diagnostics/ParseLocal・CST transactionの実証が必要である。

2026-09-02: ユーザ承認のfollow-upとして、`FnOnce(In<I, R, ()>) -> Option<T>`を
factoryなしで直接`ParserOnce`にした。function parser自身が`R` markerを取り、`None`時は
`R`をrollbackしてから`Input::Index`（`&str`ではsuffix pointer）だけを比較し、inputを
矯正せずpanicする。`In::check`は読みやすい`i.check(parser)?`入口としてparserへ委譲するだけで、
input/Rのmark・比較・rollbackを行わない。tuple/choiceの全体transactionは不変であり、これは
合成parser自身が返す`None`の正当なrollbackである。Rowanのようなnon-recoverable `S`を
fallible closureから汚さないため、直接function parserは`S = ()`に限定し、`S`を使う既存の
`then` callbackはtotalのまま維持した。custom non-unit `ParserOnce`はtotal、または`None`時に
`S`不変を守る契約とした。`check`がtransactionを隠れて作らないcounter witness、function
parserの`R` rollback、consume-then-`None` panic後にcursorを戻さない`then` witnessを追加。
M2 compiler delta reviewは最終approved、`cargo fmt --check -p chasa-recover`と
`cargo test -p chasa-recover --no-fail-fast`は10 passedでgreen。Yulang production migrationの
認可範囲は従来どおり拡張していない。

2026-09-02: ユーザは全面 parser rewrite の移行順として、remaining legacy Yumark Gate 3b
owner adoptionをここで停止し、Authoritative adoption matrixを新 parser の必須acceptance
evidenceへ引き継ぐ方を選択した。`notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`は
M3 compiler/spec/regression reviewとdelta reviewを閉じ、ユーザ承認で`Authoritative`にした。
`I = &str`のchecked root-pointer range、current-item completion（lookaheadは禁止）、explicit
`Boundary`、non-numeric `TailPosition`、composite committed `S`、AST/direct adapter保持、
`ParseLocal` bridgeなし、old/new crossingなし、HeaderInfo identity/record transportを確定した。
Gate 4–8はisolated closureのみで、production dispatchはGate 9まで不変である。Gate 1
(`with_str`)だけが次に認可された。Gate 3bのmatrix・Yumark surface/frame contracts・既存完了sliceは
そのままnormative controlである。

2026-09-02: Authoritative Gate 1 `with_str` substrateを完了した。`In<&str, R, S>::with_str`
はowned `In` のshort reborrowから、nested operationがcurrent cursorで実際に消費したborrowed sliceを
`(output, &str)`として返す。outer handleを残すnested caseは`i.rb().with_str(...)`であり、
actual lookahead、next-item cache、allocation、source rewind、cursor correctionは導入しない。
`ParserOnceStrExt::with_str()`はinput-independent blanket extensionとしてconstruction時の`I/R/S`
inferenceを遅延させ、run時の`&str` parser successだけを`(output, consumed_str)`に写す。nested、UTF-8、
CRLF、zero consumption/zero-copy、parser success、tuple nonmatchのinput/`R` rollback、`S` successを
focused witnessにした。`cargo fmt --check -p chasa-recover`、`cargo test -p chasa-recover --no-fail-fast`
は15 passed、M2 compiler/refereeとregression reviewはapproved。broad workspace check/timingはGate 1の
scope外で未実施。次はGate 2 isolated execution shellであり、production dispatchは未認可のままである。

2026-09-02: expression の `expr`/`tail` item-handoff 追補
(`notes/design/2026-09-02-yu-syntax-expression-tail-handoff-addendum.md`)を、M3 compiler/recovery・
specification review と scoped delta review 後にユーザー承認で `Authoritative` とした。追補は
expression pilot に限り、二状態 `TailPosition`、non-numeric level 制限、fallible direct function の
`S = ()` 制限を置換する。`TailExit = Result<(), Either<Item, End>>` は通常完了・同一 item handoff・
boundary propagation の三経路を持ち、binary/ML application/prefix は全てこれに従う。`S` は直接 Rowan
出力能力だが、emit 後に `None` を返さず total な typed-recovery/handoff continuation に入る。`tail_item`
は ML argument と `(` を含む一論理 tail item を分類するが、layout が継続を許さない newline/dedent は
opener 前に boundary として返す。Gate 2 は generic action/materializer shell ではなく、この直接
expression closure を pilot として実装する。ただし既存 Gate 2 の state/range/recovery/rollback acceptance
template と Gate 3 の E2/E3、Gate 4 の RB-E 割当は全て維持し、production dispatch は引き続き未認可である。

2026-09-03: Gate 2 direct pilot の M2二巡目 review は、CST/actual `OperatorChain`、owner-specific
recovery、resumable item、23-field cone、三経路 witness の初回 blockers を閉じた一方、accepted
malformed RHS が child `level`/ML mode を捨てることと、boundary resume/close/stop classifier の
cursor/frame/token/owner capability 検証がないことを検出した。ユーザー承認により handoff
addendumへ二規則を追加した。M2の二巡 budgetは使い切ったため、Gate 2 は未完のまま M3一回だけの
scoped repair/reviewへ昇格する。production dispatch、legacy crossing、Gate 3/4 matrixは引き続きscope外。

2026-09-03: Gate 2 direct pilot は完了した。`rewrite/` の直接 `expr`/`tail` は actual
`OperatorChain` と Rowan を受理 branch で直接構築し、binary/prefix/ML の三経路、ML/call/parenthesis
の nested CST/AST、typed recovery、root-pointer range、UTF-8/CRLF/EOF logical position、23-field
dependency cone、rollback/no-rescan を隔離された pilot として固定した。M3 の一巡目で見つかった
EOF 時の released dedent payload と recovered ML child ownership の二点も、二巡目 scoped repair と
compiler/recovery・specification delta review の両 approve で閉じた。focused
`cargo test -p yu-syntax rewrite::tests -- --test-threads=1` は 11 passed / 0 failed / 604 filtered、
`cargo fmt --package yu-syntax -- --check`、`cargo check -p yu-syntax`、scoped diff check は green。
package/workspace suite と計測はこの isolated gate では実行しない。production dispatch、legacy
crossing、Gate 3 の E2/E3 と Gate 4 の RB-E は未認可のまま残る。次は Gate 3 fixed-tail pilot の
範囲を authority に沿って切る。

2026-09-03: ユーザー承認により `2026-09-03-yu-syntax-gate3-fixed-tail-pilot.md` を
Authoritative とした。active gate は Gate 3 の E2 Field/Path direct tail と E3 の
borrowed outer-close witness である。call item/separator/missing-close、projection、production
Yumark bridge、legacy crossing、Gate 4/RB-E は scope 外に固定する。M3 の実装後 review は
compiler/recovery と specification の二本に限定し、focused rewrite table、scoped format/diff check、
`cargo check -p yu-syntax` を実行する。performance measurement と package/workspace suite は、
新規の replay、非線形 scan、hot-path allocation が生じない限り行わない。

2026-09-03: Gate 3 fixed-tail pilot は完了した。`rewrite/` に atomic `.` Field と `::` Path
item、direct FieldTail/PathTail AST/CST、owner-local typed Missing/Error と same-slot retry を追加し、
projection head は `Deferred` item のまま Gate 4 へ返す。spaced ML child の adjacent fixed chain は child
内に残す一方、dynamic `+` と trivia-separated tail を child が scan しない Gate 2 contract を維持した。
E3 は `\ref(x. )tail` / `[d]:f(x. )tail` の leading-trivia present `)` だけを isolated args adapter が
borrow/emit し、empty-trivia close は typed unclaimed outcome へ返す。M3 の compiler/recovery と
specification review は、two repair rounds と final test-only review 後に approve。focused
`cargo test -p yu-syntax rewrite:: --no-fail-fast` は 18 passed / 0 failed / 604 filtered、
`cargo check -p yu-syntax`、scoped rustfmt/diff check は green。package/workspace suite と計測は未実行。
production dispatch、legacy/Yumark bridge、projection/full E3、Gate 4 の Expression/RB-E closure は
引き続き未認可・未実装であり、次の active gate は Gate 4 の設計である。

2026-09-03: ユーザー承認により
`notes/design/2026-09-03-yu-syntax-gate4-6-scc-amendment.md` を Authoritative とした。
これは Gate 4–6 を TypeExpression/PV の acyclic prerequisite と、Expression/Pattern/canonical
Statement/declaration/body の共同 SCC construction として確定し、E12 register を E12a–E12k へ
訂正する。dynamic operator の戻り読みは、Item を生成・所有しない raw lexical token probe
だけに限る。grammar owner、completed Item、assigned trivia、CST、diagnostic、recovery の reread
は禁止である。次の active gate は isolated G4a dynamic item/operator kernel であり、production
dispatch、legacy/new crossing、Yumark production bridge は引き続き scope 外である。

2026-09-03: isolated G4a dynamic item/operator kernel を完了した。immutable
`OperatorTable` の all-spelling/value-start trie、source-only token probe、dynamic
Prefix/Nullfix/Infix/Suffix/ML handoff、BindingPower threshold、word/decimal literal と
flat source-order `OperatorChain`、typed ordinary trivia と base MissingOperand/Error
recovery を direct rewrite pilot に実装した。review で発見した comment-separated
indentation を ordinary trivia oracle に合わせ、nested/unterminated comment と CRLF を
含む raw evidence を修正し、invalid recovery retry-head の all-trie work を §4.3 の
`T_all` に加えた。M2 specification/performance review と一回の batched repair を閉じ、
`cargo test -p yu-syntax rewrite::tests -- --test-threads=1` は 28 passed / 0 failed、
`cargo test -q -p yu-syntax operator::tests -- --test-threads=1` は 14 passed / 0 failed、
format/diff check は green。parametric contract に従い benchmark、package/workspace suite
は未実行。production dispatch、legacy/new crossing、Yumark production bridge は scope 外の
まま、次は isolated G4b expression-local delimited/fixed owners である。

2026-09-03: ユーザー指示により successor rewrite の実験用構造を削除した。`Pilot*`、
別 `Context`、frame/stop stack、`Level` wrapper、Item identity/scanned-item history、
line state、output chain stack、`is_cut`、手書き `ParserOnce` wrapper、routine
`In::then`、borrowed-source を抱える一時 `Item`/token/trivia、trivia 上書き経路を除去した。
この中間 topology は 2026-09-03 後半の user decision で置換対象になった。successor
rewrite は source/root/range/borrowed AST を持たず、`Recover` は operator table と真に
recoverable な facts のみ、`S` は直接の `GreenNodeBuilder`、Item は owned text/trivia にする。
lexical `token` transaction と `maybe` は M3 scoped compiler/spec review 後に
Authoritative 化した。chasa-recover の focused API slice は実装・repair review 完了
(`token`/`maybe`、outer `S` を隠す private unit reborrow、unit-state-only `check`、19 tests
green)。続く source-free CST-only foundation は実装・M3 review 完了した。旧 rewrite shell を
direct `expr`/`tail` と local `In` alias へ置換し、`Recover = &OperatorTable + Mark=()`、caller-owned
direct `GreenNodeBuilder`、source lifetime/range/root/cursor を持たない owned Item/trivia/End にした。
grammar procedure は builder の生成/root/finish をせず、outer owner が `S` と tree completion を持つ。
最初の closure は identifier core と次 Item/EOF handoff のみで、leading trivia は exact
horizontal whitespace・CRLF/CR/LF・line comment・arbitrarily nested block comment を owned typed
part として保持し、word は `_` start と trailing `?`/`!` 一文字を現行 lexical authority に合わせる。
compiler/recovery review の trivia/word と CRLF/NBSP blocker は二回の repair で閉じ、final review と
specification review は clean。`cargo test -p yu-syntax rewrite::tests -- --test-threads=1` は
7 passed / 0 failed / 606 filtered、`cargo check -p yu-syntax`、scoped format/diff check は green。
package/workspace suite と performance measurement は未実行。先の focused 23 件はこの topology の
completion evidence ではない。E5 の user decision
`x[a(b)]`（一つの `IndexItem` の nested `CallTail`、`IndexSeparator` recovery なし）は
CST owner control として引き続き正本である。未完成の G4b owner loop を含むため、まだ
coverage ledger は閉じないが、この source-free foundation は独立した commit/push 境界とする。
follow-up で driver 内に残っていた test-wrapper `parse`/`ParseResult`（builder生成/root/finish）を
除去し、rewrite entry は caller-owned builder を `S` として受ける direct `expr`/owned `TailExit` のみと
した。test-only outer owner は source `String` を drop 後に owned `End` trivia を emit して builder を
finish する witness を持つ。M2 compiler/recovery review と closure review は clean、focused 7 tests は
green。

2026-09-03: isolated G4b E5 valid witness を完了した。`x[a(b)]` は outer `IndexTail` の exactly one
`IndexItem` に direct `OperatorChain(a)` を置き、その nested `CallTail` が `OperatorChain(b)` と同じ
handoff `)` を所有し、outer IndexTail が続く同じ handoff `]` を所有する。`IndexItem` は E5 正本が
要求済みの CST node として追加した。source/item の再scan、source lifetime/range/root/cursor、delimiter
stack、old parser bridge、outer builder生成、Missing/Error/`IndexSeparator` はない。mismatched close/EOF は
owned Item/End のまま上位 owner へ伝播する。M3 compiler/recovery/specification review は clean、focused
`cargo test -p yu-syntax rewrite::tests -- --test-threads=1` は 8 passed / 0 failed / 606 filtered、
`cargo check -p yu-syntax`、scoped format/diff check は green。package/workspace suite と measurement は
未実行。これは E5 の valid construction control だけで、G4b owner loop、leading-item/missing-bracket/
separator recovery、production、AST parity、Yumark bridge、Gate 4/G4b coverage ledger は未完了である。

2026-09-03: ユーザーは上の E5 primary witness を訂正した。`x[a b]` は `a` の tail がすでに
leading-horizontal-whitespace を含めて取得した `b` Item を、再 scan せず `MlArgument` の子式へ渡す
one `IndexItem` である。`IndexSeparator` Missing は作らない。`x[a(b)]` は `CallTail` の `)` と
`IndexTail` の `]` の owner control を保つ補助 witness へ下げる。正本は
`notes/design/2026-09-03-yu-syntax-g4b-e5-index-ml-application-correction.md`。この narrow valid
construction 以外の ML layout/comment/other NUD/multiple-argument、index separator/missing-close
recovery、production、AST parity、Yumark bridge、Gate 4/G4b ledger は未完了である。

2026-09-03: この訂正済み isolated valid witness は完了した。`x[a b]` は one `IndexItem` 内で
one `MlArgument(b)` を作り、同じ `]` を `IndexTail` まで handoff する。ML child の continuation
capability は child 自身の adjacent CallTail/IndexTail を通しても保たれ、`x[a b c]` と
`x[a b(c) d]` は sibling `MlArgument` になって child 内へ nest しない。M1 spec pre-write と
semantic closure review は、二つの continuation propagation gap を修正後 clean で閉じた。
focused rewrite 11 tests、`cargo check -p yu-syntax`、scoped format/diff check は green。
package/workspace suite、performance、production、AST parity、Yumark bridge、上記の deferred
G4b owner/recovery controls と Gate 4/G4b ledger は未実行・未完了である。

2026-09-03: source-free rewrite の G4b valid delimited control を拡張した。`(...)` を
identifier と並ぶ direct NUD にし、parenthesized/call/index owner が empty と comma/semicolon
区切りの ordinary item sequence を受理する。private `delimited_items` は close token と optional
`IndexItem` wrapper だけを受け、accepted owner へ直接 emit する。matching close を emit したら
owner node を閉じてから初めて outer tail を scan するため、`(a,b;c) d` の `MlArgument(d)` は
parenthesized node の外に出る。`f(a,b;c)[x,y;z]` の call close/index close と、`()`/`f()`/`x[]`
の empty shape を focused controls で固定した。missing item/separator/close、wrong close、newline
layout、comment ML、projection、production/AST/Yumark bridge、G4b/Gate 4 ledger は引き続き未実装。
focused rewrite tests は 14 passed、package check、scoped format/diff check は green。

2026-09-03: 同じ isolated G4b valid control に fixed field/path tail を追加した。field は accepted
`.` Item とそれに隣接する identifier を `FieldTail` に、path は greedy `::` Item と次の
identifier Item（leading trivia を含む）を `PathTail` に直接 emit し、それぞれ node を閉じてから
outer tail を scan する。`a .field:: name b` は flat `FieldTail`/`PathTail`/`MlArgument` と token
owner を固定し、`a..`/`a...` は field にしない。field/path RHS recovery、projection、sigil path
segment、newline/layout、production/AST/Yumark bridge、G4b/Gate 4 ledger は未実装のままである。
focused rewrite tests は 16 passed、package check、scoped format/diff check は green。

2026-09-04: direct dot dispatch は field より先に projection opener を取るよう拡張した。`.` の
次が adjacent `(` なら `ProjectionTupleTail`、adjacent `{` なら `ProjectionRecordTail` を直接
emit し、既存 `delimited_items` が comma/semicolon item sequence とそれぞれの close を所有する。
`a.(x,y).{left,right}` は outer `OperatorChain` に tuple/record tail を平坦に置き、`)`/`}` は
各 projection node が所有する。spread・record colon item・missing/separator/close recovery、wrong
close、layout、production/AST/Yumark bridge、G4b/Gate 4 ledger は未実装のままである。focused rewrite
tests は 17 passed、package check、scoped format/diff check は green。

2026-09-04: source-free direct rewrite に既存 oracle と同じ ASCII decimal integer NUD を追加した。
lexical transaction が一個以上の ASCII digit を greedily owned `Integer` Item として受理し、
`IntegerLiteral(Integer)` を直接 emit する。normal core として identifier と同じ direct tail
continuation を持つため、`123(a).field::name` は `IntegerLiteral` から Call/Field/Path tail を一つの
flat `OperatorChain` に置く。ML の argument vocabulary、integer 以外の literal、recovery、layout、
production/AST/Yumark bridge、G4b/Gate 4 ledger は引き続き scope 外である。focused rewrite tests は
18 passed、package check、scoped format/diff check は green。

2026-09-04: isolated source-free dynamic-operator scanner spine を追加した。pre-Item の raw
suffix evidence、all-spelling の long-to-short fallback、merged Prefix+Nullfix 用 filtered
value-start trie、explicit binding threshold/baseline/active-stop 引数、flat direct CST emission、
Pratt Item handoff を実装した。§4.3 の source-only parametric accounting を採用し、rejected
candidate は input/Recover/Rowan builder を変えない。M2 semantic/spec delta review は一件の
`without_value` control 追加後 clean。focused `rewrite::tests` は 28 passed、package check、format、
diff check は green。これは Gate 4/G4a や E/RB-E ledger を閉じず、production、AST parity、
recovery diagnostics、Yumark、performance claim を含まない。

2026-09-04: isolated G4b の direct delimited owner に EOF-close control を追加した。
parenthesized/call/index/tuple projection/record projection は accepted child 後または opening
trivia 後の owned EOF Item から leading trivia を一度だけ自身へ emit し、zero-width `Missing`
を owner 内に直接置いてから empty-leading `End` を外へ handoff する。source の reread、cursor/
state/rollback、event buffer、recovery record は追加していない。matching close は不変。これは
E3/E5/E7g-h と parenthesized close の CST-only construction control であり、typed recovery
record、wrong close、missing item/separator、layout、Gate 4/G4b ledger は未完のままである。M1
specification review は clean、focused rewrite tests は 29 passed、package check、format/diff check
は green。

2026-09-04: 同じ G4b loop に separator-before-item の CST-only control を追加した。pending
comma/semicolon Item は leading trivia を一度だけ owner 内の zero-width `Missing` へ移してから、
同じ empty-leading separator Item を emit/consume し、exactly one replacement Item を scan する。
これは `(,a)`/`f(,a)`/`f(a,,b)`/`x[,a]`/tuple・record projection の direct owner control であり、
index の Missing は `IndexItem` wrapper を持たない。source reread、state/rollback、event buffer、
recovery record の追加なし。wrong close、missing separator、layout、typed recovery record、Gate
4/G4b ledger は未完。M1 specification review は clean、focused rewrite tests は 30 passed、package
check、format/diff check は green。

2026-09-04: G4b direct delimited owner の wrong-close CST-only control を追加した。expected close
を優先し、それ以外の `)`/`]`/`}` Item は owner-local `Error` として直ちに emit/consume して
exactly one replacement Item を読む。`f(a])` は Error(`]`) 後に CallTail 自身が `)` を受理し、
EOF へ至る wrong close は既存の owner-local Missing-close へ進む。source reread、state/rollback、
event buffer、recovery record の追加なし。missing separator/layout/other invalid run/typed recovery
record、Gate 4/G4b ledger は未完。M1 specification review は clean、focused rewrite tests は 31
passed、package check、format/diff check は green。

2026-09-04: parenthesized item の same-line missing-separator CST-only control を追加した。
`items_accept_ml` は retained context でなく delimited owner が直接渡す scalar で、parenthesized は
false、call/index/tuple・record projection は outer ML continuation に関係なく true。false owner が
already-scanned NUD handoff を受けると、その leading trivia を出して zero-width `Missing` を置き、
同じ Item を再scanせず次の item として parse する。よって `(a b)` は二つの OperatorChain と一つの
Missing を持ち、`x[a b]`/`a.(x y)` の ML rule は不変。layout newline、typed recovery record、other
invalid run、Gate 4/G4b ledger は未完。M1 specification review は clean、focused rewrite tests は 32
passed、package check、format/diff check は green。

2026-09-04: G4b direct delimited owner に baseline 以下の layout newline を item continuation として
受理する CST-only control を追加した。opener 後に得た既存 scalar baseline と already-scanned handoff
Item の owned leading trivia だけを一回走査し、newline があり終端 indentation が baseline 以下なら、
同じ Item を reread/rescan せず次の item として loop へ戻す。parenthesized/call/index/tuple・record
projection 全 owner に共通で、state/rollback、event buffer、recovery record は追加していない。deeper
newline と other invalid run は close phase の別 slice、typed recovery record と Gate 4/G4b ledger は
未完である。M1 specification review は clean、focused rewrite tests は 33 passed、package check、
format/diff check は green。

2026-09-04: authoritative `MlArgumentSeparator` / `LayoutDelimitedFrame` に合わせ、direct rewrite の
ML policy を caller-owned scalar `MlMode::{All, LayoutOnly, None}` に明確化した。All は physical
newline のない non-empty typed trivia（opaque block comment を含む）または baseline より深い physical
newline を ML とし、parenthesized item の LayoutOnly は同じ deep newline だけを ML とするため、
`(a b)` の Missing separator と `(a\n  b)` の一 item chain を両立する。nested `MlArgument` は None
で二段目を外側へ handoff する。layout baseline と implicit separator も typed `Newline` とその直後の
Whitespace だけから求め、block comment 内の byte は layout に参加しない。deeper newline を close
phase に誤って送る試案は authority conflict として撤回済み。source reread/state/rollback/event buffer/
recovery record の追加なし。M1 specification review は repair 後 clean、focused rewrite tests は 37
passed、package check、format/diff check は green。typed recovery record、other invalid run、Gate 4/G4b
ledger は未完である。

2026-09-04: G4b delimited owner の mandatory NUD retry を追加した。parenthesized/call/index/tuple・record
projection の item loop は close/separator/EOF を先に保ったうえで invalid Item を owner-local の一つの
`Error` 内で、next NUD candidate または同じ boundary まで consume し、candidate を同じ item slot として
retry する。したがって `(@@a)` は一つの Error の後に `a` を一 element として持ち、five owner の
`@` retry も valid item へ戻る。各 iteration は current Item を消費し、source reread/state/rollback/event
buffer/recovery record は追加していない。M1 specification review は clean、focused rewrite tests は 38
passed、package check、format/diff check は green。typed recovery record、other invalid run、Gate 4/G4b
ledger は未完である。

2026-09-04: G4b E2 の direct FieldTail/PathTail mandatory identifier slot を追加した。accepted `.` / `::`
は EOF、fixed continuation、separator、close に対して tail 内の zero-width `Missing` を置き、invalid
run は next fixed/dynamic/owner boundary まで一つの local `Error` として consume する。field の whitespace
RHS は dot 直後の Missing 後に outer tail へ intact handoff し、path の trivia は PathTail 自身が所有する。
`x::::name` は first PathTail の Missing 後に second `::` を unconsumed で common tail loop へ返し、second
PathTail を正常に構築する。source reread/state/rollback/event buffer/recovery record の追加なし。M1
specification review は clean、focused rewrite tests は 39 passed、package check、format/diff check は
green。typed recovery record、other invalid run、Gate 4/G4b ledger は未完である。

2026-09-04: G4b E7e/E7f として direct `ProjectionRecordSpreadItem` を追加した。record projection の
item-required position だけで exact maximal `..` をまず spread marker として受理し、`a.{..}` / `a.{..,
next}` は spread node 内に RHS Missing を一件置いて `}` / separator をそのまま owner loop へ返す。
`a.{..@rest}` は `@` を同じ RHS slot の一つの Error にして `rest` から再開する。ordinary item または
spread RHS の後に rejected marker が来る場合は owner が Missing separator を一件置いて同じ Item を retry
し、invalid run も exact marker を消費しない。record owner の copied stop scalar は NUD item position では
fixed marker を先に、LED と spread-RHS の prefix probe では declared dynamic operator を先に判定するため、
`a.{left .. right}` の accepted infix と `...` / `..+` の longer dynamic spelling を spread に分割しない。
source reread、retained state、buffer は追加していない。M1 specification review は initial 2件とその後の
隣接 recovery 2件を修正後 clean。focused rewrite tests は 46 passed、package check、format/diff check は green。typed
recovery record、other invalid run、production/AST/Yumark bridge、Gate 4/G4b ledger は未完である。

2026-09-04: G4b E2 の direct `PathTail` に path-segment lexical vocabulary を補完した。`::`直後は
ordinary word、`$` / `&` / apostrophe 接頭辞 word、`_foo` を先に一 Item として読んで、それぞれ
`Identifier` / `SigilIdentifier` token として PathTail 自身へ emit する。bare `_` は ordinary
Identifier のままにし、path segment が不成立のときだけ既存 dynamic/fixed boundary fallback と
Missing/Error recovery を使う。trivia ownership、source reread/state/rollback/event buffer/recovery record は
増やしていない。M1 specification review は clean、focused rewrite tests は 47 passed、package check、
format/diff check は green。typed recovery record、other invalid run、production/AST/Yumark bridge、Gate
4/G4b ledger は未完である。

2026-09-04: direct rewrite の growing owner code を責務ごとに分割した。`driver` は expression recursion と
owned Item handoff、`delimited` は唯一の parameterized Item/Separator/Close loop とその local recovery、
`tails` は call/index/dot/path fixed continuation を担当する。fixed-tail fixture は `tests/tails` へ移し、
existing contract を変更していない。state/source reread/event buffer/新しい parser abstraction は追加して
いない。M1 review は stale duplicate owner の compile blocker 一件を削除後 clean、focused rewrite tests は 47
passed、package check、format/diff check は green。typed recovery record、other invalid run、production/AST/
Yumark bridge、Gate 4/G4b ledger は未完である。

2026-09-04: Gate 4–6 SCC amendment の acyclic prerequisite として、source-free direct
`TypeExpression` の normal core を追加した。identifier/sigil identifier/integer atom、parenthesized group、
call、`::` path、one-argument TypeApply、right-associative `->` を既存 type/expression parser や dynamic
operator table に依存せず、owned Item handoff と direct Rowan emission だけで構築する。type-ML boundary と
tail priority は `boundary → empty-trivia arrow/call/path → nonempty type-ML stop → nonempty arrow/path →
TypeApply` とし、`F A::B` は apply 内 path、`F A ::B` は outer path、`F A -> B` は outer arrow として
区別する。source reread、retained state、buffer、recovery record は増やしていない。これは valid input の
construction-only slice であり、mandatory-slot/invalid/close recovery と production use-site wiring は未実装、
Gate 4/G4b ledger は不変である。M1 specification review は clean、focused rewrite tests は 51 passed、package
check、format/diff check は green。

2026-09-04: standalone `TypeExpression` の `TypePathTail` mandatory segment に direct CST recovery を追加した。
accepted `::`後のEOF、separator、arrow、next `::`、call、all close tokenはtail内のzero-width `Missing`一件で
止めてboundary Itemを同位置のtail judgeへ返し、`A::::Name`はfirst Missing後にsecond path tailを構築する。non-name
runはone maximal non-empty `Error`にしてvalid name segmentまたはsafe boundaryまでretryし、`A::123`をpath segmentに
しない。post-`::` triviaはMissing/Errorが置かれるaccepted PathTailに一度だけ保持する。state/source reread/buffer/
recovery recordの追加なし。M1 specification review はclean、focused rewrite testsは52 passed、package check、format/
diff checkはgreen。call/group/arrow/primaryのremaining recoveryとproduction wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: standalone `TypeExpression` の accepted `TypeArrowTail` mandatory RHS に direct CST recovery を
追加した。exact `->`後のEOF、separator、all close token、equal-or-shallower newlineはarrow tail内のzero-width
`Missing`一件にpost-arrow triviaを置き、boundary Item自体はconsumeせずcallerへ返す。malformed RHS runはone maximal
non-empty `Error`にし、next valid TypePrimaryでsame RHS slotをretryする。boundaryへ至ったErrorにMissingを重ねず、
recursive RHSのright-associative arrow ownershipは維持する。state/source reread/buffer/recovery recordの追加なし。M1
specification review はclean、focused rewrite testsは53 passed、package check、format/diff checkはgreen。call/group/
primaryのremaining recoveryとproduction wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: `TypeCallTail` / `ParenthesizedTypeGroup` の shared direct delimiter owner にEOF close と
explicit comma/semicolon recoveryを追加した。opening/post-item EOFはclose `Missing`一件、accepted separator直後の
EOFはitem `Missing`一件とdistinct close `Missing`一件を置く。leading/repeated separatorはeach one Missing item後に
same positionからretryし、matching `)`が実在するtrailing separatorはvalidのままにする。post-separator triviaはnext
item/close/missing itemを判定してowner直下へ一度だけemitする。state/source reread/buffer/recovery recordの追加なし。
M1 specification review はclean、focused rewrite testsは54 passed、package check、format/diff checkはgreen。wrong close、
invalid item retry、same-line missing separator、layout/other remaining type recovery、production wiring、Gate 4/G4b ledgerは
未完である。

2026-09-04: standalone `TypeExpression`へnormal-only `NamedRecordType` primaryを追加した。type-local lone
`:` scannerを既存 expression punctuationから分離し、plain `Identifier : TypeExpression` field、comma / captured-base
implicit newline sequence、actual `}`だけでvalidになるtrailing commaをdirect Rowanで構築する。opening/field-boundary
triviaはrecord直下、name-to-colon/colon-to-RHS triviaはfield直下に一度だけ置き、`F {a: A}`はTypeApply、`F{a:A}`は
record tailにせずhandoffする。state/source reread/buffer/recovery recordの追加なし。これはvalid surfaceだけで、record
field/close/separator recoveryとsame-line field-head boundary queryは未実装。M1 specification reviewはclean、focused
rewrite testsは56 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: standalone `TypeExpression`へnormal-only contextual `ForallType` primaryを追加した。exact maximal
`for`はcanonical type-NUDだけで`ForKw`になり、TypeApply LEDではordinary Identifierのままにする。apostrophe-prefixed
SigilIdentifierだけをnon-empty bounded trivia付きbinderとして各`ForallTypeBinder`へemitし、colon/body gapはForall owner、
recursive canonical bodyはnested TypeExpressionが所有する。raw forallはbody exitを直接returnしてouter tailへ戻らず、
groupを通したときだけouter pathなどを付けられる。state/source reread/buffer/recovery recordの追加なし。これはvalid
surfaceだけで、binder/colon/body recoveryは未実装。M1 specification reviewはclean、focused rewrite testsは58 passed、
package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: standalone `TypeExpression`へnormal-only `EffectRowType` primaryを追加した。type-local exact adjacent
`"'["` probeはfailureでinputを動かさずapostropheだけをItemにし、ownerがadjacent `[`をdirectにconsumeする。rowは
parameterized direct type-delimited ownerでcomma/semicolon/captured-base implicit newline/actual matching `]` trailing
boundaryを共有し、full canonical TypeExpression itemをflat source orderで保持する。effect rowはnonterminal primaryなので
ordinary TypeApply/path/arrowへ戻る。exact `for`/lone `:` probeもraw suffix check + `rb().with_str`へ直し、ParserOnce
non-match契約を満たす。state/source reread/buffer/recovery recordの追加なし。これはvalid surfaceだけで、effect-row
recoveryは未実装。M1 specification reviewはclean、focused rewrite testsは60 passed、package check、format/diff checkは
green。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: standalone `TypeExpression`へnormal-only `PolymorphicVariantType` primaryを追加した。type-local exact
adjacent `":{"` probeはcomplete pairをrawで確認してcolonだけをItemにし、ownerがadjacent `{`をdirectにconsumeする。
outer tag listはplain `Identifier`、comma / captured-base qualifying implicit newline、actual `}`だけを受け、tag直下の
payloadはnon-empty same-line triviaだけをboundaryとしてfull type-ML `TypeExpression`を`PolymorphicVariantPayload`へ
保持する。physical newlineはpayload列を必ず終えてouter tag listへhandoffし、nested call内のnewlineはnested ownerへ
留まる。variantはnonterminal primaryなのでordinary TypeApply/path/arrowへ戻る。state/source reread/buffer/recovery
recordの追加なし。これはvalid surfaceだけで、tag/payload/close/separator recoveryは未実装。M1 specification reviewはclean、
focused rewrite testsは62 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: standalone `TypeExpression`へnormal-only bare `BracketRow`を追加した。`[`はfresh type slotでは
leading rowを先にdirectに構築してone enclosing TypeExpressionのmandatory headへ付き、operand-complete tailでは
TypeApplyより先にargument-effect rowとして`TypeArrowTail`へ入る。両位置のrow item listは既存のparameterized
type-delimited ownerを共有し、comma / semicolon / captured-base implicit newline / actual `]`をそのまま使う。leading
rowのhead、arrow RHS、delimited item、record/forall/poly payloadのfresh slotは同じdirect NUD dispatchを使い、type-ML
scopeもleading rowを経て保持する。state/source reread/buffer/recovery recordの追加なし。これはvalid surfaceだけで、
leading head、row close/item、mandatory arrowのrecoveryは未実装。M1 specification reviewはtype-ML propagation修正後
clean、focused rewrite testsは63 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは
未完である。

2026-09-04: direct `BracketRow` tailへBR-Aのnormal-boundary mandatory-arrow recoveryを追加した。actual arrowは
existing TypeArrow RHS recursionを共有し、arrowなしでnext TypeExpression candidateがある場合はone Missing arrowから
RHSをretryする。EOF / comma・semicolon / outer closeはarrow Missingだけを置いてboundaryをhandoffし、equal-or-shallower
newlineもzero-width Missing後にunconsumedで返す。state/source reread/buffer/recovery recordの追加なし。malformed arrow
run、missing head、row item / close recoveryは未実装。M1 specification reviewはclean、focused rewrite testsは64 passed、
package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct leading `BracketRow`へBR-Hのnormal-boundary mandatory-head recoveryを追加した。row後のvalid
non-bracket TypePrimaryはexisting outer TypeExpression内でそのまま読む一方、EOF / outer closeはone Missing headを置き、
equal-or-shallower newlineはzero-width Missing後にunconsumedでcallerへ返す。second `[`はleading-row recursionにせず
head recoveryへ残す。state/source reread/buffer/recovery recordの追加なし。disabled second row / malformed head recoveryと
row item / close recoveryは未実装。M1 specification reviewはclean、focused rewrite testsは65 passed、package check、
format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct leading `BracketRow`のdisabled second-row BR-H recoveryを追加した。matching `]`がsink-free
balanced probeで確定した`[e][f]T`だけをone `Error`へまとめ、second `BracketRow`を作らず同じhead slotから`T`へ
retryする。probeはnested `[`とtrivia/commentをopaqueに扱い、matching closeのないsecond `[`はErrorを作らずhandoffする。
state/source reread/buffer/recovery recordの追加なし。malformed head / row item / close recoveryは未実装。M1 specification
reviewはclean、focused rewrite testsは66 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b
ledgerは未完である。

2026-09-04: direct leading `BracketRow`のBR-H malformed-head retryを追加した。row-to-head accepted chain triviaは
enclosing TypeExpressionが所有し、maximal malformed bytesだけをone `Error`としてvalid non-bracket TypePrimaryへretryする。
malformed runがEOF / outer boundary / equal-or-shallower newlineへ着いた場合はsame head slotへMissingを重ねずhandoffする。
state/source reread/buffer/recovery recordの追加なし。malformed run後のdisabled second row統合とrow item / close recoveryは未実装。
M1 specification reviewはownership修正後clean、focused rewrite testsは67 passed、package check、format/diff checkはgreen。
production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: shared direct type-delimited loopへowner-local `BracketRow` policyを追加し、initial malformed itemと
local mismatched closeのBR-R retryを実装した。`T [@ A] -> U`はsame-line gap込みone `Error("@ ")`からitem `A`へretryし、
`T [)] -> U`はone Missing item + one close Error、`T [e)] -> U`はclose Errorだけでactual `]`へretryする。Generic owner
(EffectRow / call / group)のbranchは変えない。terminal malformed itemはitem Missingを重ねずclose Missingだけを置く。
state/source reread/buffer/recovery recordの追加なし。post-item malformed / separator / layout recovery、repeated close、
incomplete close後のmandatory arrow/head continuationは未実装。M1 specification reviewはclean、focused rewrite testsは68 passed、
package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: `BracketRow`の残るBR-R post-item / terminal continuationを追加した。complete item後のdeeper newline
valid primaryはzero-width Missing separatorを置いてnext itemとしてretryし、deeper newlineのmalformed followerはErrorへ
consumeせずclose Missingだけを置いてunconsumed handoffする。same-line malformed post-itemは既存のone Error retryを使い、
`,`へ到達したmalformed runもMissing itemを重ねずnext itemへ進む。incomplete row EOFはclose Missingに加え、leading rowでは
mandatory head、tail rowではmandatory arrowのMissingを各owner内に置く。Generic owner (EffectRow / call / group)は不変。
state/source reread/buffer/recovery recordの追加なし。M1 specification reviewはclean、focused rewrite testsは68 passed、package
check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: `BracketRow` BR-R の残るzero-length / close-slot収束を完了した。open直後のEOFはitem / close /
tail arrowの3 distinct Missing、separator直後のlocal mismatched closeはnew item Missing後のclose Error、complete item後の
local mismatched closeはfurther mismatchまたはactual `]`だけをretryする。後者がcaller-owned equal-or-shallower newline、
outer follower、EOFへ達したときはitem loopへ戻らずclose Missingを置いてhandoffするため、newlineはrow外に残る。malformed
itemのsame-line / newline / comment run、repeated wrong close、actual closeへのupgrade、terminal Missingの全traceをdirect
CST fixtureで固定した。Generic (EffectRow / call / group) close behaviorは不変。state/source reread/buffer/recovery record
の追加なし。M1 specification reviewはnewline ownership修正を含め2巡clean、focused rewrite testsは69 passed、package check、
format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: shared direct type-delimited item retryを一般ownerにも追加した。`TypeCallTail` /
`ParenthesizedTypeGroup` / `EffectRowType`のinitial itemまたはliteral separator直後のmalformed runは、same-line /
deeper triviaを含むone `Error`からvalid Type NUDへsame slot retryし、literal separatorなら次item slotへ、actual matching
closeならincomplete itemを重ねずcloseをそのownerが読む。EOFはErrorの後にdistinct close Missingを置く。mismatched closeは
direct standalone entryにouter-delimiter authorityがまだ無いため、一切consume / Error化せずpending `Item`のままhandoffする。
BracketRowも同じhelperへ畳んだが、BR-RP1のitem Errorとclose Errorのtrivia/range ownershipは不変に保った。state/source
reread/buffer/recovery recordの追加なし。M1 specification reviewはcompile-blocker修正とBR-RP1 range deltaを含めclean、focused
rewrite testsは70 passed、package check、format/diff checkはgreen。generic mismatched-close retry、complete item後のmalformed
gap / missing separator、other type owner recovery、production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`でaccepted field name後のmandatory colon / RHS recoveryを追加した。same-line valid
Type NUD（contextual `for`を含む）はone Missing colonからsame field RHSへretryし、comma / close / EOFはone Missing colonだけで
fieldを閉じてno-cascadeを守る。accepted colon後のcomma / close / EOF、またはequal-or-shallower record newlineはone Missing
RHSを置いてpending Itemをsequence ownerへ返す。same-line field triviaはMissing node、shallow newline triviaはrecord sequenceに
残る。`}`はrecord ownerが引き続きconsumeし、`)` / `]`はhandoffする。malformed colon / RHS retry、missing-name skeleton、
whole-field sequence error、semicolon、record close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの
追加なし。M1 specification reviewはclean、focused rewrite testsは71 passed、package check、format/diff checkはgreen。production
wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のfresh field slotでliteral colonから始まるmissing-name skeletonを追加した。`{: A}`、
explicit comma後、qualifying implicit newline後の`:`はrecord直下にgap triviaを残して`TypeRecordField`を開始し、zero-width
Missing name一件、literal colon、canonical RHSを順に所有する。`{:}`はname と RHS のdistinct Missingを持つ。既存fieldのRHS
judgeをshared helperへ抽出したがnormal / boundary branchは変えない。malformed-name skeleton、leading/repeated separator、
whole-field sequence error、semicolon、record close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの
追加なし。M1 specification reviewはclean、focused rewrite testsは72 passed、package check、format/diff checkはgreen。production
wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のaccepted name後にmalformed colon slot retryを追加した。`@` / exact longer `::`
などはname-to-slot triviaをfield直下へ残したうえでnon-empty one `Error`になり、literal colonならRHS slotへ、valid Type NUD
ならrecovered-missing colonとしてsame field RHSへretryする。shallow newline / comma / close / EOFへ到達したErrorはboundaryを
consumeせず、same slotへMissing colonを追加しない。malformed-name / RHS retry、whole-field sequence error、semicolon、record
close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。M1 specification reviewはrange修正を
含め2巡clean、focused rewrite testsは73 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは
未完である。

2026-09-04: direct `NamedRecordType`のaccepted colon後にmalformed RHS slot retryを追加した。colon-to-RHS triviaをfield直下へ
置いてからshared type RHS retryを使うため、`@`はexact one `Error`になりvalid Type NUDへsame slot retryする。retryが返すitemも
layoutを再判定し、deeper newlineはRHS continuation、shallow newlineのfield headはrecord sequenceへhandoffする。comma / close /
EOFへ着いたErrorはadditional Missing RHSを作らない。malformed-name / colon / RHS sequence recoveryの残り、semicolon、record close /
next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。M1 specification reviewはclean、focused rewrite
testsは74 passed、package check、format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のleading / repeated comma recoveryを追加した。commaごとにrecord直下へ
zero-width Missing field一件を置き、次field slotをsame-positionでretryする。accepted field後とleading/repeated位置は
shared post-comma continuationを通り、matching `}`だけがvalid trailing commaとしてraw triviaとcloseをrecordが所有する。
EOF / `)` / `]`はpost-comma triviaをMissing fieldへ置き、boundaryをunconsumed handoffするためtrailing commaと
混同しない。literal-colon missing-name skeletonもpost-comma field startとして従来通り受ける。whole-field sequence
error、semicolon、record close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。
M1 specification reviewはEOF/outer-close Missing fieldの修正後clean、focused rewrite testsは76 passed、package check、
format/diff checkはgreen。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のmalformed-name colon skeletonを追加した。plain Identifierを含まない
same-line malformed runの直後にrecord depthのliteral colonがある場合だけ、`TypeRecordField`内のname `Error`から
colon / canonical RHSをsame fieldで続行する。sigil / number / punctuation runを含み、nested delimiter内のcolonは
outer field colonにしない。physical newline、plain Identifier、separator / close / EOFではlocal probeをrollbackして
initial Itemをwhole-field sequence recoveryへhandoffする。probeはunit-state `LexIn`でlocal suffixだけを読み、shared
trivia/type-item scannerはstate-generic化してdirect parserと同じlexical spellingを使う。whole-field Error retry、semicolon、
record close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。M1 specification reviewは
AnyPhysicalHandoff / current-depth修正後clean、focused rewrite testsは77 passed、package check、format/diff checkはgreen。
production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`でaccepted field後のinvalid semicolon separator recoveryを追加した。field-to-
semicolon gapはrecord直下、semicolonからcurrent-depth malformed runまではone record-level `Error`で所有し、depth-zeroの
field start / comma / matching `}`だけへretryする。inner closeとそのleading newlineはrecord boundaryにせずError内へ残す。
EOF / outer close / qualifying newlineはunconsumed handoffで、record close recoveryはまだ追加しない。leading semicolonと
whole-field sequence error、record close / next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。
M1 specification reviewはnested-close newline修正後clean、focused rewrite testsは78 passed、package check、format/diff checkは
green。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のclose Missing recoveryを追加した。opening直後 / accepted field後 / invalid semicolon
recovery後のEOFまたはouter mismatched closeはrecord-local close Missing一件を置き、outer close tokenはunconsumed handoffする。
comma-before-boundaryはfield Missingとclose Missingをdistinctにし、actual matching `}`だけがvalid trailing commaを閉じる。
leading semicolon、whole-field sequence Error、next-field owner queryは未実装。state/source reread/buffer/recovery recordの追加なし。
M1 specification reviewはclose-cardinality確認を含めclean、focused rewrite testsは79 passed、package check、format/diff checkはgreen。
production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `NamedRecordType`のwhole-field sequence Error retryを追加した。malformed-name local probeが
colon skeletonを認めないrunはrecord直下のone `Error`として読み、same-lineまたはrecord baselineより深いnewlineを
挟むcomplete `name:` / literal `:`へretryする。retry gapのtriviaはErrorへ含めずrecordが直接所有し、`{@\n  a: A}`は
`Error("@")`とone `TypeRecordField`になる。equal-or-shallower newlineはouterへhandoffし、comma / actual `}` / EOF /
outer closeはそれぞれ既存のsequence / close ownerへ戻す。旧malformed-name unit testに残っていたpre-whole-fieldの
handoff expectationは、Authoritative field-authority cutと矛盾するため削除した。source/state reread/buffer/recovery
recordの追加なし。M1 specification reviewはcontinuation policyとtest-contract deltaともclean、focused rewrite testsは81
passed、package check、format/diff checkはgreen。leading semicolon / next-field owner query、production wiring、Gate 4/G4b
ledgerは未完である。

2026-09-04: direct `NamedRecordType`のfresh field slotでもleading semicolonをaccepted field後と同じ
record-level separator recoveryへ明示的にrouteした。semicolon前のtriviaはrecord直下、`;`だけはone `Error`、後続の
field / comma / matching `}`は既存ownerが再開する。`{;b: B}`と`{;}`でfield Missingを重ねないことを固定した。
next-field owner query、production wiring、Gate 4/G4b ledgerは未完である。state/source reread/buffer/recovery recordの
追加なし。M1 specification reviewはclean、focused rewrite testsは81 passed、package check、format/diff checkはgreen。

2026-09-04: direct `NamedRecordType`のsame-line next-field owner queryを追加した。accepted field RHSだけへ
`record_base: Option<usize>`を明示的に引き回し、TypeApply accept直前でsame-line complete `Identifier … Colon`を
sink-freeに見つけたときはcandidateをhandoffする。record sequenceがgap triviaを直下へ一度emitし、zero-width Missing
separator一件を置いてnext fieldをretryする。`{a: F b: B}`はtwo fields + one Missing separatorでRHS `F`を止め、
`{a: F B}`はone fieldのordinary TypeApplyのまま保つ。nested delimiter / ML argumentにはrecord baseを渡さず、
enclosing continuation後だけouter RHS contextを再開する。production wiring、Gate 4/G4b ledgerは未完である。
 state/source reread/buffer/recovery recordの追加なし。M1 specification reviewはclean、focused rewrite testsは82 passed、
package check、format/diff checkはgreen。

2026-09-04: direct `ForallType`のclean mandatory slot recoveryを追加した。exact `for` cut後、first binder / colon /
bodyをそれぞれzero-widthまたは同positionのMissing一件で補い、`for` EOFはbinderだけ、`for 'a` EOFはcolonだけ、
`for 'a:` EOFはbodyだけをMissingにする。colon直前のfirst-binder slotはそのcolonのbounded triviaをbinderへ置き、
adjacent binder (`for'a`)だけはactual binderと別のMissing boundaryを持つ。non-binder Type NUDはcolon Missingを置いて
body slotへretryする。equal-or-shallower newlineはfirst-binder Missingより外側へunconsumed handoffし、rootのEndが
newlineを所有する。malformed binder / colon / body run、punctuation recoveryは後続sliceへ残す。production wiring、Gate
4/G4b ledgerは未完である。state/source reread/buffer/recovery recordの追加なし。M1 specification reviewは
first-binder newline-owner delta後clean、focused rewrite testsは83 passed、package check、format/diff checkはgreen。

2026-09-04: direct `ForallType`のmalformed binder / colon / body run recoveryを追加した。first-binder phaseは
non-apostrophe candidateをone incomplete `ForallTypeBinder`内のErrorとして読み、depth-zeroのlater apostrophe binderまたは
literal colonだけへretryする。accepted binder後はsink-free unit probeがlater retry targetをbinder対colon/bodyで先に分け、
ErrorのCST homeをincomplete binderまたはForall direct childへ一意に決める。malformed colon Errorからnon-binder bodyへ
retryするときはsame-causeのMissing colonを重ねず、literal colon bodyのmalformed runもone Errorだけでcandidate / boundaryへ
戻す。all recovery scannerはcurrent delimiter depthだけをjudgeし、inner colon / binder / shallow newlineをouter retryや
indentation decisionへ混ぜない。comma / semicolonのown-vs-outer owner distinctionは未実装の次sliceである。production wiring、
Gate 4/G4b ledgerは未完である。state/source reread/buffer/recovery recordの追加なし。M1 specification reviewは
two repair delta後clean、focused rewrite testsは84 passed、package check、format/diff checkはgreen。

2026-09-04: Forall punctuation residualを解消した。rootは`outer_separators = false`、generic delimiter item・
NamedRecord RHS / recovery entry・PolymorphicVariant payloadは`true`をexplicitに渡し、TypeExpressionのtailと
ML-applicationは受け取ったcapabilityをそのまま伝播する。Forall内部ではactive outer ownerのcomma / semicolonだけを
zero-width Missingとunconsumed handoffにし、root local separatorはphase別のexact `ForallTypeBinder > Error` recoveryとして
consumeする。FirstBinderはseparator後のnon-binder NUDをbodyへ昇格させず、BinderOrColonだけが既存colon/body judgeへ戻る。
leading triviaもouter separatorと一緒にcallerへ返す。global `is_type_rhs_boundary`とRecover stateは変更していない。
root / delimiter / NamedRecord comma・semicolon / polymorphic-variant payload / body phase / comment handoffのCST fixtureを追加し、
focused rewrite tests 89 passed、package check・format・diff check green、独立spec review approved。

2026-09-04: standalone direct `TypeExpression`のsource ownerを責務単位で分割した。`type_expr.rs`は
entry / primary dispatch / fixed tails / shared boundary predicatesだけを残し、`type_expr/record.rs`がNamedRecord、
`type_expr/forall.rs`がForall、`type_expr/variants.rs`がEffectRowとPolymorphicVariant、
`type_expr/delimited.rs`がgeneric delimiterとBracketRow recoveryを所有する。Recovery state・入力形式・CST node
order・テスト契約は変更せず、移動した各4 owner bodyは旧sourceとvisibility修正を除いてbyte一致を機械照合した。
focused rewrite tests、package check、format/diff checkを実行し、独立delta reviewもclean。

2026-09-04: direct `PolymorphicVariantType`のouter tag-position `NT`を部分実装した。`outer_closes: u8`を
direct TypeExpressionの再帰引数だけでthreadし、generic delimiter・NamedRecord・PV自身が自身のclose spellingを加える。
PVはmaskにあるactive closeをleading triviaごとunconsumedで返し、local mismatched closeだけをPV直下のErrorとして
retryする。このため`F({a: :{A)`はPV Missing close→record Missing close→call `)` consumeの順になる。`NT-1..5/7`
(actual/local-or-outer close、commaのunfilled/filled slot、local/outer semicolon、qualifying/deeper newline、EOF)を
`TagPosition`だけでowner-localに処理し、`NT-6/8`と`IT` malformed recoveryは未実装のまま残した。comma / newline / EOF、
root local close / semicolon、nested active close、space有無を含むcaller-owned semicolon、local Errorとborrowed boundaryの
leading-trivia direct-CST ownershipをfixture化した。M1 spec reviewはevidence repair後approved、focused rewrite tests 93 passed、
package check・format・diff check green。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `PolymorphicVariantType`のcanonical `NT-6`を追加した。tag slotでIdentifier以外の
Type NUDを一度だけcanonical primaryとして読み、同じ`PolymorphicVariantTag`内の
`Error > TypeExpression`へ候補全体を置く。`type_ml = true`、`record_base = None`、
`outer_separators = true`、active `outer_closes`はpayloadと同じ明示引数で渡し、返ったitemはnormal tagと
共通のpayload judgeへそのまま渡すため、spaced payload・comma・newline・local closeのownerは変えない。
numeric / forall / nested PV candidate、comma/newlineのrecovered tag position、disjoint local-close Errorを
fixture化した。`NT-8`と`IT` malformed recoveryは未実装のまま残した。M1 spec review approved、focused rewrite
tests 94 passed。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: `NT-8` Error後のsame-slot retry trivia ownerに、Rowanのcontiguous CSTとone recovered tag
contractが衝突することをM1 spec reviewで発見した。ユーザー承認済みAuthoritative追補
`2026-09-04-yu-syntax-pv-nt8-same-slot-trivia-amendment.md`が、same-line `NT-6` candidateのleading triviaを
preceding Errorから除き、既に開いた`PolymorphicVariantTag`のdirect childと定める。他のcomma / close /
semicolon / EOF / newline safe-point gapはexisting outer `NT` / caller ownerのまま。次はこの追補に従う
direct `NT-8` implementationであり、`IT-4`は引き続きdeferする。

2026-09-04: direct `PolymorphicVariantType`の`NT-8` malformed tag-prefix recoveryを追加した。one
`PolymorphicVariantTag > Error`でmaximal prefixを読み、same-line `NT-6` candidateだけをそのtag内へretryする。
approved same-slot trivia追補どおりcandidate前のgapはError外・Tag直下、comma / semicolon / close / EOF /
physical newline前のgapはpending Itemのままouter `NT`へ返す。normal Identifier / wrong-kind primaryは同一tagの
shared head / payload pathへ入り、`:{@123 Int}`相当のprefix Error・TagName Error・payloadにsecond tag / Missingを
作らない。normal / wrong-kind retry、comma・newline state、local / caller separator・close、deeper newline handoffを
fixture化した。M1 spec review approved、focused rewrite tests 95 passed、package check・format・diff check green。
`IT-4` malformed payload recoveryは引き続きdeferする。production wiring、Gate 4/G4b ledgerは未完である。

2026-09-04: direct `PolymorphicVariantPayload`の`IT-1`〜`IT-3`と、nonempty same-line boundaryを既に
受理した場合に限る`IT-4` recoveryを追加した。adjacent canonical payloadはzero-width
`Missing(PolymorphicVariantPayloadBoundary, TypePayloadBoundary)`を先頭に置き、nonempty boundary後の
malformed runは`Payload > Error`へmaximalに置く。same-line type candidateの前のgapはPayload直下・
Error外、newline / comma / semicolon / close / EOFとその前のgapはpending Itemのままouter `NT`またはcallerへ
返す。`IT-4`の**empty-boundary malformed prefix**（例 `:{A@Int}`）は未実装のまま残す。現在のone-way
direct runnerでは、既に保持した最初の不正Itemを後続candidateとouter safe pointのどちらへ分類するかを、
bufferまたは禁止済みmulti-token rollbackなしには決められない。これは既存Authoritative `IT-4`の最終形を
task記録だけで変更できる問題ではないため、恒久解決にはユーザー承認済み追補が必要である。M1 spec review
approved、focused rewrite tests 96 passed、package check・format・diff check green。production wiring、
Gate 4/G4b ledgerは未完である。

2026-09-04: standalone direct `Pattern`のnormal constructionを追加した。source/root/cursor・token/event
buffer・ambient parser stateを持たず、入力`Item`を一方向にhandoffする直接Nud/tailとして、identifier/
sigil/integer/symbol、parenthesized/list/record、spread・record field/default、`as`・`|`・`:`の固定tailを
実装した。`PatternSymbolColon`はNudだけで`:identifier`を一tokenとして認識し、tail/callerのbare colonは
奪わない。newline baseはleading triviaをCSTへ移す前にscalar一個としてcaptureして再帰引数でのみ渡し、
annotationのpre/post gap、alternation RHS gap、delimiter/field/spread gapはそれぞれのdirect CST ownerへ
emitする。M1 specification delta reviewでこのtrivia ownerとequal/deeper newline baseを査読し、focused
Pattern tests 5 passed、`cargo check -p yu-syntax`、format/diff checkはgreen。Pattern recovery P1〜P8・
RB-P、malformed type RHS、production wiring、AST parity、Gate 5 certificationは未実装であり、この記録は
normal constructionの途中経過だけを表す。

2026-09-04: direct `Pattern`のP1〜P4 mandatory recoveryを追加した。primary / alias bindingのnonempty
malformed runは一個の`Error`でsame slotのnormal Nudだけをretryし、retry gapだけをErrorへ移す。一方、EOF・
comma・close・active colon stop・qualifying newlineなどcaller boundaryはleading triviaを含むpending `Item`のまま
handoffし、current `as` / `|` / non-active colon tailへはrecovered Patternを開いたまま再入する。aliasはaccepted
`as`直後のboundaryだけone `Missing`、nonempty Error後のboundaryはError-onlyで閉じ、same-cause cascadeを作らない。
M1 specification reviewはtwo repair deltas後approved。focused Pattern testsは7 passed、P1 `Error("@ ")`、P2
one Missing、P3 initial-Missing/post-Error split、P4 nested Missing/tail、caller gap handoffをexact CSTで固定した。
P5〜P8、production wiring、AST parity、full RB-P/Gate 5 certificationは未完である。

2026-09-04: direct `Pattern`のP5/P6 parenthesized/list delimiter recoveryを追加した。Parenthesized / Listの
mandatory item positionは直接`Pattern`へ委譲し、P1のnonempty Error / same-slot retry / boundary handoffをそのまま
再利用する。list spread `..`のRHSも常にnested `Pattern`へ委譲するため、close / commaではone Missing、`@tail`では
one Error後に`tail`を同じRHS slotへretryする。accepted delimiterのEOF closeとleading triviaはdelimiter ownerに
留め、shared `missing_close`とRecordの既存item/field pathは変更していない。P5 `(,a)` / `(a b)` / `(a]` / `(a`、
P6 `[,a]` / `[a b]` / `[..]` / `[..,a]` / `[..@tail]` / `[a`、`[a, @ b]`、`[...,a]`をexact direct CSTで
固定した。M1 specification reviewはinitial evidence gap（literal EOF、malformed ListItem retry、non-split marker）を
一回のtest-only repairで閉じてapproved。focused Pattern tests 9 passed、`cargo fmt --all -- --check`、
`cargo check -p yu-syntax`、diff checkはgreen。P7/P8、consumer / outer-arrow recovery、production wiring、AST parity、
full RB-P/Gate 5 certificationは未完である。

2026-09-04: direct `Pattern`のP7 Record recoveryを追加した。colon nested-patternとrecord spread RHSは
直接`Pattern`へ委譲してP1のError/retryを再利用するため、`{a: @}`はone nested Errorのみ、`{a: @ p}` / `{..@tail}`は
same slotでvalid primaryへretryし、Missing cascadeを作らない。colon RHSのexact `=` handoffはfieldだけがconsumeし、
`{a: = 1}`はnested Pattern Missing、raw Equals、default `OperatorChain(1)`を同じfieldに保持する。exact `..` / `=`を
rejectしたoperator-shaped continuationだけは一Unknownにまとめ、`.`の既存Dot分類を変えず、`{...a}`、`==` / `=>` / `=+`を
prefix splitしないone Errorへ固定した。Record post-item Error後はitem-required phaseへ直接retryするため、`{a; b}`と
rejected-equals casesはone Error、two fields、zero Missingになる。P7a〜P7gと上記retry / non-split / punctuation controlを
direct CSTで固定し、M1 specification reviewはone repair round後approved。focused Pattern tests 10 passed、
`cargo fmt --all -- --check`、`cargo check -p yu-syntax`、diff checkはgreen。P8、consumer / outer-arrow recovery、
production wiring、AST parity、full RB-P/Gate 5 certificationは未完である。

2026-09-04: direct `PatternTypeAnnotation`のisolated P8 mandatory TypeExpression recoveryを追加した。
annotationはType vocabularyでfirst Itemを一度だけ取り、Type側の`required_type_expr`が正常Nud、mandatory boundary、
malformed primary Errorとsame-slot retryを直接裁定する。EOF・comma・semicolon・three close・exact `=`・
equal/shallow newlineは`TypeExpression > Missing`だけを作り、boundary Item（leading triviaを含む）は未消費でhandoffする。
`==`などlonger `=` spellingはone Type-primary Errorとして読み、valid type Nudがあればsibling TypeExpressionへretryする。
Error後のretry leading triviaはErrorにもannotationにも移さず、retried TypeExpression自身が所有する。M1 specification
reviewはこのtrivia owner gapをone repairで検出・修正しapproved。focused Pattern tests 11 passed、
`cargo fmt --all -- --check`、`cargo check -p yu-syntax`、diff checkはgreen。active outer Arrowをcaller boundaryにする
consumerはまだ存在しないため、この入口はArrow policyを発明しておらず、consumer / outer-arrow recovery、production wiring、
AST parity、full RB-P/Gate 5 certificationは未完である。

2026-09-04: source-free direct expressionに、dynamic Prefix / Infixを受理した後のnarrow mandatory
operand recoveryを追加した。normal operator scannerがvalue-start不足で不受理にした場合だけ、同じcanonical
all-spelling trieのlonger-to-shorter recovery probeでcurrent NUDのPrefixまたはcurrent LEDのInfix roleが一意に
決まるときに受理する。EOF / active delimiter stopにはretained leading triviaを`Missing`へ一回だけ置き、invalid
`Item` runはone `Error`へまとめてnext Nudを同じoperand slotにretryする。boundaryまでならError sentinelだけで
`Missing`を重ねない。equal-or-shallow newline、colon / equal / other structural starter、non-active closeは
unacceptedのままhandoffし、generic colon/equal vocabularyやterminal ownerは追加していない。M1 specification reviewは
pre-writeとone repair deltaでapprovedとなり、shallow newlineをEOFより先にboundaryとして判定する修正を含む。focused
 rewrite operator tests 11 passed、`cargo check -p yu-syntax`、format/diff checkはgreen。この記録はdirect
CST/remainderだけのisolated evidenceであり、diagnostic/recovery identity、AST parity、production wiring、G4a/RB-E、
Gate 4 certificationは未実装である。

2026-09-04: isolated SCC construction witnessとしてdirect expressionのC1 lone-colon tailを追加した。operand-complete
かつML argumentでないLEDで、pre-colon triviaがchain-continuationであり、source-onlyのsame-line direct normal core
probe（Identifier / Integer / `(`）が成功した場合だけ`ColonApplicationTail`をcommitする。colon-leading triviaはouter
`OperatorChain`直下、post-colon horizontal triviaとcolon-own same-line commaはtail直下に置く。rootの`f: x, y`はtwo RHS
chain、active outer commaを持つ`(f: x, y)`はone RHSのままcommaをparentへhandoffする。accepted tailはterminalで
predecessorをwrapしない。`::`は`PathTail`のまま、exact `with:`はfuture `WithBodyTail`へreservation handoffする。colonや
colon-owned commaの前にはsource-only probeを置き、EOF / post-colon newline / invalid initial RHSではcolonを、trailing
comma / newline-after-comma / invalid next RHSではcommaをunconsumed handoffするため、Missing/Error recoveryを暗黙に
実装していない。M1 specification reviewはone repair delta後approved。focused rewrite tails tests 7 passed、
`cargo check -p yu-syntax`、format/diff checkはgreen。これはC1 inline normal constructionだけであり、dynamic prefix
initial RHS、layout newline argument、`IndentedStatementBlock` / canonical `Statement`、mandatory recovery、diagnostic / AST
parity / production wiring、G4a RB-E / Gate 4は未実装である。

2026-09-04: isolated SCC construction witness C2として、direct colon tailから呼ぶnormal-only
`IndentedStatementBlock`とreusable `Statement > OperatorChain` calleeを追加した。colonはsource-only unit parserで
post-colon maximal triviaを観測し、newlineのfinal indentationがexpression baselineよりstrictly greaterで、Identifier /
Integer / `(`のdirect coreが続くときだけC2をcommitする。blockはpost-colon opening trivia全体を直接所有し、各statementを
block indentationでdirect expressionへ渡す。equal-indentで返ったnormal core Itemだけを`BlockStatementSeparator`として
emitし、dedent・deeper continuation・invalid startはleading triviaを含むItemをunconsumed handoffする。深い行は同一
statementの`MlArgument`のままでsiblingにしない。semicolon、dynamic prefix / nullfix block start、newline colon-inline
arguments、declaration等のStatement variant、Missing / Error recovery、AST / diagnostic / production wiringは追加していない。
M1 specification reviewはpre-write / post-writeともapproved。focused rewrite tails tests 9 passed、`cargo check -p
yu-syntax`、format/diff checkはgreen。これはcanonical Statement / colon recoveryの完了を主張せず、G4a RB-E / Gate 4は
未実装のままである。

2026-09-04: isolated SCC construction witness C3として、direct expressionの`LBrace` Nudから
`BracedStatementBlockExpression`を追加した。privateな`StatementSequencePolicy::{Indented, Braced}`だけでC2と
statement start・normal successor・separator emissionを共有し、source/root/cursor・token/event buffer・ambient contextは
導入していない。brace ownerはlocal stop `{Comma, Semicolon, RBrace}`でouter stopを遮断し、空 block、opening trivia、direct
normal statement、comma / semicolon / current-depth newline separator、trailing separator、matching closeを直接所有する。
`{x: 1, y: 2}`のcommaはcolon RHSではなくbrace sequenceのseparatorであり、record CSTは作らない。accepted `{`はEOF時に
owner-local `Missing` closeを一つ置き、invalid runとmismatched `)` / `]`はbrace-local one `Error`にしてmatching `}`まで
進める。returned newlineはblock baseline以下だけがseparatorで、deeper newlineはexpression continuationのまま残す。
M1 specification reviewはboundary repair後approved。focused rewrite tails tests 11 passed、`cargo check -p yu-syntax`、
format/diff checkはgreen。declaration / dynamic Prefix・Nullfix statement start、colon mandatory recovery、AST / diagnostic /
production wiring、G4a RB-E / Gate 4は未実装のままである。

2026-09-05: isolated SCC construction witness C4として、eligible lone `:`をdirect `ColonApplicationTail`として
commitした時点でRHS mandatory slotをowner-localにtotal化した。`::`、`with:`、ML-argument reservationは従来どおり
unconsumedで、post-colon source probeはstrictly-deeper newlineによる`IndentedStatementBlock`選択だけに限定した。
inlineは既存direct `is_nud_item`（normal core、brace primary、accepted Prefix / Nullfix）を`OperatorChain` RHSとして
受理し、EOF / horizontal EOF / shallow newline / outer separator・closeにはone `Missing`、nonempty invalid runにはone
`Error`とsame-slot retryを置く。Error後のhorizontal triviaもtailが所有し、shallow newlineだけはouter Itemに残す。
colon-owned commaはinitial / trailing argumentともmandatoryであり、outer commaは一RHS後にhandoffする。deep blockは
EOF・invalid first itemでも開始し、normal-core statementのinitial / equal-indent slotを同じMissing/Error recoveryで処理する。
nonmatching closeはblock-local Error、active outer close・dedent・outer separatorはunconsumedである。deep blockの
Prefix / Nullfix statement startは依然deferであり、canonical Statement完了は主張しない。M1 specification reviewは
pre-write・post-write・owner-boundary deltaともapproved。focused rewrite tails tests 11 passed、`cargo check -p yu-syntax`、
format/diff checkはgreen。typed diagnostics、AST / production wiring、dynamic Statement variants、G4a RB-E / Gate 4は
未実装である。

2026-09-05: isolated SCC construction witness C5として、direct generic `WithBodyTail`を追加した。
chain-continuationかつML scope外のmaximal exact `with`をdynamic word operator / ML argumentより先にterminal LEDとして
受理し、pre-`with` triviaはouter `OperatorChain`、`WithKw`以降のintroducer / inline triviaはtail直下に置く。dynamic
tableが`with` spellingをoperatorとしてscanした場合もsource-only suffix probeで`with?` / `with!`をrejectし、exact
`with`だけを`WithKw`へemitする。actual lone colonならinline一 `Statement`またはstrictly-deeper existing
`IndentedStatementBlock`へ入り、inline terminal semicolonはcomplete / Missing / Error body後に限ってtailが所有する。
colonがないaccepted keywordはone Missing colonにcutし、same-line normal coreからbody retryするが、shallow newline、`::`、
`{}`はunconsumed boundaryのままにしてgeneric `with {}`をbraced bodyへしない。inline invalid runはone `Error`にして
same slotでretryし、nested colon / withはbody `Statement`側へ入る。tailはterminalでouter chainにlater tailを追加しない。
M1 specification reviewはinitial planのmissing-colon brace / semicolon ownership gapとpost-writeのoperator suffix /
shallow-newline / semicolon gapをone repair roundで閉じてapproved。focused rewrite tails tests 11 passed、
`cargo check -p yu-syntax`、format/diff checkはgreen。current direct Statement subset以外のdeclaration / Prefix /
Nullfix statement、typed diagnostics、AST / production wiring、G4a RB-E / Gate 4は未実装である。

2026-09-05: isolated SCC construction witness C6として、source-free direct NUD `IfExpression`を追加した。`if`は
maximal exact wordをNUD scannerでdynamic word operatorより先に受理し、pre-`if` triviaはouter `OperatorChain`、
`IfKw` / `ElsifKw`後のtriviaとcondition-colon間のtriviaはowning `IfArm`へ置く。conditionは必ず
`Condition > OperatorChain`となり、arm colonはdirect childとしてexactly-one inline expressionまたはstrictly-deeper
existing `IndentedStatementBlock`を所有して`ColonApplicationTail`やinline comma listを作らない。normal topologyは
zero-or-more `ElsifKw` sibling `IfArm`、one `ElseArm`、bare `else if`のnested `IfExpression`までを含み、completed
primaryはouter flat chainへ戻る。accepted `if` / `elsif` / `else`はcondition / colon / bodyのmandatory slotをowner-localに
total化し、initial Missing、nonempty Errorとsame-slot retry、wrong-indent handoffをdirect CSTで閉じる。
existing punctuation stop maskだけを`Stops = u16`へ広げ、Colon / LeftBrace / Elsif / Elseはpassed valueとしてcondition /
body / shared block loopへ渡す。word stopはcomplete `Item`とoperator-backed suffix probeでexact maximal spellingだけを
判定し、dynamic / MLより先にhandoffする。nested delimiter ownerは従来どおりown close maskへreplaceするためif-local
word stopを継承しない。raw dynamic-operator followerもlone `:`だけをcondition stopとし、`::`をpath spellingのまま
保つ。If brace body、case/catch、full Statement/declaration、typed diagnostics、AST / HIR / production wiring、G4a RB-E /
Gate 4 certificationは未実装である。M1 specification reviewはpre-writeでaccepted-keyword totality、shared companion
boundary、pre-keyword triviaを補正し、post-writeでcondition wrapper / trivia ownerと`::` raw stopをone repair roundで
閉じてapproved。focused direct if tests 8 passed、existing tails tests 11 passed、`cargo check -p yu-syntax`、format/diff
checkはgreen。

2026-09-05: isolated SCC construction witness C7として、source-free direct NUD `CaseExpression` / `CatchExpression`を
追加した。maximal exact `case` / `catch`はdynamic word operatorより先に受理し、apostrophe-sigil label、mandatory
`CaseLikeScrutinee > OperatorChain`、family-owned blockだけをdirect Rowanで構築する。`CaseLikeFamily`とclosed
`ArmSequencePolicy`はcase inline、catch inline single、両familyのstrictly-deeper indented、catch-only braceを表し、
statement sequenceとは分離した一個のarm loopがPattern・catch handler・`if` / `where` guard・exact `->`・one bodyを
所有する。case scrutineeはcolonだけ、catch scrutineeはcolonとbraceをlocal stopにし、caseがbrace blockを先取りしない。
arrow、guard word、delimiter close、outer punctuationはcaller-owned `PatternStops` capabilityとして渡し、nested
Pattern delimiterは自分のclose/comma maskへ置換する。`->>`は一個のunknown spellingのまま、operator tableのfixity / BPは
arm shapeへ影響しない。colon / arrow後layoutはif / colon / withとも同じsource-only `introduced_body_indentation`へ寄せ、
wrong-indent colon bodyはBlock内のone Missing armと未消費handoffになる。caseのmalformed next armだけにはcompleted
Pattern grammarを変えないrecovery-only comma safe pointを与え、accepted arm-entry triviaはPatternでなくBlockが直接所有する。
M1 specification reviewはpre-write approved、post-writeでwrong-indent・policy region/trailing comma・case recovery comma・
trivia parentの4 blockerを検出し、one repair deltaでapproved。focused direct case-like tests 12 passed、existing Pattern
tests 11、If tests 8、tails tests 11 passed、`cargo check -p yu-syntax`、format/diff checkはgreen。AST / HIR / typed
diagnostics / production dispatch / Yumark wiring / G4a RB-E / Gate 4 certificationは未実装である。

2026-09-05: isolated SCC construction witness C8として、nested canonical `Statement` の最初の宣言選択肢に
direct CST-only `BindingStatement` を追加した。shape は `Statement > BindingStatement > BindingHeader
[BindingBody]` であり、Header が `my` / `our` / `pub`、canonical `Pattern` target、受理された exact
`=` とその前の Gbind trivia を所有する。body のない binding は `BindingBody` を作らず、受理後の
`=` は inline の一つの `OperatorChain` または strictly-deeper `IndentedStatementBlock` を必須にする。
target は caller の active stop を Pattern capability へ写して exact `=` を加え、nested delimiter の
local replacement を保つ。`==` / `=>` は `=` へ分割しない。target 後および `=` 後の shallow/equal
newline は Item と leading trivia を outer Statement owner へ戻し、deeper newline だけを Gbind / body
layout として受理する。visibility-led head は Statement position だけで source-only に reservation し、
`my use = value` と `my use path`、将来 declaration head、operator-definition head の既決 collision を
区別する。braced / indented sequence と inline `with:` は同じ canonical Statement entry を使うが、colon
inline と if/case/catch inline body は引き続き expression-only である。M1 specification review は
accepted-equals の shallow-newline overclaim を一件検出し、one repair で delta-approved。focused Binding
tests 7、tails 11、if 8、case-like 12、Pattern 11 passed、`cargo check -p yu-syntax`、format/diff check は
green。package/workspace suite、performance、legacy/public dispatch、AST/HIR、typed diagnostics、Yumark、
Gate 4/6 certificationは未実施のままである。

2026-09-05: isolated SCC construction witness C9として、nested canonical `Statement` に source-free direct
`UseDeclaration > UseTree` を追加した。plain path、`mod` / `realm/` / `band::` form、operator-name segment、
terminal group / glob、recursive group / exclusion group、alias、`without`、version、`with` anchorまでを一つの
recursive direct Rowan ownerで構築する。bare exact `use`はStatement headで即時に選び、visibility prefix後の
`use`はsource-onlyのvalid UseTree starterを条件に選ぶため、`useful`と`my use = value`は従来どおりUseへ
予約しない。mandatory slot/retryはsink-free canonical Item transactionからcaller-owned stopとleading triviaを
そのままhandoffし、groupはnewline separatorを受理しつつ、missing close後のequal-or-shallower known statement
introだけをouter safe pointとして優先する。mismatched local closeはgroup自身が`Error`で所有する。これに必要な
shared internal helperは、既存payload scanを共用する`scan_statement_item(LexIn, ..)`と
`is_active_stop_lex(LexIn, ..)`のみであり、state、token buffer、source/CST replay、legacy/public dispatchは増やして
いない。M2の仕様・sibling reviewerは初回にidentifier vocabulary、typed caller boundary、group newline、mismatched
closeの4 blockerを検出し、round 1で修復した。delta regressionがmissing-close後のdedent statement handoffを追加で
検出し、architectureのouter safe-point ruleに従うround 2で修復、両reviewerがfinal deltaをapprovedした。focused
Use tests 10、Binding 7、tails 11、if 8、case-like 12、Pattern 11、`cargo check -p yu-syntax`、format/diff checkは
green。broad package/workspace suite、performance、legacy/public dispatch、AST/HIR/header projection、typed
diagnostics、Yumark、Gate 4/6 certificationは未実施のままである。

2026-09-05: isolated SCC construction witness C10として、nested canonical `Statement` に source-free direct
`ModDeclaration`を追加した。optional visibility、exact `ModKw`、ordinary raw nameまたは
`TestModuleMarker > Identifier(test)`、bodyless semicolon・既存brace block・colon inline one Statement / strict
indented blockをdirect ownerで構築する。`mod`はbare/visibility-ledともstatement authorityを得るため
`my mod = value`はBindingへ戻らずtotal Mod recoveryに入り、`my test = value`、`module`、`modular`、`testable`は
prefix splitしない。accepted introducer時点のbaseを全Gmod gapへ適用し、deeper newlineだけをcontinuationとし、
shallow/equal newline、caller separator、typed matching close、companion stopはleading triviaごとhandoffする。
`mod test`はbody starter `;` / `{` / `:`が見えるときだけanonymousで、EOF/boundaryではsecond name Missingとなる。
body-introducerのnon-matching close / bracketはcaller boundaryでなくMod-local Errorとsame-slot retryであり、brace
close recoveryは既存brace ownerへ委譲する。brace statement sequenceは`braced_nud`からbody constructionだけを
`braced_statement_block`へ最小抽出し、braced NUDのouter expression-tail continuationは不変にした。M2の仕様査読が
unconditional non-matching close/bracket handoffと`testable`/inline Binding coverageを検出し、one bundled repairで
閉じ、specification / sibling delta reviewerともapprovedした。focused Mod tests 7、Binding 7、Use 10、owners 23、
tails 11、if 8、case-like 12、Pattern 11、lexical 10、`cargo check -p yu-syntax`、format/diff checkはgreen。
broad package/workspace suite、performance、legacy/public/root dispatch、AST/HIR/header projection、typed diagnostics、
Yumark、Gate 4/6 certificationは未実施のままである。

2026-09-05: isolated SCC construction witness C11として、nested canonical `Statement` に source-free direct
`StructDeclaration`を追加した。optional visibility、exact `StructKw`、raw name、bodyless semicolon、named brace
field、tuple field、strictly-deeper named indented fieldを直接構築し、new direct nodeは`StructDeclaration`と
`StructField`だけである。field listはstatement / NamedRecord ownerを流用せずStructがcomma、qualifying newline、
close、gap triviaを所有し、named fieldのcolon-to-type triviaは`StructField`、tuple fieldはnested
`TypeExpression`だけを持つ。named/tuple RHSはordinary mandatory TypeExpression entryを使い、named field scopeだけに
`StructNamedFields` pre-TypeApply probeを渡すため、`x: F y: Y`はMissing separator + two fieldsとなる一方、
`x: F Y`とtuple `Pair(F Y)`は一つのTypeApplyのままにする。complete Struct name後の全TypePrimaryはbodyを発明せず
BodyIntroducer Missingとpending handoffになり、`:{` polymorphic variantはlone colon bodyと誤認しない。M2仕様査読は
first reviewでTypePrimary handoff、tuple Type vocabulary、Gfield-name newline、trivia ownership、consumer matrixを検出し、
round 1で修復した。final deltaで`:{` body-starter誤認を検出し、round 2でexisting Type scannerのsource-only probeへ寄せて
閉じ、specification / sibling reviewerともapprovedした。focused Struct tests 11、direct Type / Binding / Use / Mod /
owners / tails / if / case-like / Pattern focused sets、`cargo check -p yu-syntax`、format/diff checkはgreen。broad
package/workspace suite、performance、legacy/public/root dispatch、AST/HIR/header projection、typed diagnostics、
generics/derives/companion/method/doc-comment、Yumark、Gate 4/6 certificationは未実施のままである。

2026-09-05: isolated SCC construction witness C12として、nested canonical `Statement`にequality-formだけの
source-free direct `TypeDeclaration`を追加した。optional visibility、exact `type`、raw `Identifier` name、
same-line whitespace-separated `Identifier | SigilIdentifier` parameter list、exact lone `=`、ordinary mandatory
full `TypeExpression` RHSを直接構築する。bare nominal、`impl` / `with` / colon / brace body、derives、semanticsは
追加していない。parameter scannerは全canonical declaration starterと`impl` / `with` / `derives`を予約し、
`$` / `&` / `'`を`SigilIdentifier`、underscore-leading nameを`Identifier`として保持する。
Type RHS caller boundaryは既存`Stops`を明示引数で全normal / malformed / nested ownerへ通し、outer semicolon、
exact `with`、active stopをpending Itemとして返す一方、`A::with`と`{with: T}`のlocal syntax precedenceを保つ。
new ambient state、buffer、replay、TypeDeclaration固有delimiter/list/fenceは導入していない。M2仕様査読の
round 1でraw name vocabulary、declaration-starter reservation、nested caller-stop propagation、TD-R fixture不足を
検出して修復した。round 2でmalformed path retryのcaller-stop漏れと残るTD-R matrixを修復し、regression deltaは
approvedとなった。最後のspec deltaで指摘されたRHS ownership証明不足は、既決expected contractだけを固定する
test-only parent/RHS assertionとしてprimaryが補完した。focused TypeDeclaration 13、TypeExpression 49、Struct 11、
Use 10、Binding 7と関連canonical owner sets、`cargo check -p yu-syntax`、format/diff checkはgreen。broad
package/workspace suite、performance、production/public/root parser、AST/HIR/header projection、typed diagnostics、
Yumark、Gate 4/6/9 certificationは未実施のままである。

2026-09-05: isolated SCC construction witness C13として、nested canonical `Statement`にsource-free direct
`ForStatement`を追加した。Authoritative `FOR-G/J/T/R`のisolated Gate 2--8 analogueだけを実装し、exact bare
`for`、lexical transactionによるoptional apostrophe-sigil label、full `Pattern`、exact `InKw`、one
`ForIterable > OperatorChain`、colon inline/strictly-deeper indented/brace statement bodyをdirect Rowanで
構築する。`forall` / `fork` / `format`はordinary expressionのまま、`my for = 1`はBindingのままであり、
public/root/header/AST/HIR/session/legacy parserを変更していない。For callerだけがPatternのexact `in`、fresh
primary colon / left-brace boundaryを渡し、Pattern annotationのTypeExpressionにも`in` stopを引き渡す。入れ子
Patternのcompletionはdelimiter owner内で単調に集約するため、`for (x |) in ...`は未完成Patternとしてexact
`in`をpendingのまま返し、`InKw`を誤ってcommitしない。iterableのcolon/brace stop、missing
in/iterable/bodyのno-cascade recovery、Use groupのshallow statement handoff、inline body後のsame-indent sibling
保持をfocused fixtureで固定した。M2 pre-write spec audit、post-write specification / sibling regression review、
one bundled repairと両delta reviewはapproved。focused For 12、Pattern 11、`cargo check -p yu-syntax`、
format/diff checkはgreen（existing warningのみ）。broad package/workspace suite、performance、production/public/root
parser、AST/HIR/header projection、typed diagnostics、Yumark、Gate 4/6/9 certificationは未実施のままである。

2026-09-05: C14候補として、bare nominal `TypeDeclaration`のterminal newline provenanceを
source-free direct pathへ移す`direct-tnd-statement-line-handoff-amendment`をReviewed化した。
旧ambient-owner stack / skipped-inline countの**実装経路だけ**を、immediate Copy argument
`StatementLineHandoff::{OrdinaryLayout, BracedStatementSequence, CatchBracedArm,
CatchArmSequenceThroughInlineCanonicalStatement}`へ置換する候補である。四値はglobal state / Context /
Item metadataではなく、nearest statement ownerからcontained callへlexically渡し、return後にcallerの
incoming valueを再利用する。Catch braced armではzero crossingをrecoveryのまま、With/Mod経由のone-or-more
inline canonical Statement crossingだけをNominal newline authorityにする。TND-J priorityはcomplete exact
equality、ordinary/braced/Catch-through line、EOF/semicolon/active stop、deeper EOF trivia、recoveryを一つの
pure form judgeへ固定し、EOFとsemicolonもphysical line evidenceを先に判定する。M3 compiler-referee / spec
reviewはthree delta roundsでapproved。ユーザーは2026-09-05に承認し、設計はAuthoritativeへ遷移した。C14ではこの
four-state valueをstatement / expression / Patternのdirect coneだけで明示的にthreadし、complete bare `type`の
post-header Itemを一回だけform judgeへ渡してNominal / Equality / existing EqualityRecoveryを選ぶ。初回M3
post-write査読はrecord-pattern default expressionが`OrdinaryLayout`とstopなしをfabricateする欠落を検出した。
修復はPatternの全current entry / recursion / delimiter pathへincoming valueを即時引数として通し、record defaultには
unchanged handoffと`stops_for(RBrace)`を渡した。braced/Catch-through-inline newline、record comma / right brace、
zero-inline Catch controlのfocused fixtureを追加し、compiler-referee / specification / regression delta reviewはapproved。
`cargo check -p yu-syntax`、focused TypeDeclaration / repair fixture、`cargo test -p yu-syntax rewrite::tests:: --lib`
(198 passed)、format / diff checkはgreen。broad package/workspace suite、performance、production/public/root parser、
AST/HIR/header projection、typed diagnostics、Yumark、Gate 4/6/9 certificationは未実施のままである。

2026-09-05: 次の construction slice C15 として、direct `TypeDeclaration` の既存 `DerivesClause` を
isolated direct-CST だけで構築する設計を Reviewed 化した。`derives` / `via` / derives RoleRef の `with`、
header RoleRef の `impl` / `=` は flat `Stops` ではなく immediate `TypeOuterBoundary` で current logical
TypeExpression episode にだけ見せる。fresh nested TypeExpression edge は `NONE`、same episode の candidate /
malformed retry / tail / path は incoming value を保存する。`StatementLineHandoff` は clause の全 trivia gap
へ immediate に渡すが state にはしない。braced / Catch-through-inline は outer handoff、zero-Catch は header の
existing EqualityRecovery と trailing clause 自身の recovery + outer continuation を分ける。header clause 後の
`with` / `impl` は Complete / Missing / malformed RoleRef を問わず extra DefinitionIntroducer recovery なしで
pending Item を返す。compiler/recovery と specification の独立査読は repair 後 approved、2026-09-05に
ユーザーも承認した。C15 は実装・査読完了した。direct `DerivesClause` を `TypeDeclaration` の直下へ
構築し、header / Equality trailing のownerだけが immediate `TypeOuterBoundary` を渡す。reviewで見つかった
RHS / path / forall binderのouter-boundary trivia移譲とCatchBracedの`with` / `impl` handoffは、いずれも
pending Itemを保持するowner側で修復した。focused C15 fixture 15、`cargo check -p yu-syntax`、format / diff
checkはgreen。C15はnew state / Stops / Item / public dispatch / AST / HIR / Struct / Yumarkを増やしていない。
次のshared derives owner / Gate 6採用には別途の設計・承認が必要であり、C15から自動で進めない。Gate
6/D11/RB-DRV/public/legacy/AST/diagnostic/Struct/Yumarkは scope 外のままである。

1. **standalone `TypeExpression`の残りuse-site(where節)**: role signature・act
   signatureは上記で解決(role method signatureはexisting Binding Pattern
   TypeAnnotationを再利用、act operationも同じくexisting Patternを再利用)。
   where節は、role/act同様「そもそも宣言文法自体が未実装」と判明済み
   (2026-08-27調査)——着手にはまず宣言family自体の設計が要るうえ、正本が
   「type-specific where clauseをYulang3に発明しない」と明記していて位置付けが
   不明確。
2. **canonical Statement / root Declarationの残りvariant**:
   declaration-level `where`/doc-comment宣言。`role`/`act`/`enum`/`error`/`for`文は実装完了。
   `type`/`struct`/`mod`/`impl`(shellのみ)/`cast`/演算子定義も完了。
3. **defer済みType colon/brace role-like bodyの優先順位決定**: companion `with:`は完了した。
   Type colon/brace role-like bodyは引き続き別addendumが必要で、実装順序は未決定。
4. **Cast known-residualの一般化解消**: 追補が明示的に別addendum送りにした、caller
   boundary hidden behind a missing nested delimiterというcondition-based residual
   family(ASOB追補由来、Castで再確認)。nested Pattern/TypeExpressionへのcaller
   boundary伝播・missing delimiter・local candidate/same-spelling separator priorityを
   一般化する新しいsigned addendumが必要。

### standalone `role`宣言addendum、Authoritative化(2026-08-27、commit `fb076d6e`)

サイト完成直後、ユーザに次の作業候補を提示 → TypeExpression残りuse-site配線
(role signature・where節・act signature)を選択 → 調査の結果3つとも
「TypeExpression配線」でなく「宣言文法自体が未実装」と判明(role/act:
`Declaration`/`Statement`/`StatementIntro`/`StatementKind`にvariantなし、
where節: declaration-level `WhereClause`が未実装かつ正本が「type-specific
where clauseを発明しない」と明記) → roleから着手を選択。

Sol xhighへdesign委任、Proposal初稿(719行、design doc 22777–23494)を
Claudeが査読。yulang2 oracle(`yulang2-oracle`タグ、実commit`a58eefc31e22`)の
実sourceと全citation照合、誤り2件発見・修正(oracle commit hash誤citation、
fold.yuが実際には持たない"unannotated default method"の誤claim——実例は
fmt.yuのみ)。Solが挙げたopen design question 11件は全部derives/impl/cast
既存パターンと一貫、実質的異論なし。ユーザ承認によりAuthoritative化完了。

設計の要点: role headはfull mandatory TypeExpression(Y2のwhitespace-applied
input parameterをseparate parameter ASTへ分解しない)、role method signatureは
new RoleSignature nodeでなくexisting `Binding > Pattern > PatternTypeAnnotation
> TypeExpression`をそのまま使う(これが今回のTypeExpression配線の本体)、
bodyはbodyless semicolon/existing brace block/colon inline-indentedの3形態、
derives Gate 1aの`TypeExpressionEpisodePolicy`等をhard dependencyとして
再利用、cast Gate 4aの`classify_binding_style_body_layout`は明示的に
非再利用(authorityが違うため)。intro priorityはType後/Impl前。10 gate計画。

実装完了(2026-08-27): Gate 1 vocabulary/AST、Gate 2 isolated intro、Gate 3 head
TypeExpression episode、Gate 4-5 AST/direct body adapters、Gate 6 RLD-R recovery、Gate 7
body composition、Gate 8 state restoration、Gate 9 real dispatch、Gate 10 final public
scope matrixを順に閉じた。Gate 5中にY2の`container.index`等がPattern DotField
continuationを必要とする未実装gapを発見し、Roleのscopeへ推測実装せずplain identifier
fixtureへ訂正、Pattern別追補へdeferした。Gate 10はall visibilityとcontextual `role`の
ordinary-word positionsをpublic/direct parityで固定し、Role syntax typeがyu-syntax外へ
漏れていないことも確認した。

### standalone `act`宣言addendum、Authoritative化・11 gate実装完了(2026-08-27)

role完走直後、ユーザから次候補を「どれでもいいですよ」と一任され、act宣言を選択。
Sol xhighへdesign委任、role Gate 3で確定したoracle commit hash二重citation
(タグオブジェクト`1ec55fdfd33d...`と実commit`a58eefc31e22...`を区別)を最初から
正しく踏襲、Claude独立レビューで実誤りゼロ判定(role addendumの2件から改善)。
ユーザ承認によりAuthoritative化。

設計の要点: `ActDeclaration`は`[visibility] act Head [= Source] Body`の3-slotで、
headはfull mandatory TypeExpression、sourceはoptional `= TypeExpression`(copy
source)、bodyはbodyless(explicit `;` / implicit tail-nothing)・brace・colon
inline-indentedの3形態。role/derives/impl/castの共有TypeExpression episode
infrastructureをhard reuseしつつ、role単一slotのHead→BodyIntroducerと異なり
Head→Source→BodyIntroducerの3段no-cascade recoveryを新規設計。intro priorityは
Cast後/Binding前。`my act = 1`はBinding target(rollback)、`my act A = B`は
raw head candidate lookaheadでAct intro選択という非対称衝突規則も新規。

実装完了: Gate 1 vocabulary/AST、Gate 2 isolated intro(`my act`非対称
lookahead)、Gate 3 head episode、Gate 4 slot-parameterized head/source shared
driver、Gate 5-6 AST/direct body adapters、Gate 7 ACT-R recovery matrix(3段
no-cascade chain確認)、Gate 8 body composition matrix(Role含む9 live Statement
construct全部が全body formで合成可能と確認)、Gate 9 pre-promotion
state-restoration matrix、Gate 10 real dispatch atomic promotion(Cast後/
Binding前へ挿入、既存優先順位無傷)、Gate 11 final public scope/contextual-word
matrixを同日中に完走、511→530 tests green。Gate 11では、role Gate 10で
Claude自身が犯した誤り(検証していない`my role = value`をordinary word例として
誤指定)を教訓に、全contextual-word例を追加前に文法対応状況と照合する規律を徹底し、
誤りゼロで着地した。host act tier・operation registration/classification・
derives attachment拡張・declaration companion `with:`・copy source resolutionは
addendum自身が別addendumへ明示的にdefer。

## 文法・CSTをエラー含めて完全に規格化するサイト(`syntax-reference/`、pilot稼働中)

ユーザ指示(2026-08-23)で起票、2026-08-27にスコープ確定・pilot実装・push完了
(commit `cc25bc2e`)。同日中に英語版・日本語版の並行構成へ再編(commit `6edb534d`)
——ユーザ指示「英語版と日本語版が欲しい。英語版の方があなたは参照しやすい。
日本語版の方は私が読みやすい」。

### 決定事項(2026-08-27、AskUserQuestionで確定)

- 技術基盤: **mdBook**。`web/`(yulang2時代のplayground/docsサイト、yulang3では
  一括削除済み)は再利用しない。`cargo install mdbook`でこの環境に導入済み。
- 設置場所: 新規`syntax-reference/`(`docs/`のarchitecture文書とは責務分離)。
- 対象読者: **実装者向け**(このセッションの開発者・将来のClaude/Codexセッション)。
  文体は簡潔・省略多め、実装ファイルへのクロスリファレンス重視。
- 着手タイミング: **grammar確定を待たず、要素ごとに確定次第ページ化**。TypeExpression
  残りuse-site・declaration残りvariantが未着手でも並行して進める。
- 生成方式: 正本(`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`)からの
  半自動抽出。Codex(Terra、要素ごとの内容は正本から機械的に転記する作業のため)が
  1ページずつ執筆し、Claudeが実装ファイル・commit履歴と照合してfaithfulness検証する
  運用。
- 多言語化: gettext系(`mdbook-i18n-helpers`)は採用せず、`en/`・`ja/`それぞれ
  独立した軽量mdBook bookとして持つ(共有SUMMARY/翻訳同期の仕組みなし)。両言語とも
  独立して正本を要約し、機械翻訳の下訳にしない。`en/`は将来のClaude/Codex
  セッションの横断参照用、`ja/`はユーザの読解用。

### サイト構成

```text
syntax-reference/
  README.md          # bilingual概要、build/serve手順
  en/
    book.toml         # language = "en"
    src/
      SUMMARY.md
      index.md
      conventions/   # Parser共通規約(trivia/range/AST-direct parity等、stub)
      expressions/
      patterns/       # 4/4完成 (下記参照)
      types/
      statements/     # 7/7完成 (下記参照)
      cross-cutting/
      indexes/
  ja/
    book.toml         # language = "ja"
    src/               # en/と同じ構造、日本語
```

### statements/ family: 7/7完成(2026-08-27、push済み)

bare-nominal-type・equality-type・binding-use・mod-declaration・struct-declaration・
derives-attachment・impl-shell・cast-declarationの8ページ(7要素、binding/useは
1ページに統合)を英日両方で執筆・独立検証・push完了。commit
`cc25bc2e`〜`587ea716`。各ページで関数名・test名・commit hash・design doc行範囲・
worked exampleのbyte range・AST struct shapeを実装/正本と照合し、mod-declarationの
初稿で1件(worked exampleが正本に実在しない)実際の問題を発見・修正した。

### patterns/ family: 4/4完成(2026-08-27、push済み)

pattern-core・list-pattern・record-pattern・type-annotationの4ページを英日両方で
執筆・独立検証・push完了。commit `102cfa98`〜`1647fc18`。type-annotationは
TMN(newline owner policy)・positional fence追補まで含む複雑な履歴(commit 9件)を
正確に反映、独立検証でtype-annotationの初稿にある実装関数名の誤citation
(`malformed_trivia_classifier`→正しくは`classify_type_malformed_trivia`)を1件
発見・修正した。

残りfamily: expressions(9要素)・types(6要素)・cross-cutting(4要素)。
優先順位は未確定、着手時に選ぶ。

ページ追加時は、`en/`・`ja/`両方に同じelementの11節ページを別々に執筆する
(翻訳ではなく、同じ正本事実を各言語で独立に書く)。引用するcommit hash・関数名・
test名の集合が両言語で一致することをClaudeが照合する運用(pilotで確立済み)。

### types/ family: 4/6完了(2026-08-27、push済み)

type-expression-core・named-record-type・forall-type・effect-row-typeの4ページを
英日両方で執筆・独立検証・push完了。commit `063da888`〜`b22a7973`。独立検証で
実際の誤り2件を発見・修正: (1) forall-typeの前段階でtype-annotationページの
関数名citation誤り(既に修正済み・前述)、(2) effect-row-typeのAST shape section
がEffectRowType structに存在しない"trailing separator" fieldを主張していた
(NamedRecordType/ParenthesizedTypeGroupの記述からの誤コピーと推定)——実際は
apostrophe/open/items/close/rangeの5 fieldのみで、正確な記述へ修正した。

### types/ family: 6/6完成(2026-08-27、push済み)

残り2要素、多相variant型(このプロジェクト最難の設計サーガ、実装7 commit・shared
driver rewrite・active-newline境界バグ修正を含む)とbracket row grammar
(leading/trailing非対称2位置grammar)を英日両方で追加。commit
`b22a7973`〜`b9f1d6cf`。今回はsection 6のAST struct fieldを1つずつ実装と
照合する追加検証を行い、誤りゼロで着地(前回effect-row-typeで発見した
"trailing separatorの誤citation"の再発防止)。

これで`statements/`(7/7)・`patterns/`(4/4)・`types/`(6/6)の3 familyが完成。

### expressions/ family: 9/9完成(2026-08-27、push済み)

ユーザから「3時間は自由に動いていい、一切承認する」と権限付与を受け、質問なしで
連続実行中。parenthesized-expression + operator-chain → colon-application +
if-expression → braced-statement-block + case-catch → call/field/path/ML-application
tails + index/projection tails → WithBodyTailの5バッチで完走(commit
`f5c3554f`〜`ded1788d`)。call/field/path/MLとindex/projectionは隣接する2つの
fixed-tail addendum(design doc 9695–10182 / 10184–10660)で、Codexは正しく
page単位を分離した(内容を無理に1ページへ統合しなかった)。WithBodyTailは
declaration companionではなくgeneric-expression terminal tail専用の単一addendum
(10662–11085)と正確に確認。実装関数34件・fixture 17件・commit hash 15件・
AST struct/enum 13種を独立検証、誤りゼロ。

これで`statements/`(7/7)・`patterns/`(4/4)・`types/`(6/6)・`expressions/`(9/9)の
4 familyが完成、英日52ページ。残り`cross-cutting/`(4要素)。

各elementページの11節template: Status/正本/last-verified commit → Scope →
BNF grammar → judge/priority/owner boundary → byte-exact CST worked example →
AST shape → typed recovery table → boundary/state-restoration contract →
yulang2 divergence → known residual/deferred surface → 実装関数・fixture
cross-reference。

### cross-cutting/ family: 2/4完了(2026-08-27、push済み)

expressions完走直後、残り最終familyへ着手。cross-cuttingのmechanismは単一BNF
production/単一AST nodeを持たないため、grammar-element用11節templateがそのまま
使えない——着手前にSol xhigh(document構造判断のため)へ調査+template適応案を
委任。1回目の応答がtool-level cache TTLエラーでtruncateされたため、続きの
section(proposed template・ASOB scale recommendation)だけを再送させて全文回収。

適応後のtemplate: section 3(BNF grammar)を"canonical rule and decision
procedure"、section 6(single AST shape)を"participating parser state and
adoption matrix"に置換、他9節は既存templateの精神を保持。ASOBは19 gate・
6 implementation file・design doc約803行と他3件合計より大幅に大きいため、
main page + `asob-integration-matrix.md`appendixの2ファイル構成をSolが推奨
(per-gate 19ページ分割は非推奨——gate番号はimplementation sequenceであり
概念単位ではないため)。

layout-aware-separator-authority(design doc 9314–9693) + TMN(16557–16860、
`TMN-B/P/C/S`)の2 mechanismを英日で追加(commit `1d028643`)。TMN実装
commit列(9件)が本セッション既知の「TMN Slice D/E/F/G」タスク群と一致することを
確認。両page共worked example・function/type名・commit hash全部独立検証で
誤りゼロ。SUMMARY.mdの"Cross-cutting"を"Cross-cutting mechanisms"へ改名し
pilot placeholder(概要のみ・未執筆)から実ページ2件へ差し替え。

続けてpositional fence(design doc 16862–17289、比較appendix 17291–17399、
実装12 commit)を追加(commit `4e4be29e`)。TMNが「malformed newlineが
handoffするか」を決め、positional fenceはその「caller owns this
boundary」という事実をParseLocal-scoped rollback-owned ambient stateとして
任意の深さのnestingを越えて伝播させる実装権限——旧`caller_owned_boundary`
bool方式を置換した経緯を正確に反映。worked trace 4件・commit 12件・
function/type名全部独立検証で誤りゼロ。

残り1要素: ASOB(main page + `asob-integration-matrix.md` appendix、
Sol推奨の2ファイル構成)。これでcross-cutting/family 3/4完了。

### ASOB main page追加(2026-08-27、push済み、commit `0bd500a5`)

cross-cutting最後のmechanism、ASOB(design doc 18358–19160、19 gate、
`7b5ab178`でfinalize)のmain pageを英日で追加。Sol推奨どおりmain page限定、
完全gate ledgerは後続appendix(`asob-integration-matrix.md`、未作成)へ委譲。
「later integration section」(19162/19677/20278)がASOB本体でなく
equality-type/bare-nominal-type/derives-attachmentのowning addendumだと
確認しbacklinkのみ、ASOB独自の4 known-residual familyを正確に記述し
Castのfour-condition predicateがfamily 4のdownstream specializationだと
明記。

独立検証でこのfamily最大の実誤り3件を発見・修正(Codex自身の検証パスが
見逃していたもの):
1. "Struct missing-close before an outer else"例が正本18730–18740行を
   引用していたが、その範囲は**別の**worked example("Deliberate
   same-column companion divergence"、内容が異なる"else: Bool }")。
   実際のcode blockは18761–18763行——source string自体は正確だったが、
   citationが30行分ずれて無関係な内容を指していた。
2. "Braced owner suspends/resumes"例が18814–18821(explanation prose)を
   引用していたが、実際のcode blockは18808–18810行。
3. ListPattern例のcitation(18832–18840)を実際のcode block行
   (18833–18835)へ精密化。
4. (副次)en/jaパリティのgap 1件——`IfExpression`のbacktick wrapが
   英語版のみで日本語版に欠けていた。

6 commit hash・5実装fileにまたがる9個のtype/function・7 fixture全部を
grep照合、修正後のworked example行・"later integration"判定を再照合、
en/ja token集合完全一致・両mdbook build成功を確認してからcommit。

これでcross-cutting/の4 mechanism全部(layout-aware-separator-authority・
TMN・positional-fence・ASOB main page)が完成。残るのはASOB
integration-matrix appendixのみ。

### ASOB integration matrix appendix追加、サイト完成(2026-08-27、push済み、commit `ba06fdac`)

`syntax-reference/`最後のページ、ASOBのGate 1〜19完全ledger(design doc行範囲・
実装内容・commit・主要file・代表fixtureの6列表)を英日で追加。main pageの
section 11が委譲していた完全ledgerがこれで揃った。

独立検証でこのプロジェクト最大級の実誤りを発見・修正: gate 16・17・19が
「`5f627f1c`(final 19/19 closure)」に帰属されていたが、`git show --stat
5f627f1c`で確認するとこのcommitは`type_expr.rs`(BracketRow専用)にしか
触れておらず、commit message自体も"ASOB Gate 14(final ASOB gate、19/19)"
——gate 14がBracketRow文法自体がまだ存在せずASOB作業の最初からblockされて
いて19個中「時系列で最後に完了した」gateだったという意味であり、
「このcommitがgate 16/17/19を実装した」という意味ではなかった。さらに
`git log -S`でgate 16・19が引用していたfixture 2件の導入commitを追跡した
ところ、それぞれGate 8(`a355058d`)・Gate 3(`5cafd19a`)で導入済みと判明
——5f627f1cより2 gate分も前。3行とも「専用のgate-tagged commitなし、
cross-construct invariant/regression gateとして先行gateの実装で累積的に
満たされる」へ訂正し、正しい導入commitを引用し直した。

これで`syntax-reference/`は全5 family(statements 7/7・patterns 4/4・
types 6/6・expressions 9/9・cross-cutting 4 mechanism+appendix)が完成、
各言語41ページ(index/SUMMARY含む、英日計82ファイル)、未執筆要素ゼロ。
ユーザの「3時間自由に動いていい、一切承認する」という権限付与のもとで
質問なしに完走した。commit範囲は`f5c3554f`(expressions着手)〜
`ba06fdac`(サイト完成)。

### pilotページの検証結果

`statements/bare-nominal-type.md`(bare nominal `type`宣言、9 gate完了済み)を
pilotとして選定・作成。Claudeが独立に照合し、引用した実装関数8件・回帰test 7件が
全部実在、AST struct shapeが実装と完全一致、引用commit hash 10件が全部正しい
gate commitを指す、正本の行範囲引用(19677–20277)がbyte-precise、worked
example 2件が正本から実際に転記されたものであることを確認済み。

### 次にやること

expressions/patterns/typesの各elementから1つずつページを追加していく。優先順位は
未確定——着手時に選ぶ。tuple/operator chainのように複数の正本節を合成する要素は、
1ページに統合せずcross-cuttingページ参照にする方針(Sol提案どおり)。
