# 現在のタスク: yu-syntax parser構築の継続とgrammar/CST正規化サイトの起票

更新: 2026-09-02（`syntax-reference/`サイト完成→standalone `role`宣言10 gate完走→
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
owner adoptionをここで停止し、Authoritative adoption matrixをfinal approval後の新 parser の
必須acceptance evidenceへ引き継ぐ方を選択した。`notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`は
そのM3 successorを起票し、M3 compiler/spec/regression reviewとdelta reviewを閉じて
`Reviewed`にした。current-chasa mechanism、`SourceInput`/`ParseLocal`の
field ownership、direct Rowan/typed diagnostic、leading-trivia `Item`/`Boundary`、flat
`OperatorChain`、old/new atomic promotionを対象とするが、まだproduction `yu-syntax`の変更を
認可しない。次はReviewed plan §6の未決定点を閉じ、ユーザ承認を得てGate 1 (`with_str`)へ
進む。Gate 3bのmatrix・Yumark surface/frame contracts・既存完了sliceは
そのままnormative controlである。

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
