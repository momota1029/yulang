# `case` / `catch` expression

## 1. 状態・正本・最終確認

Authoritative な NUD-primary `case` / `catch` 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 7243–8017 行にある。この arm-sequence policy は Pattern page が繰り返し参照する Case/Catch arm newline を所有する。Statement sequence ownership とは別であり、Case-inline、Catch-inline-single、indented、Catch-braced policy を持つ。

design / implementation commit は `51ccc640`、`0efd67e4`、`6e8ca889`、`72c93d5a`。後ろ二つの fix は current contract の scrutinee trivia/arrow recovery と same-position missing arm-separator retry を保持した。

## 2. 対象範囲と非対象

`case` と `catch` は別々の operand-starting NUD primary である。optional apostrophe-sigil label、flat OperatorChain scrutinee、family-owned block、Pattern arm、optional guard、exact arrow、inline chain 一つまたは indented statement body、Catch の optional second handler Pattern を所有する。Catch はさらに braced arm block を所有する。

`\case`/`\catch` lambda、shared Pattern grammar を越える Pattern form、case-only constructor application、case brace arm block、multi-arm Catch colon-inline block、exhaustiveness/guard/handler/label/exception semantics、HIR lowering、inference、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
CaseExpression  := CaseKw  CaseLikeHead CaseBlock
CatchExpression := CatchKw CaseLikeHead CatchBlock
CaseLikeHead := G* [ CaseLikeLabel G* ] Scrutinee G0*
CaseLikeLabel := Apostrophe!Identifier

CaseBlock := Colon (CaseInlineArmSequence | CaseIndentedArmSequence)
CatchBlock := Colon (CatchInlineArmSequence | CatchIndentedArmSequence)
            | LBrace G* CatchBracedArmSequence G* RBrace

CaseArm  := Pattern [ CaseGuard ]  Arrow ArmBody [ Semicolon ]
CatchArm := Pattern [ Comma Pattern ] [ CatchGuard ] Arrow ArmBody [ Semicolon ]
CaseGuard := (IfKw | WhereKw) OperatorChain
CatchGuard := (IfKw | WhereKw) OperatorChain
ArmBody := OperatorChain | IndentedStatementBlock
```

Case/Catch scrutinee は Colon で stop し、Catch はさらに LBrace で stop する。Case は comma-separated inline arm、Catch colon-inline は exactly one arm、Catch indented/braced form は multiple arm を持てる。Case braced arm block は invalid by design である。

## 4. Judge・priority・owner boundary

operand-required NUD site では exact maximal contextual word `case`/`catch` だけを accept/cut し、`casefold`/`catcher` は identifier のままである。Case scrutinee は Colon だけ、Catch scrutinee は Colon と LBrace を reserve する。そのため `case x { ... }` は brace を scrutinee/outer expression へ残す一方、Catch は direct `CatchBlock` を所有できる。

arrow は dynamically associated operator ではなく exact fixed `->` punctuation である。Pattern、handler、guard、arrow、body、arm separator は各自の stop を持つ。Catch handler comma は CatchArm の direct child、arm-list comma は family separator である。current-depth Catch-brace newline と indented arm-indent newline は arm-sequence policy が所有し、body-statement newline は indented statement block が所有する。

## 5. Byte-exact CST の worked examples

追補は source-order CST outline を示すが byte-range 付き tree はない。ここでは range を作らない。

```text
case 'go x: 1 if ok -> yes, _ -> no
```

設計文書 7657–7697 行は label、scrutinee、`CaseBlock`、guard を持つ first `CaseArm`、`CaseArmSeparator`、second arm が source order の sibling となる detailed `CaseExpression` outline を与える。

```text
catch action { err, handler -> recover; }
```

設計文書 7699–7702 行は brace を direct `CatchBlock` child として固定する。handler comma、second Pattern、arrow、body、semicolon は `CatchArm` の direct child であり、`BracedStatementBlockExpression`/Statement/colon tail は作らない。

```text
case x: 1 -> a, 2 -> b
```

設計文書 7959 行は `CaseInlineArmSequence` の multiple inline Case arm と optional trailing-comma coverage を固定する。

```text
catch action: err, handler -> recover
```

設計文書 7964 行は full second handler Pattern を持つ exactly-one inline Catch arm を固定する。

## 6. Parser 側 AST shape

`PrimaryExpression::Case` と `PrimaryExpression::Catch` は `CaseExpression` と `CatchExpression` を持つ。各 struct は正確に `keyword`、optional `label`、recovered boxed `scrutinee`、recovered `block`、`base_indent`、`range` を持つ。`CaseLikeLabel` は正確に `text` と `range` を持つ。

`CaseBlock` は正確に recovered `colon`、recovered `arms`、`layout`、`range` を持つ。`CatchBlock::Colon` は正確に recovered `colon`、recovered `arms`、`layout`、`range`、`CatchBlock::Braced` は正確に `open`、recovered `arms`、recovered `close`、`range` を持つ。`ColonArmLayout` は正確に `Inline` または `Indented { base_indent, arm_indent }`、`ArmSequence` は正確に recovered ordered `arms` と optional `trailing_comma` を持つ。

`CaseArm` は正確に recovered `pattern`、optional recovered `guard`、recovered `arrow`、recovered `body`、optional `terminator`、`range` を持つ。`CatchArm` は optional recovered `handler` を追加する。`CaseGuard`/`CatchGuard` は各々正確に `keyword`、recovered boxed `condition`、`range` を持つ。`ArmGuardKeyword` は正確に `If` または `Where`、`ArmBody` は inline boxed `OperatorChain` または `IndentedStatementBlock` である。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| keyword 後に scrutinee がない | Scrutinee Missing 一件。`:`、Catch `{`、close/newline/EOF を保持 |
| block introducer がない | Block Missing 一件。outer delimiter/newline/EOF を非消費で return |
| colon 後の same-or-shallower newline | Arm Missing 一件。trivia と next outer construct を保持 |
| first pattern がない | Pattern Missing 一件。handler comma/guard/arrow/close/arm boundary を保持 |
| Catch handler comma 後に handler がない | Handler Missing 一件。guard/arrow を保持 |
| guard expression がない | Guard Missing 一件。exact arrow を保持して arm 継続 |
| body NUD candidate があるが arrow がない | Arrow Missing 一件後 same-position body retry |
| arrow/body が同一 boundary でともにない | root-cause record 一件と required slot marker。comma/dedent/right brace/EOF を保持 |
| next pattern 前の arm comma がない | Separator Missing 一件後、その Pattern を一度 retry |
| arm comma 後の malformed byte | non-empty Error 一件後、nearest safe point で mandatory-arm retry |
| Catch `}` がない | CatchBlock close Missing 一件。caller delimiter/lexical boundary を越えない |

committed Missing/Error CST node と recovery record は one-to-one である。Pattern recovery 自体を Case/Catch が再診断しない。

## 8. Boundary と state-restoration contract

closed `ArmSequencePolicy` は earlier Pattern page が参照する shared authority である。Case inline は comma を所有し、Catch inline は意図的に所有しない。indented sequence は arm-indent newline だけ、Catch-braced sequence は current-brace-depth newline と comma を所有する。これは `StatementSequencePolicy` と別なので、body-block separator は arm separator にならない。

全 probe は sink-free。normal/recovery/rollback exit は stop frame、delimiter/brace scope、indentation baseline、ambient ownership、lexical-region boundary を restore する。nested delimiter/opaque lexical region は inner colon/comma/arrow/brace/`if`/`where` spelling を arm safe point にしない。

## 9. Yulang2 divergences

Yulang3 は contextual primary placement、label、guard、Catch handler、exact arrow、colon/indented form、direct Catch brace を保つ。Pratt subtree でなく flat OperatorChain を保存し、generic case-like wrapper でなく family-specific source-order CST node を使い、typed Missing/Error recovery を持つ。Case brace は Yulang3 では Case block として意図的に accept しない。

## 10. Known residual / deferred surface

documented `ASOB-G` residual は representative Case/Catch arm-sequence boundary situation を含み、hidden にせず characterize する。lambda form、future Pattern form、semantic exhaustiveness/guard/handler/label/exception behavior、other colon-owner unification、HIR lowering、inference、diagnostics、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_case_like_nud`、`parse_case_like_label`、`parse_catch_braced_block_ast`、`parse_case_arm_sequence_ast`、`parse_catch_arm_sequence_ast`、`arm_sequence_boundary`、`parse_case_arm_ast`、`parse_catch_arm_ast`、`parse_case_guard_ast`、`parse_catch_guard_ast`、`commit_case_like_expression`、`commit_arm_sequence`、`commit_one_arm`、`commit_arm_guard`、`commit_arm_body`、`emit_case_like_missing`、`commit_case_like_invalid_arrow` を参照する。

fixture は `case_and_catch_are_primary_expressions_with_family_owned_arm_shapes`、`case_like_guards_and_indented_arms_keep_their_boundaries`、`case_like_arrow_is_exact_and_never_splits_a_longer_operator`、`case_like_ast_and_direct_paths_agree_on_arm_count_and_layout`、`case_like_missing_arrow_retries_the_body_from_the_same_position`、`case_like_recovery_marks_missing_mandatory_slots_once`、`case_like_invalid_arrow_run_recovers_to_the_next_comma_arm`、`case_like_same_indent_boundaries_stay_with_the_outer_owner`、`case_like_missing_arm_comma_retries_the_next_pattern`。
