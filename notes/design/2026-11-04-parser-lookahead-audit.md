# yu-syntax lookahead / speculation audit (2026-11-04)

Status: 調査報告(read-only audit by Codex gpt-6.1-sol, 実測なし・静的調査)。実装は未着手。
HEAD 4e79cdf28 時点。Y2 = tag `yulang2-oracle`。

The strongest finding is **unbounded rescanning inside token selection**, especially polymorphic-variant and lambda admission. The current code does **not** contain the full pattern described in the premise: production `maybe(...)` calls are absent, and syntax-output rollback is absent.

Audit snapshot: branch `yulang3`, HEAD `4e79cdf28448d5093caeef747bd696a64215da5d`. `yulang2-oracle^{commit}` resolves to the requested `a58eefc31e22141574b6f20c6a5748151c6d79f1`.

**A–B. Inventory and classification**

Paths below are relative to `crates/yu-syntax/src/`. Historical paths prefixed **Y2** are relative to `crates/parser/src/` at `yulang2-oracle`. Line numbers refer to the inspected versions.

Counting conventions:

- **T** counts explicit lexical `token(...)` transaction call expressions, including `token(scan_...)` constructors inside choices. There are **251**, distributed in the census below. This is a syntactic count, not 251 independently harmful speculations.
- There are **6 production `choice(...)` expressions**, all in `lexical/lexer.rs`; **0 production `maybe(...)` calls**.
- There are **4 detached lexical probe constructors**: three in `lexical/lexer.rs`, one in `type_expr/record.rs`.
- Each inventory row groups one decision or closely related implementations; all constituent locations are identified.
- Tests under `tests/`, inline test modules, and `#[cfg(test)]` helpers are excluded.

Classification:

- **a** — real grammatical/environment context; pass explicit parser state.
- **b** — structural decision belongs in the parser; retain ordinary lexical tokens/evidence.
- **c** — redundant probe, rescan, dispatch attempt, or transaction can be removed while preserving recognition.
- **L** — necessary local lexical recognition or a consuming scan. These are listed to distinguish them from removable speculation; forcing them into a/b/c would misclassify ordinary maximal munch.
- **N** — no source lookahead: coordinate observation, existing-token inspection, or output construction.

Reach notation: **C** = fixed characters/scalars; **W** = one variable-length word/token; **G** = trivia run, potentially comments through EOF; **LINE** = physical line, potentially the whole remaining source without a newline; **REGION** = balanced/delimited region through EOF or the applicable fence.

Historical comparison keys used in the classification column:

| Key | Verified Yulang2 behavior and citation |
|---|---|
| R1 | Fixed punctuation alternatives: `scan/mod.rs:152` `scan_punct_expr`, `:184` `scan_punct_pat`, `:207` `scan_punct_typ`. Ordinary `:`, `|`, `\`, `'`, and pattern `..` tokens. |
| R2 | Scan a maximal identifier, then classify it: `scan/mod.rs:19` `scan_ident_or_keyword`, `:257` `ident`, `:300` `contextual_word_kind`. Contextual scanners receive stop sets. |
| R3 | One `Number` scanner: `scan/mod.rs:117` `scan_number`; number components at `:237` `number_with_leading`, `:249` `frac`, `:253` `exp`. No separate whole-integer retry after a whole-float attempt. |
| R4 | Token scanners retain trailing trivia: `expr/scan.rs:109`, `:261`; `scan/trivia.rs:13` `scan_trivia`; `lex.rs:417` `Lex`. Quote/doc modes come from `Env`. |
| R5 | Operator trie selection uses context and limited successor evidence: `expr/scan/op/scan.rs:32` `scan_op_with_trie`, `:121` `next_is_expr_stop`, `:129` `value_start`. Y2 also performs lookahead here. |
| R6 | Emit `Backslash`, then parse the lambda: `expr/scan.rs:178` `read_expr_nud_punct`; `expr/core.rs:116`; `expr/control.rs:37` `parse_lambda_expr`, `:198` `parse_lambda_after_intro`. No lexer-wide complete-header recognizer. |
| R7 | Type punctuation is ordinary; parser owns structure: `typ/scan.rs:94` `read_typ_nud_punct`; `typ/parse.rs:379` `parse_type_poly_variant_group`; `:452` `TypeRecordFieldMachine::parse_item`. Bar variants are not implemented equivalently there. |
| R8 | Pattern tags and tails come from ordinary tokens: `pat/scan.rs:146` `read_pat_nud_punct`, `:159` `read_pat_led_punct`; `pat/parse.rs:123` `parse_tail_bp`. Pattern `..` exists as punctuation/spread; signed/range-pattern equivalents were not found. |
| R9 | Statement/visibility dispatch is parser-owned: `stmt/mod.rs:64` `parse_statement_from_stop`, `:159` `parse_visibility_stmt`. Y2 itself checkpoints and retries contextual `my` dispatch at `:166–205`. |
| R10 | Dedicated use vocabulary: `stmt/use_scan.rs:52` `scan_use_tok`, `:153` `use_version_chars`, `:162` `use_op_name_chars`; parser owns operator-name parentheses in `stmt/use_decl.rs:178` `parse_use_operator_name`. |
| R11 | For-label discrimination is in the parser: `stmt/for_stmt.rs:78` `parse_for_label`. Y2 also peeks; this is not evidence that label discrimination can disappear. |
| R12 | Literal mode/chunks: `string/scan.rs:48` `scan_string_nud`; rule chunks: `expr/scan/rule.rs:26` `scan_rule_lit_start`, `:93` `scan_rule_lit_token`, `:117` `scan_rule_lit_lazy_name`. |
| R13 | Yumark has its own mode-aware scanner: `mark/scan.rs:76` `scan_mark`, `:204` `scan_block_nud`, `:243` `scan_inline_nud`. Y2 also uses lookahead for markup boundaries. |
| R14 | Operator-header/body work is parser-owned: `stmt/op_def.rs:216` `skip_op_def_body`, `:306` `scan_op_name`, `:332` `scan_bp_vec`. |
| R15 | Expression parser owns colon/with structure: `expr/tail.rs:47` `pratt_tail_bp`, including `With` at `:165`; `:304` `parse_apply_colon_rhs`. |

**`lexical/lexer.rs` — 55 decision groups; T=87; choice=6**

| Line(s): function | Inspection/speculation and reach | Classification |
|---|---|---|
| 68: `scan_statement_payload` | Try statement keyword before expression payload; W. | a for statement mode; c duplicated word classification, R2 |
| 101,105,109,113,117,120,133,138,142,155: `scan_expression_payload` | Ordered transactional lambda/spread/arrow/keyword/sigil/operator/equals/dangling attempts. Reach inherits REGION from lambda and G from operators. | a for site/stops; b lambda/structural admission, R1/R5/R6 |
| 180,183,186,188,190,192,194,206,217,219,221,224: `scan_nud_payload` | Another ordered candidate chain; failed candidates restore input. Same large inherited reaches. | a for NUD; c dispatch duplication, R2/R3/R5; b lambda, R6 |
| 242: `scan_path_segment_payload` | Try path vocabulary, then expression LED vocabulary; W+G. | a mode; c repeated classification, R2 |
| 260–266: `scan_token` | Choice of identifier, float, integer, colon, punctuation, unknown. A plain integer’s digits can be scanned twice. | c, R1/R3 |
| 281: `contextual_word_suffix_follower` | Peek next scalar for `?`/`!`. | c by retaining maximal-word evidence, R2 |
| 292–293: `introduced_body_indentation_normalized` | Observe future trivia without consuming it; G. | a layout context; c repeated observation, R4 |
| 316: `scan_type_nud_payload` | Try `for` before general type payload; 4C. | a type-NUD mode; c classify maximal word once, R2 |
| 329–340: `scan_type_payload` | Two nested choices, including variant probe before path/number/punctuation. Reach includes LINE. | c dispatch; b type structure, R1/R7 |
| 349: `scan_malformed_equals` | `starts_with('=')` before scanning malformed operator token; 1C then W. | L; recovery interpretation b, R1 |
| 361–369: `scan_pattern_nud_payload` | Probe whether `..` starts a range, then rescan marker; literal/symbol alternatives. | b, R8; exact Y2 range equivalent absent |
| 381,384–391: `pattern_range_start` | Check `..`; construct `LexRecover` and detached `In`; scan marker; inspect upper-bound start. G+W. | b, R8; detached probe c |
| 407–419: `pattern_range_upper_starts` | Detached `In`, `current_item`, then test newline and integer kind. G+W, possibly EOF. | b, R8; carry next Item instead |
| 432–445: `pattern_range_after_expression_item` | Inspect following dot/operator character, then invoke upper-bound probe. G+W. | b, R8; split-dot repair is removable with consistent token cuts |
| 460,464,468: `scan_pattern_payload` | Symbol/arrow/tail retries according to arm stops and leading trivia. | a stops; b symbol/arm interpretation, R1/R8 |
| 480–491: `scan_pattern_tail_token` | Two nested choices for colon/path/signed integer/integer/range/equals/pipe/recovery. W, plus range probe. | c dispatch; b signed/range classification, R8 |
| 497–499: `scan_pattern_negative_integer` | Consume `-`, transactionally scan an integer; one unbounded-length numeric token. | b; Y2 has unsigned Number recognition, R3/R8 |
| 510,513–517: `scan_pattern_range_marker` | First try exact spread marker; otherwise detached parser scans a negative integer after `..`, then real cursor consumes only `..`. W. | b; redundant numeric probe c, R8 |
| 530–534: `scan_pattern_malformed_fixed_operator` | `starts_with(".."/"="/"->")`, then operator-shaped scan. 1–2C+W. | L token recognition; b recovery grouping, R1 |
| 540: `scan_operator_shaped_unknown` | Transaction per operator-shaped scalar. Consuming W, one-scalar failed sentinel. | c per-character transaction overhead; ordinary scan retained, R10 |
| 568–572: `scan_trivia_part` | Choice of horizontal/newline/line-comment/block-comment scanners. 1–2C dispatch, comment body through EOF. | L; c dispatch overhead, R4 |
| 579: `scan_horizontal_whitespace` | Transaction per whitespace scalar. Consuming run. | c transaction overhead, R4 |
| 593: `scan_newline` | Optional LF after CR. 1C. | L, R4 |
| 610: `scan_line_comment` | Transaction per non-newline scalar. Consuming LINE. | c transaction overhead, R4 |
| 626,630: `scan_block_comment` | Try nested opener and closer at every position. Consuming REGION; each failed delimiter test ≤2C. | L; c avoid repeated transactions, R4 |
| 701,706,712,725: `scan_fenced_block_comment_body` | EOF, nested delimiters, CRLF, then fence-line judgment. Local checks plus LINE at transitions. | a fence context; L delimiter recognition |
| 747: `fenced_comment_line_decision` | Judge future physical line using passed fence; LINE. | a; retain boundary authority, reduce duplicated line scans |
| 831–852: `scan_lambda_backslash` | Borrow suffix; scan **all parameters and exact arrow**, then consume only backslash. REGION through EOF/fence. | b, R6; sign-off required for admission-policy changes |
| 864–865: `lambda_reference_suffix` | `&` plus maximal identifier, non-consuming. W. | b as part of header grammar, R6 |
| 876–910: `lambda_parenthesized_suffix` | Balance parentheses; skip trivia/literals; retain original cursor. REGION. | b, R6 |
| 922–968: `lambda_literal_suffix` | Quote-run, escapes, complete literal, physical fence transitions. REGION. | b duplicate literal recognizer, R6/R12 |
| 981–985: `lambda_inline_suffix` | Non-consuming logical trivia scan; G. | b header grammar; c rescan, R4/R6 |
| 991,995,996: `scan_identifier` | First-scalar category peek; transactional continuation/suffix sentinels. W. | L; c sentinel transaction overhead, R2 |
| 1010–1012: `scan_nud_keyword` | Retry three fixed complete-word recognizers. ≤6C each. | a keyword mode; c classify one maximal word, R2 |
| 1016–1023: `scan_statement_keyword` | Retry eight complete-word recognizers. ≤7C each. | a statement mode; c, R2 |
| 1029–1041: `source_identifier` | Non-consuming maximal identifier and optional suffix. W. | c when used to predict a later identifier scan, R2 |
| 1053–1061: `source_declaration_head` | Probe full identifier, or sigil+identifier. W. | b declaration admission, R9 |
| 1094–1096,1105–1109: `scan_arm_arrow` / `is_exact_arm_arrow` | `->` plus one operator-shaped follower check. 3C. | L cut; a active-arrow mode |
| 1113–1124: `scan_exact_word` | Prefix and word-boundary peek, then consume same spelling. Fixed word+1C. | c duplicated recognition, R2 |
| 1140–1143: `identifier_starts` | One-scalar category predicate. | L |
| 1147–1156: `scan_path_segment` | Identifier attempt, otherwise sigil+identifier. W; underscore classification reads accepted text. | a vocabulary; c dispatch duplication, R2 |
| 1169,1172: `scan_declaration_type_parameter` | Identifier attempt followed by path-segment scanner that attempts identifier again. W. | c repeated identifier attempt, R2 |
| 1210–1222: `scan_integer` | Tentative radix prefix+digit run, otherwise decimal. W. | L; c avoid numeric-prefix replay, R3; Y2 radix parity unverified |
| 1235,1237,1242: `scan_float` | Scan decimal run; tentative fraction/exponent; reject complete scan if neither exists. W; caller then scans integer again. | c, R3 |
| 1254: `scan_float_exponent` | Optional sign transaction before required digits. 1C+W. | L; c transaction overhead, R3 |
| 1267,1272–1274: `scan_radix_digit_run` | Digit transaction, then `_`+digit transaction, per iteration. 1–2C each. | L; c per-character transaction overhead |
| 1294–1297: `scan_punctuation` | Try second dot to reject `..`; require second colon for `::`. 2C. | L; b preserve `..` as a token instead of repairing split dots, R1 |
| 1310,1436,1449: `scan_expression_colon` / `scan_type_colon` / `scan_pattern_colon` | Three copies of lone-colon versus `::` check. 2C. | L; c duplicate implementation, R1 |
| 1324,1334,1358,1463: symbol-colon scanners / `is_expression_symbol_item` / `scan_expression_payload_with_symbols` | Inspect identifier start after colon; classify the same surface in several layers. 1C beyond colon. | b, R1/R8; Y2 also has contextual `scan_symbol` at `scan/mod.rs:140` |
| 1377–1388: `scan_type_forall` | Fixed `for`+boundary check, then consume it again. 4C. | a type mode; c maximal-word classification, R2 |
| 1398: `scan_type_effect_row_apostrophe` | Peek `'[` but consume only apostrophe. 2C. | b, R1/R7 |
| 1412–1422: `scan_type_polymorphic_variant_colon` | **Unconditionally find current line first**, then inspect `:{` or search first `|` and following `:Tag`. LINE. | b structural decision, R7; unconditional line scan c |
| 1485,1495,1508–1512: assignment/exact-equals scanners | Single-character assignment versus exact operator-shaped `=` boundary. 1–2C. | a vocabulary; L cut; b interpretation, R1 |
| 1517–1521: `scan_record_spread_marker` | Read `..`, try a following operator-shaped scalar, reject if present. 3C. | L cut; b spread/range owner, R1/R8 |
| 1531–1537: `scan_lparen` / `scan_lbrace` | Invoke general punctuation scanner, then reject other punctuation kinds; callers retry scanners. ≤2C. | c use direct opener recognition, R1 |

**Other lexical files**

| File:line(s), function | Inspection/speculation and reach | Class / comparison |
|---|---|---|
| `lexical/current_item.rs:60`, `current_item` | Transaction around complete trivia+payload acquisition; failed optional payload restores all acquisition. G+payload. | L atomic acquisition; redundant surrounding transactions c, R4 |
| `lexical/current_item.rs:100,103,119,142–164`, `scan_current_item` | Block-comment/trivia alternatives, EOF checks, payload dispatch. G+payload. | a fence/mode; L scanning |
| `lexical/current_item.rs:210`, `classify_line` | Non-consuming fence-line judgment before accepted prefix consumption. LINE. | a |
| `lexical/expression_item.rs:53,108–128`, `expression_item_with_doc_boundary` / `scan_expression_item_lexical_with_doc_boundary` | Scan trivia to predict doc boundary, then `current_item` scans it again. G+marker. | a doc permissions; c repeated trivia, R4/R13 |
| `lexical/expression_item.rs:159`, `scan_expression_payload_with_literals` | Literal attempt before ordinary expression vocabulary. Quote run or 2C. | a literal mode; L |
| `lexical/expression_item.rs:178,182`, `scan_expression_literal_payload` | Rule opener versus string opener transactions. 2C/quote run. | a NUD; L, R12 |
| `lexical/expression_item.rs:189–192`, `scan_pattern_literal_payload` | Count quote run, then scan malformed run or literal opener. W. | a pattern literal mode; c repeated quote counting, R12 |
| `lexical/expression_item.rs:197`, `scan_pattern_quote_literal_payload` | Count quote run before calling scanner that counts it again. W. | c, R12 |
| `lexical/operator_scan.rs:41–81`, `scan_operator_fenced` | Longest-first trie candidates; word boundary; future trivia; adjacent `(`/`:`; stop/value-start evidence. Operator length+G+next prefix. | a for NUD/LED, stops, baseline/table/fence; c repeated/eager successor work, R5 |
| `lexical/operator_scan.rs:109–129`, `scan_dangling_operator_fenced` | Second trie selection after normal selection fails; inspect follower. Operator length+G. | a recovery role; c repeated trie/trivia, R5; exact dangling recovery differs |
| `lexical/operator_scan.rs:154–169`, `dangling_follower_fenced` | Future trivia, indentation, stop, first visible scalar. G+1C. | b recovery admission; use retained successor evidence |
| `lexical/operator_scan.rs:175–180`, `operator_boundary` | One following scalar for word-operator boundary. | L, R5 |
| `lexical/operator_scan.rs:194–209`, `raw_value_start` | 1–2C start category or another operator-trie traversal. | b value-start/fixity evidence; Y2 also probes, R5 |
| `lexical/observation.rs:31–39,49–56`, contextual-word functions | Inspect accepted Item, then `?`/`!` suffix if it was cut as an operator. 1C. | c retain maximal-word boundary evidence, R2 |
| `lexical/stops.rs:45–54`, `active_stop` | First scalar, `::` exclusion, exact-arrow predicate. ≤3C. | a stop set; b stop decision, R1/R5 |
| `lexical/trivia.rs:15–17`, `lone_colon_after_fenced_trivia` | Scan trivia, then `:` versus `::`. G+2C. | b, R15 |
| `lexical/trivia.rs:27`, `newline_indentation_after_fenced_trivia` | Scan future trivia to obtain indentation. G. | a layout; c replay, R4 |
| `lexical/trivia.rs:53–80`, three observation entrypoints | Forward to raw trivia observer with physical/logical mode. G. | a explicit mode; c duplicate acquisition, R4 |
| `lexical/trivia.rs:107,121–206`, `observe_fenced_trivia_mode` | Scan spaces/newlines/comments/fence lines without moving live input. G through EOF/fence. | a fence/context; c observation followed by real scan, R4 |
| `lexical/trivia.rs:261–305`, `observe_ordinary_trivia` | Scan entire ordinary trivia; block comment text is traversed again to derive layout when non-opaque. G. | c repeated work, R4 |
| `lexical/trivia.rs:325,330`, `ordinary_block_comment_suffix` | Balance nested comment using borrowed suffix. REGION. | L inside observer; duplicated consuming implementation c, R4 |
| `lexical/trivia.rs:360`, `observe_line` | Fence-line classification while observing future trivia. LINE. | a |
| `lexical/trivia.rs:397,406,416,426`, `observe_block_comment` | Another nested-comment recognizer plus CRLF/fence handling. REGION. | a fence; c duplicate scanner responsibility, R4 |
| `lexical/yumark.rs:96–103`, `is_yulang_fence_info` | Reject line breaks, find first horizontal-delimited atom. Supplied info span. | a fence mode; L |
| `lexical/yumark.rs:120–138`, `judge_fence_line` | Find whole physical line before testing close/prefix transition. LINE. | a; c repeated line discovery |
| `lexical/yumark.rs:190–202`, `strict_close` | Indentation, marker width, all remaining horizontal suffix. LINE. | a fence facts; L |
| `lexical/yumark.rs:226–238,252–263`, quote marker functions | Count contiguous/prefixed chevrons and gaps; inspect complete suffix for explicit quote. LINE. | a quote mode; L |
| `lexical/yumark.rs:268–272`, `horizontal_len` | Maximal horizontal run. | L |
| `lexical/yumark.rs:288`, `PhysicalLine::new` | `find('\n')`; no newline means remaining source. LINE. | L line segmentation; repeated use c |
| `lexical/opaque_region.rs:62`, `finish_opaque_opener` | Apostrophe follower distinguishes markup group. 1C. | a recovery vocabulary |
| `lexical/opaque_region.rs:94–124`, `Scan::ready` | At physical line starts/EOF, inspect fence line before consuming prefix. LINE. | a |
| `lexical/opaque_region.rs:134`, `Scan::next` | LF after CR. 1C. | L |
| `lexical/opaque_region.rs:163–196`, `Scan::opaque` | Dispatch comments, quoted markup, rule/string openers; count quote run. 1–2C/run; accepted scan consumes REGION. | a opaque recovery; L |
| `lexical/opaque_region.rs:208–224`, `Scan::string` | Quote run/end, escape, interpolation region. Consuming REGION. | a string mode; L |
| `lexical/opaque_region.rs:233–248`, `Scan::code` | Balanced delimiters and opaque-region dispatch. Consuming REGION. | a recovery context; L |
| `lexical/opaque_region.rs:258–270`, `Scan::yumark` | Horizontal/quote prefixes and fence opener. Prefix/run+3C. | a; L |
| `lexical/opaque_region.rs:291,300–315`, `Scan::nested_fence` | `yulang` prefix, quote prefixes, closing ticks. Consuming REGION. | a; L; exact equivalence to header scanner unverified |
| `operator_table.rs:65–81`, matching entrypoints | Source matching and boundary-valid value-start matching. Operator-length prefix. | a operator environment; L, R5 |
| `operator_table.rs:701–718`, `OperatorTrie::longest_source_match_from` | Recursively inspect longer source prefix; offer terminals on unwind, longest first. Max registered matching spelling+one scalar. | L; candidate callbacks may rescan suffix, R5 |
| `operator_table.rs:723–728`, `operator_boundary_source` | Following scalar category. | L |

**Parser-side source decisions**

These are not lexer responsibilities merely because they receive a `LexIn`.

| File:line(s), function | Inspection/speculation and reach | Class / comparison |
|---|---|---|
| `statement.rs:441–450,479–509`, `classify_statement_item_normalized_at` / `classify_statement_item_lexical_at` | Sequential declaration-family admission; several families inspect the same suffix after visibility. Several words+G. | b, R9; c repeated observations |
| `statement.rs:1150,1409`, indented/braced statement slots | Pass suffix to member-doc admission. Marker/LINE. | a doc position; R13 |
| `statement.rs:1268,1509`, retry functions | Repeat statement admission at recovery candidates. Same reach as classifier. | b, R9; retain admission with Item |
| `declaration/binding.rs:91,102`, `binding_follower_normalized` | Future trivia and maximal word after visibility. G+W. | b, R9 |
| `declaration/binding.rs:136`, `observed_after_head` | Future trivia after an already-probed word. G. | b; c replay, R4/R9 |
| `declaration/binding.rs:147–158,169–177`, named-head / definition predicates | Further trivia+declaration-head or exact-equals evidence. G+W/2C. | b, R9 |
| `declaration/struct_decl.rs:92–99`, `prefixed_struct_candidate_normalized` | Trivia+next maximal word equals `struct`. G+W. | b, R9 |
| `declaration/type_decl.rs:70–78`, `prefixed_type_candidate_normalized` | Same for `type`. G+W. | b, R9 |
| `declaration/mod_decl.rs:62–69`, `prefixed_mod_candidate_normalized` | Same for `mod`. G+W. | b, R9 |
| `declaration/role_decl.rs:176–184`, `prefixed_role_candidate_normalized` | Same for `role`. G+W. | b, R9 |
| `declaration/impl_decl.rs:156–164`, `prefixed_impl_candidate_normalized` | Same for `impl`. G+W. | b, R9 |
| `declaration/cast_decl.rs:191–199`, `prefixed_cast_candidate_normalized` | Same for `cast`. G+W. | b, R9 |
| `declaration/enum_decl.rs:182,193,204–214`, `prefixed_enum_candidate_normalized` | Keyword plus optional required named head, separated by observed trivia. Up to two words+G. | b, R9 |
| `declaration/error_decl.rs:182,193,204–214`, `prefixed_error_candidate_normalized` | Same structure for error declaration. | b, R9 |
| `declaration/act_decl.rs:188,199,205,209,228–234`, `prefixed_act_candidate_normalized` | Host/`act`/named-head admission, repeatedly observing gaps. Several words+G. | b, R9 |
| `declaration/use_decl.rs:283,290,304–308`, `prefixed_use_candidate_normalized` | `use` plus optional target-start evidence. G+two words. | b, R9/R10 |
| `declaration/use_decl.rs:1777–1780`, `use_tree_starter_source` | Group character or maximal identifier; `mod` can cause repeated `source_identifier`. W. | b; c duplicate word recognition, R10 |
| `declaration/fields.rs:1177–1184`, `named_declaration_fields_next_field_candidate` | Future trivia+same-line lone colon after accepted field name. G+2C. | b, R7; retain next token |
| `declaration/impl_tail.rs:689–695`, `colon_following_has_physical_newline` | Scan all following trivia for physical newline evidence. G. | a layout/recovery; c repeated trivia, R4 |
| `declaration/doc_comment.rs:47`, `doc_comment_selected_lexical` | Marker judgment across current Item spelling and live suffix. Marker/LINE. | a statement position; R13 |
| `declaration/doc_comment.rs:95–115`, `doc_comment_declaration_normalized` | Opening-line newline search and closing indentation. LINE; accepted document parsing is committed. | a document mode; L |
| `declaration/doc_comment.rs:166–183`, `line_doc_after_equals` | Trim horizontal gap; check `--` versus `---` and saved line boundary. Gap+3C. | a attachment permission; b parser attachment, R13 |
| `declaration/doc_comment.rs:203–208,226–231,241–246`, trailing/member selectors | Reinvoke marker admission with source and position. Marker/LINE. | a; c repeated admission, R13 |
| `declaration/doc_comment.rs:259,271–275`, `member_trailing_doc` | Repeat selection; otherwise trim gap and inspect `--`/`---`. Gap+3C. | a; c repeated evidence, R13 |
| `sequence.rs:45`, `DeclarationDocContext::new` | `find(['\r','\n'])` before parsing body. LINE. | a attachment boundary; c derive from shared line metadata, R4/R13 |
| `declaration/operator_header.rs:145–195`, `next_slot_item` | Tentative **whole parenthesized operator name**, numeric power run, exact/malformed equals, then expression fallback. W/LINE to rejection/EOF. | b parentheses/header structure, R14; c retries |
| `declaration/cast_decl.rs:1746–1749`, `scan_cast_item_lexical` | Exact equals attempt, then raw `=` prefix and malformed operator attempt. W. | b recovery classification; R1 |
| `declaration/declaration_companion.rs:1079–1080`, `scan_companion_item_lexical` | Peek `::`, deliberately consume one unknown scalar in form mode. 2C. | a companion-form mode; b recovery interpretation |
| `declaration/use_decl.rs:1648–1657`, `scan_version_token` | Following digit and maximal version characters. Consuming W after local validation. | L, R10 |
| `declaration/use_decl.rs:1695–1700`, `scan_operator_token` | Peek each next operator character before consuming. W. | L, R10 |
| `declaration/use_decl.rs:1801–1807`, `operator_name_follows` | Acquire next complete Item, save Boolean externally, **return `None` deliberately** to roll back. G+W. | b, R10; c reacquisition |
| `declaration/use_decl.rs:1910–1916`, `path_segment_retry` | Same deliberate-rollback operator-name probe during recovery. G+W. | b, R10; c duplicated probe |
| `expression/for_decl.rs:93–128,140`, `emit_optional_label_normalized` | Scan label and following Item, deliberately return `None`; accepted label is scanned again. Two Items, including G and expression-payload reach. | b, R11; c replay |
| `expression/operator_chain.rs:1069–1083`, `optional_nud_item` | Complete Item acquisition, then reject boundary/EOF/non-NUD and roll it back. G+payload, potentially lambda REGION. | b NUD admission; c reacquisition, R6 |
| `declaration/type_parameters.rs:93–112`, `parameter_item_normalized` | Acquire parameter Item, then reject based on gap/newline/form/spelling. G+W. | a parameter form; c reacquisition, R2 |
| `expression/delimited.rs:379–386`, `delimited_baseline_from_source` | Observe future trivia for delimited baseline. G. | a layout; c replay, R4 |
| `expression/tails/with_body.rs:50–55`, `with_tail_normalized` | Observe trivia+lone colon before acquiring actual Item. G+2C. | b, R15 |
| `expression/tails/with_body.rs:290`, `retry_with_inline_body_normalized` | Statement admission again during retry. Several words+G. | b, R9 |
| `type_expr/record.rs:469–478,492–515`, malformed-name wrapper/probe | Detached suffix scans **successive type Items**, tracking nesting until colon/boundary/newline. REGION; each Item can run LINE variant probe. | b, R7; c scan-then-recovery replay |
| `type_expr/record.rs:583–591,604–608`, field-head wrapper/probe | Detached scan of next type Item, then colon/indentation test. G+W/LINE. | b, R7; c reacquisition |
| `type_expr/record.rs:1011–1028`, `observe_type_item` | Observe trivia, create detached `In`, try pipe, scan type NUD. G+payload/LINE. | b, R7; common mechanism for preceding probes |
| `rule/mod.rs:689–690`, `scan_rule_equals` | `="` special case before exact equals. 2C. | a rule vocabulary; b literal/equality interpretation, R12 |
| `rule/mod.rs:702–707`, `scan_rule_fixed` | Recognize `..`, `*?`, `+?`, then single-character rule punctuation. ≤2C. | L, R12 |

The indentation observer also has these direct callers; each has **G** reach and class **a**, with repeated scanning removable as **c/R4**:

| File | Function and call line |
|---|---|
| `expression/tails/assignment.rs` | `assignment_tail_normalized`:38 |
| `expression/tails/colon.rs` | `colon_tail_normalized`:46 |
| `expression/tails/with_body.rs` | `with_tail_normalized`:72 |
| `expression/case_like.rs` | `colon_block_normalized`:288; `arm_body_normalized`:851 |
| `expression/if_expr.rs` | `colon_body_normalized`:468 |
| `expression/for_decl.rs` | `colon_body_normalized`:581 |
| `declaration/binding.rs` | `binding_body_normalized`:352 |
| `declaration/mod_decl.rs` | body dispatch at :477 |
| `declaration/enum_decl.rs`, `declaration/error_decl.rs` | `parse_body_item_normalized`:495 in each |
| `declaration/act_decl.rs` | body dispatch at :731 |
| `declaration/cast_decl.rs` | `cast_definition_body_normalized`:1089 |
| `declaration/role_decl.rs` | body dispatch at :445 |
| `declaration/impl_tail.rs` | `colon_body_normalized`:466 |
| `declaration/fields.rs` | `parse_indented_fields_normalized`:257 |
| `declaration/declaration_variant.rs` | `declaration_variant_sequence_normalized`:98 |

Range lookahead is additionally invoked by `expression/operator_chain.rs:657`, `tail_normalized`, and `expression/case_like.rs:1113` during arm selection. Both inherit the detached range-bound scan described above.

**Literal scanning**

| File:line(s), function | Inspection/speculation and reach | Classification |
|---|---|---|
| `literal/mod.rs:89`, `scan_string_opener_token` | Count entire quote run before consuming selected opener width. W. | L; mode a, R12 |
| `literal/mod.rs:130`, `accept_string_close` | Count entire quote run, compare mode/width. W. | a mode; L |
| `literal/mod.rs:260–355`, `string_literal_with_interpolation_body` | Repeated transactional prefix/text/close/percent/escape alternatives and source `%` peek at :304. Consuming chunks plus quote-run/fence observations. | a literal mode; c repeated dispatch/observations, R12 |
| `literal/mod.rs:394–436`, `emit_string_interpolation` | Optional format text, `%` and `{` recognition, boundary checks. Format chunk through structural stop/fence. | a literal state; L, R12 |
| `literal/mod.rs:443,449`, `emit_string_interpolation` | Borrow suffix before/after committed child solely to update origin. | N |
| `literal/mod.rs:487–527`, `scan_multiline_literal_item` | Check stop predicate before each scalar, count quote runs, CRLF, fence-line transition. Accepted text is consumed once. | a mode/fence; L; repeated line/quote discovery c |
| `literal/mod.rs:550,554,884–893`, stop predicates | `%`, escape, brace, quote-run close, interpolation `{`. 1C or quote run. | a literal mode; L |
| `literal/mod.rs:612–637`, `emit_string_escape` | Try Unicode opener; inspect string close, two quotes, EOF; otherwise consume target. 1–2C/quote run. | a escape/mode; L, R12 |
| `literal/mod.rs:655–745`, `emit_unicode_escape` | Hex/end attempts; EOF/`%`/string-close probes; fence/prefix checks. Hex run+LINE. | a escape state; L; c repeated boundary observation |
| `literal/mod.rs:788`, `current_boundary_item` | Acquire boundary Item through transaction. G/LINE. | a; L |
| `literal/mod.rs:837`, `scan_unicode_start` | `starts_with("u{")`, then consume same two bytes. | L |
| `literal/mod.rs:843–853`, `scan_unicode_hex` | First-byte hex test and repeated hex-byte tests while consuming. W. | L |
| `literal/mod.rs:906–941`, `literal_line_transition` | EOF, structural-start callback, fence-line judgment, accepted-prefix suffix. LINE+local delimiter. | a explicit literal/fence state |
| `literal/mod.rs:1021–1022`, `quote_run` | Non-consuming maximal quote run; multiple callers may count the same run. | L helper; duplicated calls c |
| `literal/rule_literal.rs:38`, `scan_expression_rule_literal_opener_token` | `~"` prefix. 2C. | L, R12 |
| `literal/rule_literal.rs:66–78`, `scan_pattern_literal_opener_token` | Rule opener attempt, quote count, string-opener retry. W. | a pattern mode; c repeated quote work, R12 |
| `literal/rule_literal.rs:122–208`, `rule_literal_normalized` | Prefix/text/quote/brace/colon alternatives. Text chunk through structural stop/fence. | a rule-literal state; L, R12 |
| `literal/rule_literal.rs:234–284`, `emit_rule_lazy_capture` | Peek `{`, parse captured name/body, try closing brace/name. Chunk/REGION. | b capture structure, R12; ordinary local token cuts L |
| `literal/rule_literal.rs:298`, `scan_rule_capture_name` | Transaction per identifier continuation scalar. W. | c transaction overhead, R12 |
| `literal/rule_literal.rs:315,322,339`, structural/text scanners | Prefix-aware structural-character attempt and text stop set. 1C+LINE when fenced. | a literal/fence mode; L |

**Yumark source inspection**

These belong to the Yumark parser/scanner, not the ordinary Yulang lexer. None of the embedded `SyntaxIn::new` calls below is a throwaway lexical probe.

| File:line(s), function | Inspection and reach | Classification |
|---|---|---|
| `yumark/judge.rs:153–173`, `judge_document_marker_parts` | Reconstruct marker from Item+suffix; strict block-marker suffix test. Marker/LINE. | a position; L, R13 |
| `yumark/judge.rs:196–197`, `judge_line_document` | Find physical newline to establish line-document extent. LINE. | a line mode; L |
| `yumark/judge.rs:218–223`, `judge_block_close` | Active block-close context, marker and strict horizontal suffix. LINE. | a; L |
| `yumark/judge.rs:233–273`, `judge_chunk` | Terminator/blank/newline/block/inline dispatch; `\`+identifier start; otherwise maximal raw text. Chunk/LINE. | a explicit context; L |
| `yumark/judge.rs:284–321`, `active_terminator` | Active delimiter, quote depth, indentation, strict closing line. 1–3C/prefix/LINE. | a; L |
| `yumark/judge.rs:327–354`, `line_structure` | Hash/digit runs, list marker, fence and quote classification. Run/LINE. | a line-start context; L |
| `yumark/judge.rs:372–386`, `quote_marker_facts` | Contiguous chevrons and strict suffix; otherwise prefix run. LINE. | a quote context; L |
| `yumark/judge.rs:395–398`, `strict_horizontal_suffix` | Scan horizontal gap to newline/EOF. LINE. | L |
| `yumark/judge.rs:401–402`, `raw_fence_opener_suffix` | **`suffix.contains('\n')`**, potentially through remaining source. | L line-existence evidence; c reuse known physical-line facts, R13 |
| `yumark/judge.rs:405–409`, `physical_newline_offset` | Search next LF. LINE. | L |
| `yumark/judge.rs:414–428`, newline/blank-line helpers | CRLF/LF or horizontal run+newline. 1–2C/run. | L |
| `yumark/judge.rs:431–444`, `prefix_quote_marker` | Chevron/horizontal-prefix loop. Prefix run. | a quote vocabulary; L |
| `yumark/judge.rs:447–474`, raw-text/boundary helpers | Scan raw chunk while checking inline delimiter/start boundaries. Chunk/LINE. | a active close; L |
| `yumark/grammar.rs:314–321`, `physical_line` | Find LF and indentation. LINE. | L; repeated calls c |
| `yumark/grammar.rs:490,536`, parenthesized Yulang/condition parsers | Current-byte dispatch and close check. 1C. | b parser delimiter ownership, R13 |
| `yumark/grammar.rs:549–673`, `parse_block_iterative` | Inspect physical line, document close, heading/list/quote/fence/command forms. LINE. | a block mode; b structure, R13 |
| `yumark/grammar.rs:735,805,906–912`, section/list/quote openers | Next physical line or current content classification. LINE. | b structure, R13 |
| `yumark/grammar.rs:1048`, `horizontal_end` | Borrowed forward horizontal run. Gap. | L |
| `yumark/grammar.rs:1055–1061`, `strict_colon_body` | Current colon plus all remaining line bytes horizontal and newline exists. LINE. | b command-body grammar, R13 |
| `yumark/grammar.rs:1075`, `parse_doc_argument` | Next byte is closing bracket. 1C. | b parser delimiter ownership |
| `yumark/grammar.rs:1090–1104`, `parse_do_candidate` | `(do`+word-boundary+`)`; once admitted it commits/recover-consumes. 3C+scalar initially. | b; **not a rollback parse**, R13 |
| `yumark/grammar.rs:1178–1313`, `parse_command_line` | Current-byte argument/body dispatch, following `[`/`{`/`;`, strict colon, paragraph fallback. 1C/LINE. | b; output checkpoints classify already-consumed content, R13 |
| `yumark/grammar.rs:1425–1481`, `parse_braced_command_body` | Byte dispatch, identifier-start follower after slash, CRLF, argument/body punctuation. 1–2C. | a body mode; b structure |
| `yumark/grammar.rs:1515–1556`, `braced_parent_boundary` | Physical line, parent closer/quote transition and logical indentation. LINE. | a parent-frame context |
| `yumark/grammar.rs:1569–1578`, `finish_after_braced` | Discover current line; classify remaining accepted range as horizontal/text. LINE. | b parser continuation |
| `yumark/grammar.rs:1672–1819`, `parse_my_tail` | Current-byte binder/equals/body/semicolon decisions; physical-line discovery. 1C/LINE. | b, R13 |
| `yumark/grammar.rs:1863,1878,1902`, `parse_use_tail` | Parenthesized payload/close/semicolon decisions. 1C. | b, R13 |
| `yumark/grammar.rs:1963–2064`, `parse_if_chain_line` | Argument/body decisions; inspect subsequent blank/branch lines and `\elsif`/`\else` boundaries. Multiple LINEs. | b, R13 |
| `yumark/grammar.rs:2117–2123,2199–2206`, fence parsers | Info classification; fence-line judgment followed by physical-line discovery again for body lines. LINE. | a fence mode; c duplicated line segmentation |
| `yumark/grammar.rs:2263–2324`, `paragraph_last_line` | Scan all future paragraph lines and classify each, before inline parsing consumes paragraph. REGION through EOF. | b paragraph boundary; c prepass, R13 |
| `yumark/grammar.rs:2349–2444`, `parse_inline_owned_until` | Current closer, newline spelling, judged chunk and active-frame close. 1–2C/chunk. | a active frame; b structure |
| `yumark/grammar.rs:2509,2526,2540`, `finish_group_tail` | Following `(`/`:`/argument opener classifies completed group as link/apply/group. 1C. | b; no cursor rollback |
| `yumark/grammar.rs:2559`, `parse_raw_destination` | `find(')')` to supplied limit; immediately consumes selected span. REGION, possibly paragraph/EOF. | L consuming destination scan |
| `yumark/grammar.rs:2580,2587`, `parse_inline_reference` | Following argument opener/semicolon. 1C. | b |
| `yumark/grammar.rs:2616,2643,2661,2679`, heading/list/quote/fence predicates | Each calls general `judge_chunk`, which can scan a complete raw-text chunk even when only a Boolean is needed. Chunk/LINE. | c avoid full fallback chunk scan for category predicates, R13 |
| `yumark/grammar.rs:2634–2635`, `terminal_colon` | Trim line suffix backwards and inspect colon. LINE suffix. | b |
| `yumark/grammar.rs:2715–2723`, `identifier_end` | Borrowed maximal identifier scan before emitting same range. W. | L |
| `yumark/adapter.rs:809–810`, `first_physical_line` | Find LF, inspect preceding CR. LINE. | L |

**Per-file transaction census**

Every production lexical `token(...)` invocation is located here or in the lexer/literal rows above. “Acquire” means successful consumption is retained; it is not automatically speculative parsing.

| File | T | Functions and invocation lines |
|---|---:|---|
| `cursor.rs` | 1 | `SyntaxIn::token`:232 |
| `cursor/recovery/emit.rs` | 1 | `lexical`:40 |
| `lexical/lexer.rs` | 87 | All dispatch/scalar transactions above; additionally `scan_case_label_payload`:306. Choice expressions:260,329,334,480,488,568. |
| `lexical/current_item.rs` | 3 | `current_item`:60; `scan_current_item`:103,119 |
| `lexical/expression_item.rs` | 7 | outer acquire:53; doc payload:128; literal alternatives:159,178,182,190,192 |
| `lexical/observation.rs` | 1 | `is_contextual_word_lex`:56 |
| `lexical/position.rs` | 1 | `suffix_marker`:5 — N, pointer/length only |
| `declaration/act_decl.rs` | 3 | `act_item_normalized`:1120; `scan_act_item`:1151,1158 |
| `declaration/binding.rs` | 2 | `binding_target_normalized`:302; `binding_statement_item_normalized`:544 |
| `declaration/cast_decl.rs` | 3 | `cast_item_normalized`:1693; `scan_cast_item_lexical`:1746,1749 |
| `declaration/declaration_companion.rs` | 1 | `scan_companion_item_lexical`:1080 |
| `declaration/declaration_variant.rs` | 7 | `drive_variant_sequence`:189; `parse_variant_contents`:448,466,544; `variant_item_normalized`:692; `variant_item_lexical`:713,719 |
| `declaration/derives.rs` | 3 | `next_clause_item_normalized`:227; `next_clause_item_lexical`:257; `clause_gap_continues`:291 |
| `declaration/enum_decl.rs` | 2 | `enum_item_normalized`:869; `enum_item_lexical`:908 |
| `declaration/error_decl.rs` | 2 | `error_item_normalized`:836; `error_item_lexical`:875 |
| `declaration/fields.rs` | 3 | `declaration_item_with_pipe_lexical_normalized`:1263; `scan_declaration_item_lexical`:1298,1304 |
| `declaration/impl_decl.rs` | 3 | `impl_item_normalized`:233; `scan_impl_item`:264,271 |
| `declaration/mod_decl.rs` | 3 | `mod_item_normalized`:710; `scan_mod_item`:739,747 |
| `declaration/operator_header.rs` | 7 | `next_slot_item`:145,191,195; `operator_header_normalized`:278,285,298,364 |
| `declaration/role_decl.rs` | 3 | `role_item_normalized`:719; `scan_role_item`:750,757 |
| `declaration/type_decl.rs` | 3 | `header_boundary`:768; `type_item_normalized`:822; `type_item_lexical`:854 |
| `declaration/type_parameters.rs` | 2 | `parameter_item_normalized`:93,100 |
| `declaration/use_decl.rs` | 11 | `next_use_item`:1614; `scan_use_payload`:1619,1621,1623,1626,1629,1631,1633,1636; probes:1801,1910 |
| `expression/case_like.rs` | 3 | `case_head_item`:247; `arm_body_boundary`:987; `pattern_item_normalized`:1343 |
| `expression/delimited.rs` | 2 | `delimited_baseline_from_source`:379; `error_run`:506 |
| `expression/for_decl.rs` | 5 | label probe/reacquire:93,140; `pattern_slot_normalized`:177; `statement_item_normalized`:738; `outer_boundary`:759 |
| `expression/if_expr.rs` | 1 | `inline_boundary`:641 |
| `expression/lambda.rs` | 1 | `lambda_header_item`:145 |
| `expression/operator_chain.rs` | 2 | `append_nud`:370; `optional_nud_item`:1069 |
| `expression/tails/fixed_access.rs` | 3 | `field_item_normalized`:187; `scan_field_item_lexical`:215; `path_segment_item_normalized`:330 |
| `header.rs` | 3 | `discover_header_with_cursor`:61,158; `operator_selected`:202 |
| `literal/mod.rs` | 28 | main literal loop:260,269,292,299,304,318,326,355; interpolation:394,399,406,431,436,443,449; escape:612,619,622,625,637; Unicode:655,662,673,687,719,727,745; boundary:788 |
| `literal/rule_literal.rs` | 17 | opener:66,78; literal loop:122,130,145,154,195,208; capture:234,238,244,265,275,284; name:298; structural:315,322 |
| `pattern/mod.rs` | 3 | `pattern_from_primary_with_recovered_tail_stops_normalized`:865; `pattern_item_normalized`:968; `pattern_nud_item_normalized`:988 |
| `root_statement.rs` | 1 | `root_error`:364 — N suffix borrowing |
| `rule/mod.rs` | 13 | `next_rule_item`:646; `scan_rule_payload`:659; `scan_rule_token`:667,670,673,676,679,680,681,682,683; equals:690; identifier continuation:748 |
| `statement.rs` | 1 | `statement_item_normalized`:1663 |
| `type_expr/mod.rs` | 6 | `type_item_with_pipe_lexical_normalized`:993,1000; NUD counterpart:1041,1048; error-run counterparts:1091,1138 |
| `type_expr/record.rs` | 3 | malformed-name probe wrapper:469; field-head wrapper:583; detached pipe attempt:1022 |
| **Total** | **251** | |

Files appearing in the source-decision inventory but absent from this census have **T=0**. Other production files have no direct source lookahead/transaction site identified by this audit.

Ordinary acquisition wrappers in the census are **L** when they supply failure atomicity. Pure `Some(predicate(...))` transactions are **N** as rollback mechanisms; their redundant transaction overhead is **c**. Their underlying contextual-word inspection remains the separately classified site in `lexical/observation.rs`.

**Cursor, sink and state checkpoints: important distinctions**

| File:line(s) | Actual behavior |
|---|---|
| `cursor.rs:230–242`, `SyntaxIn::token` / `map` | Construct lexical views of the **live** suffix. These are bridges, not detached probes. `token` supplies rollback; `map` delegates to `check`. |
| `cursor.rs:190–193`, `LexRecover::mark/rollback` | Recovery mark is `()` and rollback does nothing. There is no mutable lexical semantic state being restored. |
| `cursor.rs:67–76,138–156` | Output checkpoints support `start_node_at`; they do not restore cursor or erase speculative sink output. **N**. |
| `yumark/grammar.rs:633,1138,1171,1260,1974,2405,2434,2492` | Output checkpoints for recovery wrapping and delayed node classification. No source/sink rollback. **N**. |
| `yumark/adapter.rs:225,409–411,522–524,599,658–659` | Output-position checkpoint implementations/delegation. **N**. |
| `yumark/frame.rs:147–161` | `begin/commit/rollback` API exists, but no production call sites were found; uses are in tests. Do not count this as active parser rollback. |
| `yumark/grammar.rs:374,417,1600,1637` | `SyntaxIn::new` runs committed embedded expression/pattern/use parsing against a streaming output. Not probe-and-discard parsing. |

The actual transaction contract is at `crates/chasa-recover/src/parser.rs:144–149`: `token` checkpoints and rolls input/recovery back on `None`. `maybe` itself adds **no transaction** (`:158–175`); `check` adds no input checkpoint (`input.rs:235–247`). Consequently, “every combinator layer rolls everything back” is not accurate for this checkout.

**Header scanning and recovery scanning**

| File:line(s), function | Reach and classification |
|---|---|
| `header.rs:61,88–113`, `discover_header_with_cursor` | Header Item acquisition, doc/use/operator admission. G+words. b/R9/R14. |
| `header.rs:188,202–228`, `operator_selected` | Binding precedence check; scan visibility/lazy modifier Items, save Boolean, deliberately return `None`. Up to two following Items+G. b/R9/R14; replay c. |
| `header.rs:240–255`, `skip_opaque_body` | Consume body until top-level layout boundary; CRLF/indent checks. REGION through EOF. L; Y2 also skips operator bodies, R14. |
| `header.rs:276–310`, `opaque_region` | Comment/string/rule/markup opener dispatch and quote count; consumes accepted region. L with recovery mode a. |
| `header.rs:334`, `finish_opaque_opener` | Apostrophe follower; 1C. a. |
| `header.rs:344–346`, `string_region` | Quote-run/end recognition while consuming body. REGION. a+L. |
| `header.rs:372`, `code_region` | Consume balanced region, recursively dispatch opaque content. REGION. a+L. |
| `header.rs:393–404`, `yumark_region` | Prefix/gap/fence opener checks while consuming. REGION. a+L. |
| `header.rs:425,434–448`, `fence_region` | Language prefix, quote-prefix and fence-close checks. REGION. a+L. |
| `root_statement.rs:364–371`, `root_error` | Borrow suffix and classify already-scanned opener before committed opaque recovery. N for borrowing; a for recovery vocabulary. |
| `virtual_statement_block.rs:236`, `retry_statement` | Invoke statement admission on recovery candidate. Same source reach as statement classifier; b/R9. |
| Declaration error-run calls at `act_decl.rs:1229`, `mod_decl.rs:809`, `role_decl.rs:828`, `impl_tail.rs:805`, `declaration_companion.rs:1038` | Reuse statement admission while scanning recovery. b/R9; repeated source classification c. |

`remainder().len()/as_ptr()` bookkeeping in declaration Item scanners, `lexical/position.rs`, literal interpolation coordinates, and type error-run scanners is **N**. Likewise, `.find(...)` over CST children, trivia arrays, operator definitions, or open-node arrays is not source lookahead.

**Top 10 by forward reach**

These are static reach rankings; several tie because no fixed source-length bound exists.

| Rank | Site | Maximum inspected suffix |
|---:|---|---|
| 1 | `lexer.rs:831` lambda admission and helpers | Whole candidate header, balanced parameters and opaque literals; EOF/fence |
| 2 | `type_expr/record.rs:492` malformed-name probe | Successive nested type Items until recovery boundary/newline/EOF |
| 3 | `lexical/trivia.rs:83` observer family | Entire trivia/comment suffix through EOF/fence |
| 4 | `operator_scan.rs:41` normal operator candidate selection | Operator prefix, entire following trivia, then value-start prefix |
| 5 | `operator_scan.rs:109` dangling operator selection | Operator prefix and following trivia through EOF/fence |
| 6 | `lexer.rs:407` range-upper probe | Following trivia plus complete integer/token; EOF possible |
| 7 | `yumark/grammar.rs:2263` paragraph prepass | Entire remaining paragraph, potentially document remainder |
| 8 | `yumark/judge.rs:402` fence-opener newline search | Next LF or EOF |
| 9 | `lexer.rs:1412–1420` type variant probe | Current line, potentially remaining source |
| 10 | `yumark/grammar.rs:2559` raw destination | Through `)` or supplied paragraph/inline limit |

Committed opaque scanners also consume arbitrarily large regions, but are not equivalent to reading those regions speculatively and then parsing them again.

**Top 10 by repeated execution/rescanning**

| Rank | Site/path | Evidence and risk |
|---:|---|---|
| 1 | Type variant probe | `lexer.rs:1412` obtains `lines().next()` **before checking for colon**. `scan_type_payload` tries this at :331 before ordinary identifiers. A long same-line type application repeatedly searches shrinking line suffixes: static quadratic byte-scan risk. |
| 2 | Malformed record-name probe | `record.rs:496–515` scans many type Items, each potentially triggering the preceding line scan, then committed recovery scans the region again. |
| 3 | Lambda admission | Header balancing/literal skipping happens before real Pattern parsing. Nested lambda candidates can inspect overlapping large suffixes. Quadratic behavior is plausible; no measured bound established. |
| 4 | Operator successor classification | `operator_scan.rs:44–63` observes trivia and computes `raw_value_start` for every offered candidate, even when with-value/without-value fixity results agree. Normal failure may trigger dangling selection again. |
| 5 | Boolean Yumark category predicates | `heading_facts`, `list_marker_end`, `quote_facts`, `raw_fence_opener` each invoke full `judge_chunk`, whose fallback scans raw text. `paragraph_last_line` can invoke several on the same line. |
| 6 | Statement-family admission | `statement.rs:482–506` asks multiple declaration predicates to rescan the same visibility suffix. This is bounded family fanout, not by itself proof of quadratic complexity. |
| 7 | Binding admission | Rechecks contextual declaration candidates and following gaps; duplicates work already performed by family dispatch. |
| 8 | Range/signed-bound admission | `pattern_range_start` → marker probe → negative-integer probe → upper Item probe, followed by actual marker/bound scanning. Large numeric tokens are repeatedly recognized. |
| 9 | For-label probe | Label+successor are scanned, rolled back, then label and later successor are acquired again. Successor acquisition inherits expensive expression recognition. |
| 10 | Use operator-name probes | Normal/recovery paths have separate acquire-and-deliberately-rollback implementations; accepted next Item is later scanned again. |

Also frequent: per-scalar transactions in identifier, whitespace, comment, digit and rule-name loops. Their local reach is small; the demonstrated concern is constant-factor overhead, not an established asymptotic regression.

**C. How Yulang2 tokenizes — 15 points**

1. It scans on demand from character input; it is not a fully pretokenized token-array parser (`context.rs:87`).
2. A `Lex` contains leading trivia information, kind, text, and retained trailing trivia (`lex.rs:417–421`).
3. `Token<Tag>` adds a grammatical dispatch tag without changing the lexeme (`lex.rs:425–428`).
4. Identifiers are maximal XID words with optional `?`/`!`; classification follows recognition (`scan/mod.rs:257–260`, `:300`).
5. Expression versus statement-head words use explicit `ExprWordMode` (`expr/scan.rs:67–77`, `:151–159`).
6. Pattern versus visibility words use explicit `PatWordMode` (`pat/scan.rs:55–65`, `:101–109`).
7. Stops, indentation, inline mode, ML-argument mode, quote depth and operator table live in `Env`/`State` (`context.rs:20–55`).
8. Contextual word scanners receive stop sets rather than searching future source for grammatical structure (`scan/mod.rs:52–107`).
9. Numbers use one `Number` vocabulary with fraction/exponent components (`scan/mod.rs:117`, `:237–254`).
10. Punctuation is mostly fixed lexemes: `->`, `::`, pattern `..`, then single characters (`scan/mod.rs:152–227`).
11. Some lexemes are deliberately composite: sigil identifiers, `.field`, and context-admitted `:symbol` (`scan/mod.rs:110–149`).
12. Strings emit an opener and mode-sensitive body chunks; they do not lex the entire literal as one token (`string/scan.rs:35–98`).
13. Operators use longest trie matching plus boundary, whitespace, stop and limited value-start evidence (`expr/scan/op/scan.rs:32–81`).
14. Operator lookahead retains the selected token’s trailing trivia rather than observing trivia and always discarding it (`expr/scan/op/scan.rs:50–78`).
15. Structural interpretation—lambda parameters, type variants, pattern tails, visibility dispatch—belongs to parser functions; Y2 still uses choices and some parser checkpoints.

**D. Concrete refactor order**

Tiers are task-allocation judgments using the requested names, not benchmarked model-capability claims. Each step can be reviewed separately; later steps should not be bundled into a lexer rewrite.

Tests below are module paths under `crates/yu-syntax/src/tests`.

| Order | Independent scope | Existing guards | Risk / tier / sign-off |
|---:|---|---|---|
| 1 | Move the cheap `:`/identifier-start rejection before `lines().next()` in `scan_type_polymorphic_variant_colon`. Preserve existing accepted cases exactly. | `type_expr::pv_bar`, especially `lone_polymorphic_variant_tag_remains_rejected`; `normalized` variant cases | Low; **luna**. No intended CST/diagnostic change. |
| 2 | Share the three identical lone-colon cuts; keep existing token kinds and call priorities. | `lexical`, `colon_sequence`, `tails`, `pattern`, `type_expr` | Low; **luna**. No intended output change. |
| 3 | Replace `scan_lparen`/`scan_lbrace` general-punctuation trial with direct fixed opener recognition. | `lexical`, `delimited_recovery`, `expression_recovery`, `unary_lambda` | Low; **luna**. Preserve all failure consumption contracts. |
| 4 | Remove repeated identifier attempt in `scan_declaration_type_parameter`; preserve underscore/sigil distinctions. | `declaration::{type_decl,struct_decl,enum_decl,error_decl}` | Low; **terra**. No intended output change. |
| 5 | Make `raw_value_start` conditional on the fixity comparison actually needing it; preserve prefix/nullfix special handling. | `operators`, notably raw-successor, no-value, prefix/nullfix controls; `lexical` fenced operator cases | Medium; **terra**. No intended output change. |
| 6 | Replace per-scalar transaction loops with consuming runs plus local stopping tests, one lexical transaction per token. Start with horizontal whitespace, then identifiers/digits/comments separately. | `lexical`, `literal`, `rule_literal_recovery`, `string_literal_recovery`, `doc_comment_matrix` | Low–medium; **terra**. Preserve malformed-token extent and newline ownership. |
| 7 | Scan numeric prefix/digits once and classify integer/float without replaying a whole integer after failed float recognition. | `lexical::expression_numeric_scanning_distinguishes_floats_from_integer_boundaries`, radix/separator tests, `type_numeric_scanning_does_not_admit_float_tokens` | Medium; **terra**. **Sign-off if malformed numeric cuts or diagnostics change.** |
| 8 | Replace keyword trial lists with one maximal-word recognition and explicit context classification; retain dynamic word-operator priority and suffix rules. | `operators`, `lexical`, `if_expr`, `unary_lambda::binder_bypasses_registered_word_operator_selection`, declaration modules | Medium–high; **sol**. **Sign-off for any keyword/operator admission change.** |
| 9 | Replace use operator-name rollback probes with retained next-Item evidence shared by normal/recovery paths. | `declaration::use_decl`, `normalized::normalized_use_path_operator_probe_is_strict_and_transactional` | Medium; **terra**. Preserve recovery boundaries; output changes need sign-off. |
| 10 | Make For label admission consume/retain its two inspected Items once, with explicit pending-Item handoff. | `for_statement`, `normalized` label-probe cases | Medium; **terra**. **Sign-off if label ownership, recovery or CST changes.** |
| 11 | Consolidate declaration admission after visibility into parser-owned token/state dispatch; eliminate per-family raw-suffix rescans. | `declaration::{binding,type_decl,struct_decl,enum_decl,error_decl,role_decl,impl_decl,cast_decl,act_decl,use_decl}`, `normalized`, braced/indented recovery modules | High; **sol**. **Architecture and admission/diagnostic sign-off.** |
| 12 | Move next-field and malformed-name colon decisions into a parser-owned field state machine; retain scanned Items instead of detached `observe_type_item`. | `type_expr::{record_field_recovery,record_sequence_recovery}`, `normalized` next-field/malformed-name probe cases | High; **sol**. **Recovery/CST sign-off**, especially malformed-name skeleton ownership. |
| 13 | Emit consistent `..`/sign evidence and let Pattern parser choose spread/range/signed bound. Preserve expression operators independently. | `pattern::range`, especially negative bounds and expression-operator controls; `case_like`, `normalized`, `lexical` | High; **sol**. **Sign-off for token fusion/CST, malformed bounds and handoff changes.** |
| 14 | Remove lexer’s line-wide bar-variant search; parse colon/tag/bar structure from ordinary tokens with explicit type context. | `type_expr::pv_bar`, `type_expr::pv_recovery`, `normalized`, annotation/record/forall tests | High; **sol**. **Sign-off**: lone tags, same-line restrictions and first-bar behavior are observable. |
| 15 | Remove complete lambda-header recognition from lexer; design parser-owned candidate handling that preserves dynamic `\` fallback and existing accepted headers. | `unary_lambda`, particularly complete/nonmatching headers, dynamic-backslash priority, opaque parentheses, fences and direct CST tests | Highest; **sol**. **Owner design sign-off required before implementation.** |
| 16 | Give Yumark category predicates narrow recognizers; share physical-line facts and remove paragraph/line rediscovery where contracts allow. Separate this from ordinary lexer work. | `yumark`, `yumark_cell`, `yumark_cell_witness`, `doc_comment*`, `root`, `structural_diagnostic` | Medium–high; **terra** for narrow predicates, **sol** for paragraph ownership. **Sign-off if paragraph boundaries/CST/diagnostics change.** |

The lambda constraint is explicit in [the authoritative gap-closure addendum](/home/momota1029/rust/yulang/notes/design/2026-11-04-parser-gap-closure-addendum.md:90): the whole header must match before a lambda token is emitted. Moving responsibility is a design change even if common valid examples keep identical CSTs. [Parser rules](/home/momota1029/rust/yulang/rules/parser-chasa.md:48) also require approval for grammar, recovery, CST/AST, diagnostics or dispatch changes.

**E. Uncertainties and verification limits**

- **No timing or allocation measurements were run.** Rankings are static. The unconditional type-line search has a concrete overlapping-suffix path; other quadratic risks remain unverified.
- **Y2 is not behaviorally equivalent to current Y3.** I did not find corresponding signed/range-pattern parsing or bar-variant parsing in the inspected Y2 pattern/type implementations. Its token cuts are useful evidence, not a drop-in implementation.
- **A global context-free operator tokenization policy is not settled by this audit.** Registered spelling overlap, exact fixed-token boundaries and dynamic operator priority need a defined contract before changing cuts.
- **Lambda fallback is unresolved architecturally.** Preserving “complete header wins, otherwise dynamic backslash” while eliminating all rescanning requires a parser-owned retained candidate representation or an approved admission change. I have not selected one.
- **Several existing recovery rules require future colon evidence.** Replacing their probes with committed state machines must preserve exact malformed-region ownership; a simpler Y2 recovery path does not establish equivalence.
- **Necessary lexical boundary reads remain.** CRLF, word boundaries, compound punctuation and delimiter widths still require small local inspection. “Almost no lookahead” is achievable as a responsibility rule, not literally zero character inspection.
- **The census is source-level.** It counts explicit production transaction invocations and identifies source-inspection implementations; it is not a dynamic invocation count or compiler-expanded call graph.
- Executed read-only `rg`, numbered source reads, Python in-memory searches, `git show`, `git grep`, tag/HEAD resolution and status inspection. **No tests, builds or benchmarks were run; no files were changed or saved.** Final Git status was clean.
