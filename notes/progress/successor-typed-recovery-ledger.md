# Successor typed recovery callsite ledger

Updated: 2026-09-08, branch `yulang3`; Type/PV checkpoint `634d5b46`, Pattern
primary/tail checkpoint `afaa3b24`, sequence checkpoint `5de04545`,
default-Expression checkpoint `7832ab2f`; required Expression operands, their
explicit caller roles, shared Expression delimiters, and fixed Field/Path tails
are privately constructed.

Status: construction inventory, not independent or aggregate certification.
Authority: typed-output amendment §8 and the current recovery-authority and
owner-specific amendments linked from `notes/design/INDEX.md`. This record
does not select syntax/recovery policy. The initial Type/PV inventory was an
M0 pass. Pattern entries accompany their M2 construction under the user's
no-subagent instruction; self-checks are not independent certification.

## Reading the ledger

This is the single accumulating ledger for O3/O4. The Type/PV portion and
Pattern-owned modules map every current publication site to a
semantic helper; the remaining O3b SCC is explicitly open.
Source aliases are relative to `crates/yu-syntax/src/rewrite/`:

- `T` = `type_expr.rs`; `D` = `type_expr/delimited.rs`;
  `R` = `type_expr/record.rs`; `F` = `type_expr/forall.rs`;
  `V` = `type_expr/variants.rs`.
- `P` = `pattern.rs`. Its table's test prefixes are under
  `rewrite::tests::pattern::recovery::`; P's retained caller/policy controls
  are in the parent `rewrite::tests::pattern::` module.
- `PD` = `pattern/delimited.rs`; the delimiter table's test prefixes are
  under `rewrite::tests::pattern::recovery::delimited::`, `sequence::`, or
  `default_expression::`, with the unique function prefix selecting the module.
- Test names/prefixes are under `rewrite::tests::type_expr::`. `Q` denotes
  its parent test module; a named child such as `pe_recovery` is its module.
  Prefixes denote the existing finite test family, not tests to invent later.
- `M` / `E` = Missing / Error. `B` = inspected abstract-boundary coordinate,
  otherwise current Item remaining-start **after only permitted owner
  emission**. `I` = emitted Item extent. `Rng` = emitted contiguous Error run.
  Missing range is always `B..B`. Incomplete-row EOF head uses the returned
  successor coordinate; this is noted explicitly below.
- `[]` = empty unexpected array; `native(I)` = one actual-category Token;
  `other(Rng)` = one OtherCharacter Token; `items` = the ordered per-Item
  categories from `required_type_primary_unexpected_category`.
- Every expectation is a singleton with the same role/range as its site,
  sources `COMMITTED_RECOVERY_RULE`, primary index `0`. `Ty`, `Id`, `Sep`,
  `Path`, `Binder`, `BinderGap`, `PayloadGap` expand to TypeExpression,
  Identifier, DelimitedSequenceSeparator, TypePathSegment, ForallTypeBinder,
  TypeBinderBoundary, TypePayloadBoundary; punctuation is written literally.
- `prior` means all already committed/reserved records, never sorted later.
  `outer first` means an enclosing structured PV Error reserves its record
  before recursively generated records. An Error prefix precedes a retry's
  records; a distinct close Missing follows item recovery. No same-slot
  Missing is added merely because that slot's Error reached a boundary.
- State `C` means private typed construction mapped and locally tested, not
  O4/O6 certified. RB-T/RB-PV name the obligations; their local controls and
  remaining aggregate scope are listed separately below.

## Type/PV semantic publication sites

The M/E entries name both their Missing and Error producers. Shared helper
dispatch is explicit in the owner/slot column; each source role is covered.

| source location | matrix/addendum row | owner/slot | kind | sentinel/run | range formula | unexpected array | ordered expectations/source flags | primary | continuation/pending Item | recovery-order predecessor | focused test | ordinary control | RB row | migration state |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| T::required_type_expr_inner_normalized | T1; required-Type roles | explicit caller Missing role; anonymous Primary | M | fresh absent primary | B..B | [] | Ty / committed | 0 | identical Item, found=false | prior | required_recovery::required_missing_* | empty / `A` | RB-T | C |
| T::required_type_expr_inner_normalized | T1; Equals ownership | Primary | E | total malformed run | Rng | items | Ty / committed | 0 | retry NUD or return protected Item | prior; before retry | Q::required_type_primary_*; equals_recovery | `@A`, `=A` / `A` | RB-T | C |
| T::type_path_tail_normalized | T2b | PathSegment | M | fresh path boundary | B..B | [] | Path / committed | 0 | Type tail receives same Item | prior | Q::type_path_segment_missing_* | `A::` / `A::B` | RB-T | C |
| T::retry_type_path_segment_normalized | T2b; sixth terminal | PathSegment | E | run plus eligible block-comment prefix | Rng incl. emitted prefix | other(Rng) | Path / committed | 0 | same frontier-advanced retry; ordinary space stays outside | prior; before retry | Q::type_path_segment_error_*; Q::type_path_segment_malformed_trivia_* | `A::@ B` / `A::B` | RB-T | C |
| T::type_arrow_rhs_normalized | T2a | ArrowRhs | M | fresh RHS boundary | B..B | [] | Ty / committed | 0 | identical protected Item after allowed emission | prior | Q::type_arrow_rhs_missing_* | `A->` / `A->B` | RB-T | C |
| T::retry_type_arrow_rhs_normalized | T2a; fifth terminal | ArrowRhs | E | run; eligible record-only retry-leading extent | Rng, optionally through retry leading; CST excludes it | other(record range) | Ty / committed | 0 | retry Item/CST leading unchanged | prior; before retry | Q::type_arrow_rhs_publishes_*; Q::type_arrow_rhs_record_extension_* | `A ->@ B` / `A->B` | RB-T | C |
| D::emit_delimited_item_missing | T3a | CallArgument | M | initial/post-separator absence | B..B | [] | Ty / committed | 0 | caller pending or explicit separator consumed by Call | prior; before close | Q::type_call_t3a_missing_slots_* | `T(,)`, `T(` / `T()` | RB-T | C |
| D::retry_type_call_argument_normalized | T3b; seventh terminal | CallArgument | E | Unknown payloads plus eligible native retry-leading | Rng incl. emitted retry prefix | other(Rng) | Ty / committed | 0 | same advanced retry; caller/close outranks seal | prior; before retry/close | Q::type_call_t3b_argument_errors_* | `T(@ A)` / `T(A)` | RB-T | C |
| D::emit_inherited_separator_missing | T3a | CallArgumentSeparator | M | next Call item without boundary | B..B | [] | Sep / committed | 0 | retry same item | prior item records | Q::type_call_t3a_inherited_ml_* | `G T(F A)` / `T(F A)` | RB-T | C |
| D::emit_delimited_close_missing | T3a | close(TypeCall, Parenthesis) | M | absent close | B..B | [] | `)` / committed | 0 | return complete pending Item | prior item/error | Q::type_call_t3a_missing_slots_* | `T(A` / `T(A)` | RB-T | C |
| D::retry_type_call_close_normalized | T3b | close(TypeCall, Parenthesis) | E | each nonboundary close-phase Item, Unknown payload | I | other(I) | `)` / committed | 0 | close-only retry, actual close or protected Item | prior; before next close error/M | Q::type_call_t3b_close_errors_* | `T(A] )` / `T(A)` | RB-T | C |
| D::emit_delimited_item_missing; D::retry_type_noncall_item_normalized | T4P; current-Item P/E | ParenthesizedItem | M/E | absent slot / forward native run | B..B / Rng | [] / other(Rng) | Ty / committed | 0 | P retry, caller/fence Item preserved | prior; before retry/close | pe_recovery::pe_item_slots_* | `(,)`, `(@ A)` / `(A)` | RB-T | C |
| D::emit_inherited_separator_missing | T4P; inherited ML | ParenthesizedSeparator | M | next item lacks separator | B..B | [] | Sep / committed | 0 | same item, OuterTypeApply activation only | prior item | Q::type_parenthesized_t4p_inherited_ml_* | `G (F A)` / `(F A)` | RB-T | C |
| D::emit_delimited_close_missing; D::type_delimited_normalized | T4P; current-Item P/E | close(ParenthesizedTypeGroup, Parenthesis) | M/E | absent close / each unclaimed wrong close | M uses Item remaining-start; E uses I | [] / native(I) | `)` / committed | 0 | protected close pending; local error resumes P | prior item/error | pe_recovery::pe_closes_*; Q::shared_delimited_horizontal_* | `(A] )` / `(A)` | RB-T | C |
| D::emit_delimited_item_missing; D::retry_type_noncall_item_normalized | T4E; current-Item P/E | EffectRowItem | M/E | absent slot / forward native run | B..B / Rng | [] / other(Rng) | Ty / committed | 0 | E retry, full caller/fence Item | prior; before retry/close | pe_recovery::pe_item_slots_* | `'[,]`, `'[@ A]` / `'[A]` | RB-T | C |
| D::emit_inherited_separator_missing | T4E; inherited ML | EffectRowSeparator | M | next item lacks separator | B..B | [] | Sep / committed | 0 | same item, OuterTypeApply activation only | prior item | pe_recovery::effect_separators_* | `G '[F A]` / `'[F A]` | RB-T | C |
| D::emit_delimited_close_missing; D::type_delimited_normalized | T4E; current-Item P/E | close(EffectRowType, Bracket) | M/E | absent close / unclaimed wrong close | B..B / I | [] / native(I) | `]` / committed | 0 | protected Item pending; local error resumes E | prior item/error | pe_recovery::pe_closes_*; Q::shared_delimited_horizontal_* | `'[A) ]` / `'[A]` | RB-T | C |
| D::emit_delimited_item_missing; D::retry_type_noncall_item_normalized | T4B | BracketRowItem | M/E | absent slot / forward native run | B..B / Rng | [] / other(Rng) | Ty / committed | 0 | B retry or protected Item | prior; before close/arrow | bracket_recovery::bracket_row_item_errors_*; bracket_recovery::bracket_row_missing_* | `T [,] -> U` / `T [A] -> U` | RB-T | C |
| D::emit_inherited_separator_missing | T4B | BracketRowSeparator | M | next distinct item without separator | B..B | [] | Sep / committed | 0 | same item; no inherited B activation | prior item | bracket_recovery::bracket_row_missing_* | `T [A{}] -> U` / `T [A B] -> U` | RB-T | C |
| D::emit_delimited_close_missing; D::retry_bracket_row_close_normalized | T4B | close(BracketRow, Bracket) | M/E | absent close / each unclaimed wrong close | B..B / I | [] / native(I) | `]` / committed | 0 | close-only, never reenters item list | prior item/error; before arrow slot | bracket_recovery::bracket_row_close_retry_* | `T [A)] -> U` / `T [A] -> U` | RB-T | C |
| R::emit_record_field_missing; R::retry_record_run_normalized(Field) | T5a/f | RecordField | M/E | empty field / kind-matching malformed run | B..B / Rng | [] / other(Rng) | Id / committed | 0 | retry name/colon skeleton; preserve immediate caller verdict | prior; before close | record_sequence_recovery::record_sequence_* | `{,a:A}`, `{@}` / `{a:A}` | RB-T | C |
| R::emit_record_field_missing; R::retry_record_run_normalized(Name) | T5b | RecordFieldName | M/E | local colon / approved malformed-name skeleton | B..B / Rng | [] / other(Rng) | Id / committed | 0 | continue same field at local colon | prior; before colon/type | record_field_recovery::record_field_missing_*; record_sequence_recovery::record_sequence_and_name_* | `{:A}`, `{@:A}` / `{a:A}` | RB-T | C |
| R::emit_record_field_missing; R::retry_record_field_slot_normalized | T5c | RecordFieldColon | M/E | absent colon / forward malformed colon run | B..B / Rng | [] / other(Rng) | `:` / committed | 0 | exact local colon or Type retry; boundary ends slot | prior; before RHS | record_field_recovery::record_field_errors_* | `{a A}`, `{a @ A}` / `{a:A}` | RB-T | C |
| R::emit_record_field_missing; R::retry_record_field_slot_normalized | T5d | RecordFieldType | M/E | fresh missing RHS / malformed RHS run | B..B / Rng | [] / other(Rng) | Ty / committed | 0 | Type retry or complete caller Item | prior colon; before nested Type | record_field_recovery::record_field_errors_*; record_field_recovery::record_field_caller_* | `{a:}`, `{a:@ A}` / `{a:A}` | RB-T | C |
| R::emit_record_field_missing; R::retry_record_run_normalized(Separator) | T5e | RecordFieldSeparator | M/E | missing separator / malformed separator run | B..B / Rng | [] / other(Rng) | Sep / committed | 0 | retry admitted field; immediate caller verdict retained | prior field | record_sequence_recovery::record_sequence_* | `{a:A; b:B}` / `{a:A,b:B}` | RB-T | C |
| R::record_boundary_normalized; R::retry_record_run_normalized(Close) | T5g | close(NamedRecordType, Brace) | M/E | absent close / native kind-matching close-only run | B..B / Rng | [] / other(Rng) | `}` / committed | 0 | real close or complete caller Item; no field retry | prior field/error | record_sequence_recovery::record_unclaimed_closes_* | `{a:A]}` / `{a:A}` | RB-T | C |
| F::emit_forall_missing; F::retry_forall_normalized | T6 | ForallBinder | M/E | first binder absent / phase-owned run | B..B / Rng | [] / other(Rng) | Binder / committed | 0 | apostrophe binder, colon or protected Item | prior; before colon/body | forall_recovery::forall_missing_*; forall_recovery::forall_forward_errors_* | `for @`, `for, T` / `for 'a:T` | RB-T | C |
| F::emit_forall_missing; F::emit_forall_separator_binder | T6 | ForallBinderBoundary | M/E | adjacent binder / fresh comma or semicolon after binder | B..B / I | [] / other(I) | BinderGap / committed | 0 | same binder or next phase Item | prior binder | forall_recovery::forall_boundary_recovery_* | `for 'a'b:T`, `for 'a,:T` / `for 'a 'b:T` | RB-T | C |
| F::emit_forall_missing; F::retry_forall_normalized | T6 | ForallColon | M/E | required colon absent / phase-owned run | B..B / Rng | [] / other(Rng) | `:` / committed | 0 | local colon, binder, body candidate or boundary | prior binder/error; before body | forall_recovery::forall_missing_*; forall_recovery::forall_forward_errors_* | `for 'a` / `for 'a:T` | RB-T | C |
| F::emit_forall_missing; F::retry_forall_normalized | T6 | ForallBody | M/E | actual colon followed by absence / malformed run | B..B / Rng | [] / other(Rng) | Ty / committed | 0 | one full Type or pending boundary, no fake close | prior head | forall_recovery::forall_forward_errors_*; forall_recovery::forall_fence_* | `for 'a:@ T` / `for 'a:T` | RB-T | C |
| T::emit_leading_type_head_missing; T::type_leading_bracket_row_normalized; T::retry_leading_type_head_normalized | T7a/b corrected | LeadingEffectTypeHead | M/E | completed/incomplete leading row then required head | B..B (incomplete EOF: successor) / Rng | [] / other(Rng) | Ty / committed | 0 | one primary retry; kind-matched malformed nesting; caller pending | row records first | leading_row_recovery | `[e]@ T`, `[e]` / `[e]T` | RB-T | C |
| T::emit_bracket_arrow_missing; T::retry_bracket_arrow_normalized | T4A; T7c corrected | BracketRowArrow | M/E | mandatory arrow absent / forward malformed arrow run | B..B / Rng | [] / other(Rng) | `->` / committed | 0 | actual arrow or RHS retry, boundary ends slot | row records first; before RHS | bracket_arrow_recovery | `F [e] @ U` / `F [e] -> U` | RB-T | C |
| V::emit_polymorphic_variant_missing; V::recover_polymorphic_variant_run(Tag) | PV1 | PolymorphicVariantTag | M/E | empty tag / malformed tag run | B..B / Rng | [] / other(Rng) | Id / committed | 0 | same tag retry or immediate caller/close | prior; before retry/close | pv_recovery::pv_missing_slots_*; pv_recovery::pv_boundaryless_* | `:{,,A}`, `:{@A}` / `:{A}` | RB-PV | C |
| V::type_polymorphic_variant_tag_after_wrong_kind_normalized | PV1; structured reservation/extent/order | PolymorphicVariantTagName | E | structured wrong-kind Type with tight tails | sealed Item start..verified emitted nested end | other(full range) | Id / committed | 0 | payload continuation; native PV close excluded | outer first, before all nested records | pv_recovery::pv_wrong_kind_*; Q::polymorphic_variant_structured_* | `:{123::T}` / `:{Tag T}` | RB-PV + RB-T | C |
| V::recover_polymorphic_variant_run(Payload) | PV1 | PolymorphicVariantPayload | E | malformed payload run after real gap | Rng | other(Rng) | Ty / committed | 0 | same payload retry or protected Item | prior tag; before retry | pv_recovery::pv_payload_recovery_* | `:{A @ Int}` / `:{A Int}` | RB-PV | C |
| V::type_polymorphic_variant_payload_normalized via emit_polymorphic_variant_missing | PV1 | PolymorphicVariantPayloadBoundary | M | adjacent actual payload NUD | B..B | [] | PayloadGap / committed | 0 | parse same NUD | tag/name records first | pv_recovery::pv_local_punctuation_*; Q::polymorphic_variant_* | `:{A(Int)}` / `:{A (Int)}` | RB-PV | C |
| V::type_polymorphic_variant_tags_normalized via emit_polymorphic_variant_token_error | PV1 | PolymorphicVariantTagSeparator | E | local semicolon | I | native(I) | Sep / committed | 0 | retry tag-list phase, no fabricated tag | prior | pv_recovery::pv_local_punctuation_* | `:{;A}` / `:{A,B}` | RB-PV | C |
| V::type_polymorphic_variant_boundary; V::type_polymorphic_variant_tags_normalized | PV1 | close(PolymorphicVariantType, Brace) | M/E | absent close / local unclaimed close | B..B / I | [] / native(I) | `}` / committed | 0 | protected Item or same close responsibility | tag slot/error first | pv_recovery::pv_close_records_*; pv_recovery::pv_local_punctuation_* | `:{]`, `:{A` / `:{A}` | RB-PV + RB-T | C |
| T::type_tail_normalized -> T::type_apply_argument_normalized | T accepted tail / no-recovery proof | ApplyArgument | none | entry only after nonempty trivia plus admitted Type primary | none | none | none | n/a | full accepted argument; nested owners retain roles | nested records only | Q::type_apply_scope_*; Q::type_parenthesized_t4p_* | `F A`, `G (F A)` | RB-T | no own recovery site |

The shared Missing factory in T accepts caller roles but never remaps Error
or nested records. Its production callsite/role mapping is the explicit table
in `2026-09-08-successor-required-type-missing-roles.md`; the Equals amendment
updates Pattern's adapter without changing that mapping. This closes the
Type-callee sites, not the calling owners' raw bypass sites.

## Pattern primary and tail-slot publication sites

These are O3b internal construction entries, not an independently completed
Pattern owner. The Pattern-primary current-Item amendment selects the exact
run/trivia/layout rule; it overrides P1's old malformed retry-space extent.
`Pat` means ExpectedSyntax::Pattern. `C` remains construction-only.

| source location | matrix/addendum row | owner/slot | kind | sentinel/run | range formula | unexpected array | ordered expectations/source flags | primary | continuation/pending Item | recovery-order predecessor | focused test | ordinary control | RB row | migration state |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| P::pattern_from_item_core_normalized; P::recover_pattern_primary_normalized via emit_pattern_missing | P1 | Primary | M | fresh boundary/policy stop/tail | B..B | [] | Pat / committed | 0 | complete caller Item, or current tail resumes | prior | primary_missing_records_*; primary_and_alias_recovery_* | empty / `x` | RB-P | C |
| P::recover_pattern_primary_normalized | P1; Pattern-primary amendment | Primary | E | forward native Item run | Rng, excludes retry leading | other(Rng) | Pat / committed | 0 | caller boundary or same primary/tail; retry gap directly in Pattern | prior, before retry-child records | primary_error_runs_*; primary_tail_slots_* | `@ x` / `x` | RB-P | C |
| P::pattern_from_primary_with_recovered_tail_stops_normalized via emit_pattern_missing_at | P2 | SymbolName | M | immediate identifier probe misses after colon | colon successor..successor | [] | Id / committed | 0 | ordinary tail scanner; no skipped SymbolName run | prior; after colon | primary_missing_records_*; symbol_name_probe_rejection_* | `:` / `:x` with and without colon stop | RB-P | C; Error has no producer |
| P::recover_pattern_alias_binding_normalized via emit_pattern_missing or emit_recovery_error_run | P3 | AliasBinding | M/E | fresh absence / malformed name run | B..B / Rng | [] / other(Rng) | Id / committed | 0 | boundary outranks malformed-name retry; valid Identifier, including as, outranks tail | prior, before following tail | primary_missing_records_*; primary_error_runs_*; alias_error_retry_* | `A as`, `A as @ x` / `A as x`, fresh multiline name | RB-P | C |
| P::pattern_tail_normalized -> pattern_from_item_recording_with_policy_normalized -> primary helpers | P4 | AlternationRhs | M/E | explicit recursive RHS role, not precedence inference | B..B / Rng | [] / other(Rng) | Pat / committed | 0 | full RHS at Alternation threshold; children retain their roles | prior, before nested SymbolName/Alias/Type recovery | primary_missing_records_*; primary_error_runs_*; primary_tail_slots_* | `A \|`, `A \| @ x` / `A \| B as c` | RB-P | C |
| P::pattern_type_annotation_rhs_normalized -> required-Type helper | P8; required-Type roles/Equals | TypeAnnotation Missing; Type::Primary Error | delegated M/E | existing required Type contract | callee B..B / Rng | callee [] / items | Ty / committed | 0 | existing caller-close/Equal/IN policy and completion | prior Pattern records | primary_missing_records_* plus Type required_recovery/equals_recovery | `A \| @ :` / `x: T` | RB-P / RB-T | callee construction mapped; full P8 integration open |

All seven `pattern::recovery` tests reuse exact fresh/frozen records, prior
seeded output, complete Item/EOF comparisons and shifted coordinates as
applicable. SymbolName's isolated rejected lexical probe preserves output,
input identity, record count, next ID and frozen cursor. Primary/tail entry
and recovery attempts are total committed procedures, not speculative
Option-returning owners; their NUD/stop predicates are effect-free borrowed
Item queries. Literal entry probes remain assigned to later SCC/RB work.

## Pattern delimiter publication

The delimiter-slot, sequence-current-Item and default-Expression amendments
govern these internal substeps. All entries are construction-only; the
recursive Expression/literal callees prevent a whole-owner completion claim.
Five child roles pass into P's typed kernel;
Record's two structured roles reserve before entering their canonical child.

| source location | matrix/addendum row | owner/slot | kind | sentinel/run | range formula | unexpected array | ordered expectations/source flags | primary | continuation/pending Item | recovery-order predecessor | focused test | ordinary control | RB row | migration state |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| PD::pattern_delimited -> P kernel | P5 | ParenthesizedElement | M/E | absent element / malformed primary | B..B / Rng excluding retry gap | [] / other(Rng) | Pat / committed | 0 | same element retry or local/caller Item | prior, before close | delimited_missing_slots_*; delimited_child_error_roles_* | `(,a)`, `(@ x)` / `(a,)` | RB-P | C |
| PD::list_item -> P kernel | P6 | ListItem | M/E | absent ordinary element / malformed primary | B..B / Rng | [] / other(Rng) | Pat / committed | 0 | same element or sequence Item | prior, before close | delimited_missing_slots_*; delimited_child_error_roles_* | `[,a]`, `[@ x]` / `[a,]` | RB-P | C |
| PD::list_item spread -> P kernel | P6 | ListSpreadRhs | M/E | absent/malformed RHS after exact DotDot | B..B / Rng | [] / other(Rng) | Pat / committed | 0 | same full Pattern or pending comma/close/fence | prior spread head, before close | delimited_missing_slots_*; delimited_child_error_roles_*; delimited_quoted_fence_* | `[..]`, `[..@ x]` / `[..x]` | RB-P | C |
| PD::record_item colon -> P kernel | P7b/g | RecordNestedPattern | M/E | absent/malformed colon RHS | B..B / Rng | [] / other(Rng) | Pat / committed | 0 | same Pattern or caller Equal/comma/close/fence | prior field colon; before default/close | delimited_missing_slots_*; delimited_child_error_roles_*; delimited_missing_close_order_* | `{a:}`, `{a:@ x}` / `{a:x}` | RB-P | C |
| PD::record_item spread -> P kernel | P7d | RecordSpreadRhs | M/E | absent/malformed spread RHS | B..B / Rng | [] / other(Rng) | Pat / committed | 0 | full Pattern or pending comma/close | prior DotDot, before close | delimited_missing_slots_*; delimited_child_error_roles_* | `{..}`, `{..@ x}` / `{..x}` | RB-P | C |
| PD::pattern_delimited via P::emit_pattern_missing | P7a | RecordItem | M | fresh/repeated comma | B..B after sequence leading emission | [] | Id / committed | 0 | consume same comma, next record item | prior, before next item/close | delimited_missing_slots_* | `{,a}` / `{a,}` | RB-P | C |
| PD::pattern_delimited via Owner::separator_role | P5/P6/P7e; layout correction | ParenthesizedSeparator / ListSeparator / RecordSeparator | M | same-line next item without boundary | B..B after owner emits retry leading | [] | Sep / committed | 0 | same Item enters item phase; qualifying layout has no record | prior item records | delimited_missing_slots_*; delimited_accepted_layout_* | `(a b)`, `[a b]`, `{a b}` / qualifying newlines | RB-P | C |
| PD::missing_close via Owner::closing_owner | P5/P6/P7f | close(ParenthesizedPattern, Parenthesis) / close(ListPattern, Bracket) / close(RecordPattern, Brace) | M | protected caller/fence or EOF | B..B after only permitted EOF leading emission | [] | matching close punctuation / committed | 0 | complete same Item/End, caller leading untouched | all child records, innermost first | delimited_missing_close_order_*; delimited_missing_closes_*; delimited_eof_missing_*; delimited_quoted_fence_* | `(a`, `[a`, `{a` / actual local close | RB-P | C |
| PD::pattern_delimited -> PD::record_item | P7 name admission | RecordFieldName | none | only name or DotDot admitted; spread returns first | none | none | none | n/a | name is committed; malformed heads stay with sequence | none of its own | guarded sole callsite; delimited_accepted_layout_* | `{a}`, `{..a}` | RB-P | exact non-recovery proof |
| PD::recover_sequence_run | P7a; sequence amendment | RecordItem | E | maximal malformed lexical unit | Rng; initial/retry leading excluded | other(Rng) | Id / committed | 0 | same-slot retry or comma/close/EOF/fence; no duplicate Missing | prior records | sequence_error_runs_*; sequence_error_handoff_*; sequence_error_fences_* | `{@,a}`, `{@ @ a}` / `{a}` | RB-P | C |
| PD::recover_sequence_run | P5/P6/P7e; sequence amendment | ParenthesizedSeparator / ListSeparator / RecordSeparator | E | maximal malformed lexical unit | Rng; initial/retry leading excluded | other(Rng) | Sep / committed | 0 | item retry or pending comma/boundary; no separator Missing after Error | prior item records | sequence_error_runs_*; sequence_error_handoff_*; sequence_error_fences_* | `(a; b)`, `[a; b]`, `{a; b}` / comma or layout | RB-P | C |
| PD::recover_record_pattern | P7a; structured scope extension | RecordItem | structured E | complete wrong-kind Pattern including its tails | remaining primary start to pending remaining start or successor if empty; byte-delta sealed | other(Rng) | Id / committed | 0 | retry field/spread, consume separator or preserve full caller/fence | reserved before nested records; prior lexical prefix first | record_wrong_kind_literal_*; record_wrong_kind_primaries_*; record_structured_errors_*; sequence_error_fences_* | `{1,a}`, `{(A}`, `{{1}}` / `(A)`, nested accepted literal | RB-P | C |
| PD::recover_record_pattern | P7e; structured scope extension | RecordSeparator | structured E | wrong-kind Pattern after completed field | same sealed structured Rng | other(Rng) | Sep / committed | 0 | same retry/boundary rule; field-owned same-line colon wins earlier | prior field records, reserved before nested records | record_wrong_kind_primaries_* | `{a 1,b}`, newline Symbol / `{a :tag,b}` | RB-P | C |
| PD::emit_wrong_close -> close_recovery_draft | P5/P6/P7f; sequence amendment | close(ParenthesizedPattern, Parenthesis) / close(ListPattern, Bracket) / close(RecordPattern, Brace) | E | one unclaimed wrong close in either phase | remaining native Item extent including remaining leading | punctuation Close(actual) over Rng | matching close punctuation / committed | 0 | consume once; preserve phase; actual own close wins before caller bits | preceding item/sequence records | sequence_unclaimed_closes_*; existing caller-close matrix | `(])`, `[)]`, `{]}` / native matching or carried caller close | RB-P | C |
| PD::record_default_after_equals -> P::emit_pattern_missing | P7c; default-Expression amendment | RecordDefaultExpression | M | absent/non-NUD default RHS, without entering Expression | B..B after permitted field leading; abstract coordinate or protected caller remaining start | [] | Expression / committed | 0 | empty OperatorChain > Missing; unchanged current Item to sequence; canonical accepted Expression unaffected | earlier nested Pattern; enclosing structured reservation first; before sequence/close | record_default_missing_*; record_default_exact_equals_* | `{a=}`, `{a: =}`, `{a=@ x}` / `{a=1}`, `{a= "x"}` | RB-P / RB-E | C; callee SCC remains open |

The preceding Missing rows' Error counterparts are now mapped separately
above. Sequence attempts are total committed entries; Item-start queries are
effect-free. Structured and lexical recovery do not return speculative `None`.
The eight sequence tests use seeded/frozen/shifted full-record checks, complete
Item/End handoffs and output counts, including nested reservations and emitted
foreign-prefix bounds. Existing output tests retain mismatch/LIFO/discard
validation. This is local RB evidence, not actual header/full certification.

## Local rollback and output evidence

All names below are existing tests in the 470-test run at `634d5b46`.

| obligation | local evidence / exact non-recovery proof | remaining scope |
| --- | --- | --- |
| RB-T initial candidate | Q::rb_t_required_type_probe_rejection_preserves_output_and_input; Q::type_parenthesized_t4p_rejected_probe_preserves_seeded_output_and_context | actual header/full/source identity and aggregate O4 |
| RB-T partial-leading terminals | Q::rb_t_arrow_rhs_rejected_retry_seal_preserves_successor_vector; Q::rb_t_path_segment_rejected_retry_seal_preserves_successor_vector; recovery_output tests for Call eligibility | joint caller integration at O4/O6 |
| RB-T fresh/frozen/seeded reconciliation | Q::type_parenthesized_t4p_frozen_rejection_preserves_all_seeded_cursors; per-owner child modules; required_recovery; equals_recovery | actual header record production/consumption O5 |
| RB-T record probes | R::type_record_malformed_name_colon_probe / type_record_field_head_probe are lexical-only observations; record_sequence_recovery::record_name_authority_and_nested_recovery_do_not_cross_caller_stops; record_field_recovery::record_field_next_head_query_shares_exact_colon_ownership | complete O4 rollback assignment audit, not inferred from green builds |
| RB-T total owners | committed delimiter/forall/record/required-Type attempts return a complete Item/EOF or actual close; they do not speculatively publish then reject | no invented local rollback requirement for a total committed attempt |
| RB-PV candidate/reservation | Q::rb_pv_rejected_candidate_preservation; Q::polymorphic_variant_structured_frozen_mismatches_reject_each_position; Q::polymorphic_variant_recursive_structured_tag_names_are_lifo_and_reusable | actual Yumark facts, frame-pop and following literal at O6 |

## Static inventory and next construction boundary

At `634d5b46`, searching T and `type_expr/` for `emit_missing(`,
`emit_error_item(`, and `start_node(SyntaxKind::Missing|Error)` finds zero raw
constructors. Typed calls use only `emit_recovery_missing`,
`emit_recovery_error_item`, `emit_recovery_error_run`, or the PV structured
operation; every use maps above. `TypeRole::ApplyArgument` has no producer in
rewrite; the admitted-argument-only callsite is the exact non-recovery proof,
not an omitted mandatory slot. EffectRow delegates its slots to D.

The Type/PV private construction inventory is complete. Do not mark O4, O5,
O6, the overall matrix, or the parser replacement complete from this record.
No public/root/header dispatch has changed.

Pattern primary, symbol, alias and alternation sites in `pattern.rs` now have
zero raw Missing/Error constructors. Its two Error-run producers and shared
Missing producer map above; the existing annotation Type callee is typed.
Pattern delimiter/default publication is also mapped above; no raw Pattern
Missing/Error constructor remains.

Required Expression operands are now mapped below. The shared driver emits
the initial role's typed Missing or Error; once a NUD is admitted, nested
owners select their own role. It has one shared total lexical Item operation
for ordinary and sealed Error paths. The saved ` ]` witness now passes; `? ]`
remains an effect-free optional-entry rejection control. This does not close
Expression tails, literal/Statement callers, RB-E, O4 or public adoption.

| source / owner | slot role | M/E | trigger and extent | facts / expected | continuation | local evidence | state |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `driver::required_expr_item_normalized` ordinary wrapper / accepted operand | `Expression(Nud)` | M/E | absence: abstract coordinate, protected remaining start, or ordinary EOF after leading; maximal malformed run | `[]` / `Expression`; `other(Rng)` / `Expression` | preserve boundary or append retry NUD | `expression_recovery::*`, `operators::*` | C |
| `if_expr::condition_normalized` | `IfExpression(Condition)` | M/E | same shared predicate/run; existing caller leading remains outside | `[]` or `other(Rng)` / `Expression` | existing condition-arm handoff | `expression_recovery::required_operand_callers_publish_their_own_roles`, `if_expr::*` | C |
| `case_like::case_like_head_normalized` | `CaseLike(Scrutinee)` | M/E | same shared predicate/run | `[]` or `other(Rng)` / `Expression` | existing case block handoff | `expression_recovery::*`, `case_like::*` | C |
| `case_like::guard_normalized` | `CaseLike(Guard)` | M/E | same shared predicate/run | `[]` or `other(Rng)` / `Expression` | existing arrow handoff | `expression_recovery::*`, `case_like::*` | C |
| `for_decl::iterable_from_item_normalized`, including newline/fence bypass | `ForStatement(Iterable)` | M/E | same predicate plus existing implicit newline bypass; protected Item remains whole | `[]` or `other(Rng)` / `Expression` | body only when iterable is not missing | `expression_recovery::*`, `for_statement::*` | C |
| `for_decl::inline_body_normalized` | `ForStatement(Body)` | M/E | same shared predicate/run | `[]` or `other(Rng)` / `Statement` | existing statement-owner handoff | `expression_recovery::*`, `for_statement::*` | C |

Shared Expression delimiters are now mapped below. The descriptor is the only
role source; a close-only inherited mask protects `)`, `]` and `}` through
nested delimiter scans without exporting ordinary caller stops. This remains
private construction, not RB-E/O4 certification.

| source / owner | slot role | M/E | trigger and extent | facts / expected | continuation | local evidence | state |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `delimited::delimited_items_normalized` Parenthesized / Call / Index / Projection tuple / record | descriptor Item role | M/E | leading/repeated separator absence / maximal lexical item run | `[]` or `other(Rng)` / `Expression` | consume local separator or retry NUD; newline boundary stays pending | `delimited_recovery::*`, `owners::*` | C |
| same common loop | descriptor Separator role | M/E | next Item without boundary, Parenthesized `;`, or maximal malformed separator run | `[]`, native `;`, or `other(Rng)` / `DelimitedSequenceSeparator` | same Item retry or fresh Item after recovered separator | `delimited_recovery::*`, `owners::*` | C |
| same common loop | matching `ClosingDelimiter` role | M/E | absent/protected close or unclaimed wrong close | `[]` or native close / matching punctuation | protected full Item returns; local close Error retries its phase | `delimited_recovery::*`, `owners::*` | C |
| `record_spread_item_normalized` | `Expression(ProjectionRecordSpreadRhs)` | M/E | absent/malformed RHS after exact DotDot | `[]` or `other(Rng)` / `Expression` | protected separator/close/fence pending; no duplicate RHS Missing after Error | `delimited_recovery::*`, `owners::*` | C |

Field/Path fixed tails are now mapped below. The finite local mapper keeps the
name slot separate from the outer tail; Path's lexical retry recognizes sigil
segments without opening grammar inside Error.

| source / owner | slot role | M/E | trigger and extent | facts / expected | continuation | local evidence | state |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tails::field_tail_normalized` | `Expression(FieldName)` | M/E | missing adjacent name / maximal lexical non-name run | `[]` or `other(Rng)` / `Identifier` | protected Item and retry name return to outer tail | `fixed_tail_recovery::*`, `tails::*` | C |
| `tails::path_tail_normalized` | `Expression(PathSegment)` | M/E | missing post-`::` segment / maximal sigil-aware lexical non-name run | `[]` or `other(Rng)` / `Identifier` | retain Path `G*`; protected Item and retry segment return to outer tail | `fixed_tail_recovery::*`, `tails::*` | C |
Pattern literal ownership reaches the mutually
recursive literal/Expression/Statement graph; it remains O3b work, not an
independently migrated Pattern owner.

The following groups remain **Open**, to be expanded in this same ledger as
their construction proceeds: Pattern's literal/Expression callees; Expression
`Colon`/`With` tails,
if/case/Rule/string; canonical Statement and braced/indented/colon/with owners;
declarations/derives/companions; VirtualStatementBlock; all remaining RB-E/P/S/
D/DRV/CMP assignments and post-L7 literal deltas. Existing raw field separator/
close and declaration Missing sites are included, not exempted by the Type
helper's role transport. No unbounded test suite or fresh benchmark was run
for the initial inventory. Pattern construction verification now passes the
expanded 539-test owner/output/literal run, including 54 Pattern tests; benchmark
usage remains zero samples/processes.
