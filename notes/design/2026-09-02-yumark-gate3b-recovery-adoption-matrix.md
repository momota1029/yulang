# Authoritative: Yumark Gate 3b recovery adoption matrix

Status: Authoritative

Approved-by: user through the Gate 3b decision on 2026-09-02

Scope: finite implementation and evidence inventory for
`2026-09-02-yumark-gate3b-canonical-recovery-episode-amendment.md`. This is
that amendment's normative §4/§6 appendix, not a new syntax decision.

## 1. Conventions and common assertions

`R(p)` means `\ref(` + `p` + `)`; payload-local ranges shift by `+5`.
`A(p)` means `[d]:f(` + `p` + `)`; payload-local ranges shift by `+6`.
Ranges are half-open. Every row asserts ordered equality of:

```text
(GrammarRole, range, RecoveryKind, primary ExpectedSyntax)
```

between the embedded AST fact stream and direct committed records. Direct-only
auxiliary expectation unions are not transported. A single-fact row has order
zero; listed multi-fact rows establish their explicit source order.

### Exact range locators

The finite register below uses a source-relative locator where spelling a
numeric offset would obscure the owner.  `span("s")` is the half-open byte
range of the unique indicated spelling in that literal; `before("s")` is the
zero-width range at its start; and `eof` is the literal's byte length as a
zero-width range.  Every listed literal contains the indicated spelling once.
These are exact range contracts, not a search heuristic: the Gate 3b harness
must resolve the locator before parsing and compare the resulting `Range`.

`close(Owner, Delimiter)` abbreviates
`GrammarRole::ClosingDelimiter { owner: ConstructRole::Owner, delimiter:
Delimiter }`.  Other role names below are the corresponding closed
`GrammarRole` variant and slot from `session.rs`; `Missing` and `Error` name
`RecoveryKind`, and the final term names the primary `ExpectedSyntax`.

Each row also asserts the direct generic recovery node, lossless prefix,
precise remainder, full ParseLocal equality except the committed direct
diagnostic-id delta, clean/latest-sink preservation, and balanced embedded
frame. Witness names below are existing ordinary owner tests or the named
owner function when the compact literal is selected from its finite test block.

## 2. Expression recovery owners

| ID | owner family and finite variants | embedded witness and required primary fact | existing owner contract | rollback |
| --- | --- | --- | --- | --- |
| E1 | parenthesized mandatory element | `R((@a))`: `Expression(Nud)`, `6..7`, Error, Expression | `commit_parenthesized_element`; `emit_parenthesized_error` | RB-E |
| E2 | fixed `.` field and `::` path tails | `R(x.)`: FieldName `7..7`, Missing, Identifier; `R(x::123)`: PathSegment `8..11`, Error, Identifier | `fixed_tail_recovery_keeps_missing_and_invalid_rhs_local` | RB-E |
| E3 | borrowed outer call item, separator, and close | `R(,a)`: CallArgument `5..5` Missing Expression; `R(1{})`: CallArgumentSeparator `6..6` Missing DelimitedSequenceSeparator; missing `)` is ArgumentList/Paren | `call_argument_interior_extraction_preserves_ordinary_wrappers` | RB-E |
| E4 | nested legacy call item | `R(f(,a))`: CallArgument `7..7` Missing Expression | `call_tail_recovers_missing_arguments_and_closing_delimiter` | RB-E |
| E5 | index item, separator, close | `R(x[,a])`: IndexItem `7..7` Missing Expression; `R(x[a b])`: IndexSeparator at second item Missing DelimitedSequenceSeparator; `R(x[a)`: IndexTail/Bracket close | `parse_index_tail` / `commit_index_tail` | RB-E |
| E6 | parenthesized separator | `R((a b))`: ParenthesizedSeparator `8..8` Missing comma | `parenthesized_layout_keeps_deeper_newlines_and_same_line_recovery_local` | RB-E |
| E7 | projection recovery cells E7a–E7h below | exact finite register below | `projection_tail_recovery_keeps_typed_slots_local`; `projection_tail_close_recovery_is_owner_safe_on_both_paths` | RB-E |
| E8 | ML argument | payload `f +`: MlArgument at owner gap Missing Expression | `call_and_ml_recovery_keep_owner_boundaries_local` | RB-E |
| E9 | colon RHS, inline argument, indented statement | `R(f:)`: ColonApplication(Rhs) `7..7` Missing Expression | `colon_application_recovery_keeps_commas_and_retries_valid_values` | RB-E |
| E10 | With introducer, body, indented statement | `R(a with)`: WithBody(Introducer) `11..11` Missing colon | `with_body_tail_missing_colon_is_single_typed_recovery_and_retries_body` | RB-E, RB-S |
| E11 | If condition, introducer, body, else body, indented statement | `R(if : x)`: IfExpression(Condition) `8..8` Missing Expression | `parse_if_arm` / `commit_if_arm` | RB-E |
| E12 | case/catch recovery cells E12a–E12i below | exact finite register below | `case_like_recovery_marks_missing_mandatory_slots_once`; `case_like_invalid_arrow_run_recovers_to_the_next_comma_arm`; `case_like_missing_arm_comma_retries_the_next_pattern` | RB-E, RB-P |
| E13 | braced canonical Statement item and separator | `R({@ value})`: BracedStatementBlock(Statement) `6..8` Error Statement; existing missing-separator witness | `ordinary_non_comment_recovery_keeps_ast_non_recovering_and_direct_cst_exact`; `commit_braced_missing_separator_leading` | RB-S |
| E14 | braced Statement close | `R({value)`: BracedStatementBlockExpression/Brace close before borrowed `)` | `emit_braced_close_missing` | RB-S |

## 3. Pattern recovery owners

Pattern rows use `R(case x: <pattern> -> ok)`; a standalone pattern range shifts
by `+13`. The outer role remains a case/for/declaration role when its existing
owner says so.

| ID | finite variants | standalone witness / embedded primary fact | existing owner contract | rollback |
| --- | --- | --- | --- | --- |
| P1 | mandatory primary | `@ x` → Pattern(Primary) Error; embedded `13..15` | `mandatory_slot_recovery_keeps_accepted_syntax_and_one_record_per_slot` | RB-P |
| P2 | symbol name | `:` → SymbolName Missing Identifier | `commit_direct_primary` malformed-symbol branch | RB-P |
| P3 | alias binding | `A as` → AliasBinding Missing Identifier | mandatory-slot matrix | RB-P |
| P4 | alternation RHS | `A |` → AlternationRhs Missing Pattern | mandatory-slot matrix | RB-P |
| P5 | parenthesized element, separator, close | `(,a)`, `(a b)`, `(a` | mandatory-slot matrix and delimited driver | RB-P |
| P6 | list item, spread RHS, separator, close | `[,a]`, `[..]`, `[a b]`, `[a` | `list_pattern_recovery_preserves_item_and_separator_boundaries` | RB-P |
| P7 | record Pattern cells P7a–P7g below | exact finite register below | `record_patterns_keep_field_forms_spreads_layout_and_recovery_local` | RB-P, RB-E |
| P8 | pattern type annotation delegation | `x: @` → nested Type(Primary) Error | `annotation_malformed_recovery_uses_the_nested_pattern_base` | RB-P, RB-T |

## 4. TypeExpression and polymorphic-variant owners

Type rows use `R({type T = <type>})`; standalone ranges shift by `+15`.

| ID | finite variants | witness / required primary fact | existing owner contract | rollback |
| --- | --- | --- | --- | --- |
| T1 | required primary | `@A` → Type(Primary) Error TypeExpression | `mandatory_type_entry_recovers_a_nonempty_primary_prefix_before_retrying` | RB-T |
| T2 | path segment and arrow RHS | `A::@`, `A ->@ B` | path malformed matrix; `ast_type_item_recovery_scans_past_same_line_trivia` | RB-T |
| T3 | type-call item, separator, close | `T(,)`, `G T(F A)`, unclosed call | `type_call_missing_item_and_close_keep_distinct_typed_slots`; `call_and_group_retry_a_same_line_item_after_a_nested_ml_argument_stops` | RB-T |
| T4 | type-delimited cells T4a–T4h below | exact finite register below | `TypeDelimitedSpec`; `named_record_comma_policy_and_close_recovery_are_typed`; BracketRow test block | RB-T |
| T5 | named-record cells T5a–T5g below | exact finite register below | `named_record_field_colon_uses_one_chain_gap_policy_on_both_paths`; `named_record_comma_policy_and_close_recovery_are_typed`; `named_record_sequence_classifies_recovery_gaps_before_consuming_them` | RB-T |
| T6 | forall binder, binder boundary, colon, body | `for @`, `for 'a'b: T`, `for 'a`, `for 'a:` | `forall_recovery_keeps_its_phase_slots_non_cascading`; `forall_is_nud_only_apostrophe_only_and_terminal` | RB-T |
| T7 | leading-effect head cells T7a–T7c below | exact finite register below | `commit_direct_leading_effect_type` test block | RB-T |
| PV1 | polymorphic tag, separator, tag name, payload boundary/type, close | `:{,,A}`, `:{;A}`, `:{123 Int}`, `:{A @Int}`, `:{A` | `polymorphic_variant_type_uses_phase_specific_recovery_roles`; `VariantContext::begin_payload` | RB-PV, RB-T |

## 5. Canonical statement, declaration, and shared variant owners

All following literal witnesses run under `R({ ... })`, so canonical Statement
remains the direct owner. Nested Pattern/Type/Expression attempts additionally
obey their own rollback layer.

| ID | finite family | witness / required primary fact | existing owner contract | rollback |
| --- | --- | --- | --- | --- |
| S1 | canonical Statement malformed retry | `R({@ value})` → BracedStatementBlock(Statement) Error Statement | existing Gate 3 row | RB-S |
| D1 | Binding target/body/indented body | `R({my})`, `R({my value =})` | `direct_binding_missing_target_uses_the_binding_owner_role`; binding-body tests; `binding_style_body.rs` | RB-D, RB-P, RB-E |
| D2 | Use path/group/operator close/alias | `R({use})`, shells `use {value`, `use (+`, `use std as` | `direct_use_missing_target_closes_the_declaration_and_emits_one_missing_node`; recursive UseTree tests | RB-D |
| D3 | Mod cells D3a–D3d below | exact finite register below | `direct_mod_missing_identity_does_not_cascade_a_body_introducer`; `direct_mod_missing_colon_retries_a_canonical_statement`; `direct_mod_indented_body_keeps_its_statement_recovery_under_mod_owner` | RB-D |
| D4 | Struct cells D4a–D4g below | exact finite register below | `struct_header_slots_and_bodyless_form_are_typed_on_both_paths`; named/tuple field recovery blocks | RB-D, RB-T |
| D5 | Enum/Error header cells D5a–D5c plus V1–V4 recovery cross product and NV1 exclusion below | exact finite register below | `isolated_enum_declaration_recovery_contract_is_typed_and_non_cascading`; `error_gate_7_recovery_matrix_uses_error_outer_roles` | RB-D |
| D6 | Type cells D6a–D6d below | exact finite register below | Type declaration recovery cases; attached-Impl recovery cases | RB-D, RB-T |
| D7 | Role/Impl cells D7a–D7f below | exact finite register below | `isolated_role_declaration_recovery_contract_is_typed_and_non_cascading`; `isolated_impl_body_recovery_retries_one_malformed_run_without_cascade` | RB-D, RB-T |
| D8 | Cast cells D8a–D8f below | exact finite register below | `isolated_cast_declaration_recovery_rows_are_typed_non_cascading_and_lossless` | RB-D, RB-P, RB-T, RB-E |
| D9 | Act cells D9a–D9e below | exact finite register below | `isolated_act_declaration_recovery_contract_is_typed_and_non_cascading` | RB-D, RB-T |
| D10 | For cells D10a–D10f below | exact finite register below | `for_gate_7_recovery_matrix_fixtures_the_full_for_r_table` | RB-D, RB-P, RB-E |
| D11 | Derives cells D11a–D11b below | exact finite register below | `isolated_derives_direct_cst_adapter_is_byte_exact_lossless_and_ast_parity_checked` | RB-DRV, RB-T |
| D12 | declaration-companion cells D12a–D12f below | exact finite register below | `gate3_isolated_companion_form_recovery_and_state_table` | RB-CMP, RB-S |

The shared Enum/Error variant driver has a finite two-owner recovery cross
product. Every V1–V4 row executes once under `EnumDeclarationRole::Variant`
and once under `ErrorDeclarationRole::Variant`. NV1 is a normative
non-recovery exclusion under both owners:

| ID | finite variant slot | witness | primary expectation |
| --- | --- | --- |
| V1 | item and name | `,A}`, `@ A, B}` | Identifier |
| V2 | `from` type and positional field type | `From from, Next}`, `Rect @, Next}` | TypeExpression |
| V3 | named field name, colon, type, separator | `Named { : Int }, Next}`, `Named { field Int }, Next}`, `Named { field: }, Next}`, `Named { a: A b: B }, Next}` | Identifier, colon, TypeExpression, DelimitedSequenceSeparator |
| V4 | tuple field type and payload closes | `Tuple (, Int)}`, `Named { field: Int`, `Tuple (Int` | TypeExpression or exact close punctuation |
| NV1 | same-line raw positional payload exclusion | `A B}` | recovery stream `[]`; one complete variant with positional payload `B`; no `VariantDeclarationRole::Separator` fact or recovery node |

These use `enum_variant_payload_recovery_stays_in_its_own_slots`, the
Enum/Error recovery matrices, and the `variant_core` field/sequence drivers.

**Corrected 2026-09-02.** The former V5 recovery witness contradicted
governing `ENUM-R`: a same-line raw word after a complete variant name is
positional-payload evidence, not a missing variant separator. This correction
changes no syntax or recovery semantics. `VariantDeclarationRole::Separator`
remains vocabulary only; this matrix does not assign it a producer.

## 5a. Superseded editorial staging register (non-normative)

This section was an editorial attempt to expand the aggregate cells before
the ordinary controls had exposed every primary expectation.  It is retained
only to show the investigated shape and has no normative force.  Section 5b
supersedes it in full; no implementation or test may derive an expected value
from this staging material.

### Historical staging text

This historical register records the early expansion attempt.  Its values may
be stale and do not supplement §5b.  A cell's named ordinary test was used as
the fixture identity; Gate 3b would embed the exact same source after the
stated `R` or `A` shell.  `before`/`span` use §1's exact locators.  When a
literal ends at `eof`, the enclosing `R` closing delimiter is intentionally
omitted: the listed inner-close fact precedes the distinct Yumark wrapper-close
result.

### Expression aggregate cells

| subrow | ordinary fixture identity and embedded literal | exact embedded primary fact |
| --- | --- | --- |
| E7a | `projection_tail_recovery_keeps_typed_slots_local`: `R(a.(,x))` | `Expression(ProjectionTupleItem)`, `before(",")`, Missing, Expression |
| E7b | same: `R(a.(x,,y))` | `Expression(ProjectionTupleItem)`, `before(second ",")`, Missing, Expression |
| E7c | same: `R(a.(@x))` | `Expression(ProjectionTupleItem)`, `span("@")`, Error, Expression |
| E7d | same: `R(a.{,x})` | `Expression(ProjectionRecordItem)`, `before(",")`, Missing, Expression |
| E7e | same: `R(a.{..})` | `Expression(ProjectionRecordSpreadRhs)`, `before("}")`, Missing, Expression |
| E7f | same: `R(a.{..@rest})` | `Expression(ProjectionRecordSpreadRhs)`, `span("@")`, Error, Expression |
| E7g | `projection_tail_close_recovery_is_owner_safe_on_both_paths`: `R(a.(x` | `close(ProjectionTupleTail, Parenthesis)`, `eof`, Missing, punctuation `)` |
| E7h | same: `R(a.{x` | `close(ProjectionRecordTail, Brace)`, `eof`, Missing, punctuation `}` |
| E12a | `case_like_recovery_marks_missing_mandatory_slots_once`: `R(case : 1 -> a)` | `CaseLike(Scrutinee)`, `before(":")`, Missing, Expression |
| E12b | same: `R(case x)` | `CaseLike(Block)`, `before(")")`, Missing, punctuation `:` |
| E12c | same: `R(case x: -> a)` | `CaseLike(Pattern)`, `before("->")`, Missing, Pattern |
| E12d | same: `R(catch action: err, -> recover)` | `CaseLike(Handler)`, `before("->")`, Missing, Pattern |
| E12e | same: `R(case x: n if -> yes)` | `CaseLike(Guard)`, `before("->")`, Missing, Expression |
| E12f | `case_like_missing_arrow_retries_the_body_from_the_same_position`: `R(case x: n yes)` | `CaseLike(Arrow)`, `before("yes")`, Missing, Expression |
| E12g | `case_like_recovery_marks_missing_mandatory_slots_once`: `R(case x: n ->)` | `CaseLike(Body)`, `before(")")`, Missing, Expression |
| E12h | same: `R(catch action { err -> recover` | `CaseLike(Block)`, `eof`, Missing, punctuation `}` |
| E12i | `case_like_missing_arm_comma_retries_the_next_pattern`: `R(case x: 1 -> a 2 -> b)` | `CaseLike(Separator)`, `before(second arm "2")`, Missing, punctuation `,` |

### Pattern and type aggregate cells

| subrow | ordinary fixture identity and embedded literal | exact embedded primary fact |
| --- | --- | --- |
| P7a | `record_patterns_keep_field_forms_spreads_layout_and_recovery_local`: case pattern `{,a}` | `Pattern(RecordItem)`, `before(",")`, Missing, Identifier |
| P7b | same: `{a:}` | `Pattern(RecordNestedPattern)`, `before("}")`, Missing, Pattern |
| P7c | same: `{a =}` | `Pattern(RecordDefaultExpression)`, `before("}")`, Missing, Expression |
| P7d | same: `{..}` | `Pattern(RecordSpreadRhs)`, `before("}")`, Missing, Pattern |
| P7e | same: `{a b}` | `Pattern(RecordSeparator)`, `before("b")`, Missing, DelimitedSequenceSeparator |
| P7f | same: `{a` | `close(RecordPattern, Brace)`, `eof`, Missing, punctuation `}` |
| P7g | same: `{a: @}` | `Pattern(RecordNestedPattern)`, `span("@")`, Error, Pattern |
| T4a | TypeDelimitedSpec ordinary parenthesized row: `R({type T = (,)})` | `Type(ParenthesizedItem)`, `before(",")`, Missing, TypeExpression |
| T4b | TypeDelimitedSpec ordinary parenthesized row: `R({type T = (A B)})` | `Type(ParenthesizedSeparator)`, `before("B")`, Missing, DelimitedSequenceSeparator |
| T4c | TypeDelimitedSpec ordinary parenthesized close row: `R({type T = (A})` | `close(ParenthesizedTypeGroup, Parenthesis)`, `before("}")`, Missing, punctuation `)` |
| T4d | effect-row ordinary row: `R({type T = '[,]})` | `Type(EffectRowItem)`, `before(",")`, Missing, TypeExpression |
| T4e | effect-row ordinary row: `R({type T = '[A B]})` | `Type(EffectRowSeparator)`, `before("B")`, Missing, DelimitedSequenceSeparator |
| T4f | bracket-row ordinary row: `R({type T = '[,]})` in bracket-row context | `Type(BracketRowItem)`, `before(",")`, Missing, TypeExpression |
| T4g | BracketRow test block: `R({type T = '[A B]})` in bracket-row context | `Type(BracketRowSeparator)`, `before("B")`, Missing, DelimitedSequenceSeparator |
| T4h | `commit_direct_leading_effect_type_head` test block: malformed arrow after bracket row | `Type(BracketRowArrow)`, `before(offending arrow tail)`, Error, TypeExpression |
| T5a | `named_record_sequence_classifies_recovery_gaps_before_consuming_them`: `R({type T = {,a}})` | `Type(RecordField)`, `before(",")`, Missing, Identifier |
| T5b | `named_record_field_colon_uses_one_chain_gap_policy_on_both_paths`: `R({type T = {: A}})` | `Type(RecordFieldName)`, `before(":")`, Missing, Identifier |
| T5c | same: `R({type T = {name A}})` | `Type(RecordFieldColon)`, `before("A")`, Missing, punctuation `:` |
| T5d | `named_record_sequence_classifies_recovery_gaps_before_consuming_them`: `R({type T = {name: @ A}})` | `Type(RecordFieldType)`, `span("@")`, Error, TypeExpression |
| T5e | `named_record_comma_policy_and_close_recovery_are_typed`: `R({type T = {a: A; b: B}})` | `Type(RecordFieldSeparator)`, `span(";")`, Error, DelimitedSequenceSeparator |
| T5f | same: `R({type T = {a: A,})` | `Type(RecordField)`, `eof`, Missing, Identifier |
| T5g | same: `R({type T = {a: A])` | `close(NamedRecordType, Brace)`, `span("]")` then `before(")")`, Error then Missing, punctuation `}` |
| T7a | `commit_direct_leading_effect_type_head` test block: leading row `R({type T = '[@]})` | `Type(LeadingEffectTypeHead)`, `span("@")`, Error, TypeExpression |
| T7b | same: missing head `R({type T = '[]})` | `Type(LeadingEffectTypeHead)`, `before("]")`, Missing, TypeExpression |
| T7c | same: malformed arrow `R({type T = '[A] @})` | `Type(BracketRowArrow)`, `span("@")`, Error, TypeExpression |

### Declaration and statement aggregate cells

`D(X)` below abbreviates `GrammarRole::Declaration(DeclarationRole::X)`;
each role spelling remains the closed `session.rs` enum path.  Body-introducer
rows use their named ordinary test's **first** expectation as the primary fact;
the test continues to pin any auxiliary union expectations directly.

| subrow | ordinary fixture identity and embedded literal | exact embedded primary fact |
| --- | --- | --- |
| D3a | `direct_mod_missing_identity_does_not_cascade_a_body_introducer`: `R({mod})` | `D(Mod(Name))`, `before("}")`, Missing, Identifier |
| D3b | `direct_mod_complete_identity_requires_one_union_body_introducer_slot`: `R({mod outer})` | `D(Mod(BodyIntroducer))`, `before("}")`, Missing, punctuation `;` |
| D3c | `mod_colon_body_missing_keeps_outer_comma_and_close_available`: `R({mod outer:})` | `D(Mod(Body))`, `before("}")`, Missing, Statement |
| D3d | `direct_mod_indented_body_keeps_its_statement_recovery_under_mod_owner`: embedded indented `mod outer:\n  ` | `D(Mod(IndentedStatement))`, `eof`, Missing, Statement |
| D4a | `struct_header_slots_and_bodyless_form_are_typed_on_both_paths`: `R({struct})` | `D(Struct(Name))`, `before("}")`, Missing, Identifier |
| D4b | same: `R({struct S})` | `D(Struct(BodyIntroducer))`, `before("}")`, Missing, punctuation `;` |
| D4c | `struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary`: `R({struct S { : A }})` | `D(Struct(FieldName))`, `before(":")`, Missing, Identifier |
| D4d | same: `R({struct S { f A }})` | `D(Struct(FieldColon))`, `before("A")`, Missing, punctuation `:` |
| D4e | same: `R({struct S { f: @ }})` | `D(Struct(FieldType))`, `span("@")`, Error, TypeExpression |
| D4f | `struct_named_brace_semicolon_is_an_error_separator_and_retries_the_next_field`: `R({struct S { f: A; g: B }})` | `D(Struct(FieldSeparator))`, `span(";")`, Error, DelimitedSequenceSeparator |
| D4g | `struct_tuple_fields_keep_type_apply_and_tuple_close_ownership_distinct`: `R({struct S(A})` | `close(StructTupleFields, Parenthesis)`, `before("}")`, Missing, punctuation `)` |
| D5a | `isolated_enum_declaration_recovery_contract_is_typed_and_non_cascading`: `R({enum})` | `D(Enum(Name))`, `before("}")`, Missing, Identifier |
| D5b | `error_gate_7_recovery_matrix_uses_error_outer_roles`: `R({error})` | `D(Error(Name))`, `before("}")`, Missing, Identifier |
| D5c | those same matrices: `R({enum E})` and `R({error E})` | `D(Enum(BodyIntroducer))` / `D(Error(BodyIntroducer))`, `before("}")`, Missing, punctuation `{` |
| D6a | Type declaration recovery cases: `R({type})` | `D(Type(Name))`, `before("}")`, Missing, Identifier |
| D6b | same: `R({type T})` | `D(Type(DefinitionIntroducer))`, `before("}")`, Missing, punctuation `=` |
| D6c | same: `R({type T =})` | `D(Type(Rhs))`, `before("}")`, Missing, TypeExpression |
| D6d | attached-Impl recovery cases: `R({type T = U impl})` | `D(Type(AttachedImpl(Head)))`, `before("}")`, Missing, TypeExpression |
| D7a | `isolated_role_declaration_recovery_contract_is_typed_and_non_cascading`: `R({role})` | `D(Role(Head))`, `before("}")`, Missing, TypeExpression |
| D7b | same: `R({role R})` | `D(Role(BodyIntroducer))`, `before("}")`, Missing, punctuation `:` |
| D7c | same: `R({role R:})` | `D(Role(Body))`, `before("}")`, Missing, Statement |
| D7d | same indented row: `role R:\n  ` | `D(Role(IndentedStatement))`, `eof`, Missing, Statement |
| D7e | `isolated_impl_body_recovery_retries_one_malformed_run_without_cascade`: `R({impl})` | `D(Impl(Head))`, `before("}")`, Missing, TypeExpression |
| D7f | same: `R({impl T:})` | `D(Impl(Body))`, `before("}")`, Missing, Statement |
| D8a | `isolated_cast_declaration_recovery_rows_are_typed_non_cascading_and_lossless`: `R({cast})` | `D(Cast(PatternIntroducer))`, `before("}")`, Missing, punctuation `(` |
| D8b | same: `R({cast(@): A = body})` | `D(Cast(Pattern))`, `span("@")`, Error, Pattern |
| D8c | same: `R({cast(x) @ A = body})` | `D(Cast(TargetIntroducer))`, `span("@")`, Error, punctuation `:` |
| D8d | same: `R({cast(x): @ = body})` | `D(Cast(TargetType))`, `span("@")`, Error, TypeExpression |
| D8e | same: `R({cast(x): A})` | `D(Cast(BodyIntroducer))`, `before("}")`, Missing, punctuation `;` |
| D8f | same indented row: `cast(x): A =\n  ` | `D(Cast(IndentedStatement))`, `eof`, Missing, Statement |
| D9a | `isolated_act_declaration_recovery_contract_is_typed_and_non_cascading`: `R({act})` | `D(Act(Head))`, `before("}")`, Missing, TypeExpression |
| D9b | same: `R({act A =})` | `D(Act(Source))`, `before("}")`, Missing, TypeExpression |
| D9c | same: `R({act A})` | `D(Act(BodyIntroducer))`, `before("}")`, Missing, punctuation `=` |
| D9d | same: `R({act A = B:})` | `D(Act(Body))`, `before("}")`, Missing, Statement |
| D9e | same indented row: `act A = B:\n  ` | `D(Act(IndentedStatement))`, `eof`, Missing, Statement |
| D10a | `for_gate_7_recovery_matrix_fixtures_the_full_for_r_table`: `R({for @ x in xs: body})` | `Pattern(Primary)`, `span("@")`, Error, Pattern |
| D10b | same: `R({for x xs: body})` | `ForStatement(InKeyword)`, `before("xs")`, Missing, keyword `in` |
| D10c | same: `R({for x in @ xs: body})` | `Expression(Nud)`, `span("@")`, Error, Expression |
| D10d | same: `R({for x in xs @: body})` | `ForStatement(BodyIntroducer)`, `span("@")`, Error, punctuation `:` |
| D10e | same: `R({for x in xs:})` | `ForStatement(Body)`, `before("}")`, Missing, Expression |
| D10f | same indented row: `for x in xs:\n  ` | `ForStatement(IndentedStatement)`, `eof`, Missing, Statement |
| D11a | `isolated_derives_direct_cst_adapter_is_byte_exact_lossless_and_ast_parity_checked`: `R({type T = Int derives})` | `D(Derives(RoleReference))`, `before("}")`, Missing, TypeExpression |
| D11b | same: `R({type T = Int derives Eq via})` | `D(Derives(ViaTarget))`, `before("}")`, Missing, Identifier |
| D12a | `gate3_isolated_companion_form_recovery_and_state_table`: `with` form without `:` | `D(Companion(Introducer))`, `eof`, Missing, punctuation `{` (with `:` retained as a direct auxiliary expectation) |
| D12b | same inline form: `with:` | `D(Companion(Body))`, `eof`, Missing, Statement |
| D12c | same inline sequence: `with: @` | `D(Companion(Body))`, `span("@")`, Error, Statement |
| D12d | same colon form with no entered indented sequence: `with:\n  ` | `D(Companion(Body))`, `before("\\n")`, Missing, Statement |
| D12e | same braced form: `with { enum E {} type T = Int }` | `D(Companion(Separator))`, `before("type")`, Missing, StatementSeparator |
| D12f | same braced close form: `with { a` | `close(DeclarationCompanion, Brace)`, `eof`, Missing, punctuation `}` |

## 5b. Normative adoption-control completion

Gate 3b implementation does not begin for an aggregate family until its
ordinary direct control has a primary-expectation assertion.  This is not a
new recovery contract: it turns the existing producer-selected primary
expectation into an ordinary regression assertion before the same fact is
transported through Yumark.

Every completed subrow has exactly these fields:

```text
ID(.order)
embedded literal
exact locator
(GrammarRole, RecoveryKind, primary ExpectedSyntax)
ordinary control: module::test_name["exact ordinary literal"]
rollback layer
```

`primary` always means `record.expectations[record.primary_expectation]`;
it is never assumed to be the first expectation.  A fixture with two records
uses `.1`, `.2`, and so on in source order.  `first`, `last`, and `nth` range
locators are permitted only when their ordinal is written explicitly.  A test
which currently proves only kind/role/range is an
**ordinary-primary-control gap**: the only permitted preparatory change is an
assertion of that existing record field in that ordinary test.  It may not
change a literal, expected output, recovery count, or parser behavior.

The finite preparation inventory is below.  Each entry is one or more named
test-table cases, not an open-ended family.

| cells to complete | exact ordinary control identities |
| --- | --- |
| E2 fixed field/path tails | `expression::tests::fixed_tail_recovery_keeps_missing_and_invalid_rhs_local["x.", "x.@", "x::", "x::123"]`; each listed direct record asserts its selected primary expectation is `ExpectedSyntax::Identifier` |
| E7a–E7h | `expression::tests::projection_tail_recovery_keeps_typed_slots_local["a.(,x)", "a.(@x)", "a.{,x}", "a.{..}"]`; `expression::tests::projection_tail_close_recovery_is_owner_safe_on_both_paths["a.(x]", "a.{x)"]`; add separate separator controls only if their direct owner emits a committed record |
| E12a–E12k | `expression::tests::case_like_recovery_marks_missing_mandatory_slots_once["case : 1 -> a", "case x", "case x: -> a", "catch action: err, -> recover", "case x: n if -> yes", "case x: n", "case x: n ->", "catch action { err -> recover"]`; `case_like_invalid_arrow_run_recovers_to_the_next_comma_arm["case x: n @, _ -> b"]`; `case_like_missing_arm_comma_retries_the_next_pattern["case x: 1 -> a 2 -> b"]`; one existing same-indent Arm boundary control |
| P7a–P7g | `pattern::tests::record_patterns_keep_field_forms_spreads_layout_and_recovery_local["{,a}", "{a:}", "{a =}", "{..}", "{a b}", "{a; b}"]`; `pattern::tests::gate3b_ordinary_primary_control_record_pattern["{a: @}"]`; add the existing record-close literal as a separately named ordinary control |
| T4 parenthesized/effect/bracket cells | `type_expr::tests::{shared_type_delimited_driver_covers_malformed_gaps_and_close_retry, effect_row_reuses_type_call_delimited_recovery_slots, bracket_row_rp1_classifies_every_malformed_item_retry, bracket_row_rp2_rp3_rp4_converge_item_and_close_slots, bracket_row_sequence_matrix_keeps_shared_normal_behavior}`; one row per owner × Item/Separator/Close, and `BracketRowArrow` separately |
| T5a–T5h | `type_expr::tests::{named_record_malformed_item_stays_at_sequence_scope, named_record_missing_name_commits_the_field_owner, named_record_field_colon_uses_one_chain_gap_policy_on_both_paths, named_record_recovers_malformed_colon_and_type_slots, named_record_comma_policy_and_close_recovery_are_typed, named_record_sequence_classifies_recovery_gaps_before_consuming_them}`; every listed case literal receives a primary assertion |
| T7a–T7c | `type_expr::tests::leading_bracket_row_mandatory_head_recovery_is_typed_and_non_cascading["[e]", "[e][f]T", "[e]@"]` |
| D3 Mod | `declaration::tests::{direct_mod_missing_identity_does_not_cascade_a_body_introducer["mod", "mod test"], direct_mod_complete_identity_requires_one_union_body_introducer_slot["mod outer"], mod_colon_body_missing_keeps_outer_comma_and_close_available["mod outer:"], direct_mod_indented_body_keeps_its_statement_recovery_under_mod_owner["mod outer:\\n  "]}`.  Keep `Name` and `TestName` distinct. |
| D4 Struct | `declaration::tests::{struct_header_slots_and_bodyless_form_are_typed_on_both_paths["struct", "struct S"], struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary, struct_named_brace_semicolon_is_an_error_separator_and_retries_the_next_field, struct_tuple_fields_keep_type_apply_and_tuple_close_ownership_distinct}`; one explicit control each for Name, BodyIntroducer, Field, FieldName, FieldColon, FieldType, FieldSeparator, and both field-construct closes |
| D5 Enum/Error plus V1–V4 and NV1 | `declaration::tests::{isolated_enum_declaration_recovery_contract_is_typed_and_non_cascading, error_gate_7_recovery_matrix_uses_error_outer_roles, enum_variant_payload_recovery_stays_in_its_own_slots}`. Expand each V1–V4 slot once under `Enum(Variant(slot))` and once under `Error(Variant(slot))`; V3's four slots and V4's two close owners are separate cells. NV1 is a zero-recovery positional-payload exclusion under both owners. |
| D6 Type | `declaration::tests::{type_declaration_header_slots_follow_td_r_name_and_equals_recovery, type_declaration_form_aware_tnd_r_recovery_matrix_is_complete_and_non_cascading, type_attached_impl_tail_owner_selects_type_recovery_without_forking_episode_rules}`; separate Name, DefinitionIntroducer, Rhs, and every reachable `AttachedImpl(ImplRole)` slot |
| D7 Role/Impl | `declaration::tests::{isolated_role_declaration_recovery_contract_is_typed_and_non_cascading, isolated_impl_body_recovery_retries_one_malformed_run_without_cascade}`; Role Head/BodyIntroducer/Body/IndentedStatement and Impl Head/Description/BodyIntroducer/Body/IndentedStatement are separate cells |
| D8 Cast | `declaration::tests::isolated_cast_declaration_recovery_rows_are_typed_non_cascading_and_lossless`; PatternIntroducer, Pattern, TargetIntroducer, TargetType, BodyIntroducer, Body, and IndentedStatement are separate cells |
| D9 Act | `declaration::tests::isolated_act_declaration_recovery_contract_is_typed_and_non_cascading`; Head, Source, BodyIntroducer, Body, and IndentedStatement are separate cells |
| D10 For | `declaration::tests::for_gate_7_recovery_matrix_fixtures_the_full_for_r_table`; Pattern, InKeyword, Iterable, BodyIntroducer, Body, and IndentedStatement are separate cells.  `InKeyword`'s existing producer primary is `ExpectedSyntax::Expression` (`commit_for_in_and_iterable_isolated`), not a nonexistent `KeywordEvidence::In`. |
| D11 Derives | `declaration::tests::isolated_derives_direct_cst_adapter_is_byte_exact_lossless_and_ast_parity_checked`; RoleReference and ViaTarget are separate cells |
| D12 companion | `declaration::companion::tests::gate3_isolated_companion_form_recovery_and_state_table`; Introducer, Body, Item, IndentedItem, Separator, and `close(DeclarationCompanion, Brace)` are separate cells |

For every row in that inventory, the preparatory ordinary-control assertion and
the derived exact embedded tuple are added together in one focused Gate 3b
test-table change.  The implementation may then cite the completed subrow by
its stable cell ID.  An uncompleted gap is evidence that the corresponding
owner episode is not ready to adopt; it is not permission to omit the owner or
to infer the fact from an AST/CST walk.

## 6. Rejected transaction layers

| layer | owner probes that must restore before another owner commits | mandatory proof |
| --- | --- | --- |
| RB-E | OperatorChain, direct NUD, all expression item/slot probes | input, local, sink, and no published fact |
| RB-P | Pattern primary/item/separator/close probes | same, including outer-role preservation |
| RB-T | required TypeExpression, delimited, forall, record probes | same |
| RB-PV | polymorphic tag/payload candidate | same plus persistent recovery head |
| RB-S | canonical Statement candidate/sequence | same before Statement recovery |
| RB-D | declaration intro and mandatory slots | same before declaration recovery |
| RB-DRV | derives role/via candidate | same before Derives recovery |
| RB-CMP | companion introducer/form/item probe | same before companion recovery |

Every rollback row asserts exact input/remainder, `ParseLocal::value_snapshot`,
preseeded `LatestSink`, output checkpoint/node count, cut, and persistent
embedded recovery-log generation/head.

## 7. Committed fact cannot leak across an embedded-frame pop

The required AST/direct literal is:

```text
\ref(x[,a]) \ref(1) [d]:f(2)
```

It has exactly one recovery:

```text
order 0: Expression(IndexItem), 7..7, Missing, Expression
```

The first reference drains that fact before consuming its borrowed `)` at
`10..11`, tears down canonical layout/expression-owner/stop state, and pops
its exact delimiter floor and embedded frame. At byte 12 the recovery log is
empty. The second reference and the following apply publish no fact. At EOF the
Yumark frame depth is zero; canonical delimiter/stop/expression-owner/layout
depths equal entry; AST has one fact and direct one record; AST diagnostic id
is unchanged and direct id advances once; the direct prefix is lossless and
both remainders are empty.
