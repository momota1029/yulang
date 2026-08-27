# Colon application

## 1. 状態・正本・最終確認

Authoritative な generic colon-application / indented-block-boundary 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 5014–5467 行にある。original comma-only inline loop は 9314–9693 行の layout-aware separator revision で supersede され、tail、inline-versus-indented branch、CST、AST の決定は維持される。

design / implementation commit は `01348df9`、`14eb4900`、`81ef211d`。`14eb4900` が terminal colon tail、`81ef211d` が current comma-or-qualifying-newline inline boundary rule を導入した。

## 2. 対象範囲と非対象

generic colon application は completed `OperatorChain` 後の terminal continuation である。`f: x`、`f: x, y`、`f:\n  x\n  y` を扱う。outer sequence owner がない場合は non-empty inline argument sequence、strictly deeper newline 後は indented canonical statement block を所有する。

`if`/`elsif`/`else` arm colon、declaration/pattern/type colon、`with:`、semantic call sugar、target association、HIR/lowering、type inference、record-field semantics、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
ColonApplicationTail :=
    Colon G0 InlineColonArguments
  | Colon IndentedStatementBlock

InlineColonArguments(no_outer_sequence_owner) :=
    OperatorChain
    { InlineColonArgumentSeparator OperatorChain }
    [ ImplicitNewlineBoundary(colon_inline_base) ]

InlineColonArgumentSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(colon_inline_base)

InlineColonArguments(outer_sequence_owner) := OperatorChain
```

indented block は post-colon trivia に physical newline があり、`block_indent > base_indent` のときだけ選ぶ。colon-owned inline sequence では literal trailing comma を valid としない。

## 4. Judge・priority・owner boundary

operand-complete chain judge は active `StopKind::Colon`、`ml_arg`、caller boundary、longest punctuation（`::` を `:` より先）を尊重する。reserve されていない lone colon だけが `ColonApplicationTail` へ cut し、accept 後の colon parse は total で current chain を終える。

layout probe は physical post-colon newline がなければ inline を選ぶ。newline は strictly deeper indent のときだけ indented branch を開始し、wrong-indent newline は outer owner へ残す。outer sequence ownership が優先される。`(f: x, y)` では colon は RHS 一つだけを parse して comma を parenthesized owner に残し、root `f: x, y` は二argument を所有する。

## 5. Byte-exact CST の worked examples

追補は source-order CST tree を持つが byte-range 付き tree はない。ここでは range を作らない。

```text
a + b: x
```

設計文書 5213–5226 行は outer `OperatorChain` の `a`、infix `+`、`b` の後に、`:`, whitespace, RHS `x` だけを所有する target-free `ColonApplicationTail` を置く。

```text
f: x, y + z
```

設計文書 5041–5045 行と 5411–5413 行は two-inline-argument form を記録する。comma と argument chain は tail child であり source-absent list wrapper ではない。

```text
f:
  x
  y
```

設計文書 5041–5045 行と 5415–5417 行は opening trivia と statement sequence を持つ一つの `IndentedStatementBlock` を要求する。

```text
{x: 1}
```

設計文書 5323–5336 行と 5418–5419 行は dedicated record CST node ではなく、ordinary colon tail を含む `BracedStatementBlockExpression` として固定する。

## 6. Parser 側 AST shape

`TerminalOuterTail::ColonApplication` は `ColonApplicationTail` を持つ。この struct は正確に `colon`、recovered `rhs`、`range` を持ち、target field はない。

`ColonApplicationRhs` は正確に `Inline { arguments: Vec<Recovered<OperatorChain<'source>>> }` と `Indented { block: IndentedStatementBlock<'source> }` を持つ。`IndentedStatementBlock` は正確に `base_indent`、`block_indent`、recovered ordered `statements`、`range` を持つ。inline comma token と whitespace は AST field ではなく CST が所有する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `f:` または horizontal trivia 後の EOF | colon を保持し zero-width RHS Missing 一件 |
| equal-or-shallower indent の post-colon newline | newline/next statement を consume せず colon boundary に RHS Missing 一件 |
| strictly deeper newline 後の EOF | block/opening trivia を保持し block 内に statement Missing 一件 |
| colon-owned leading comma | first-argument Missing 一件。comma を保持して next argument を retry |
| colon-owned comma 後の EOF | next-argument Missing 一件。valid trailing-comma marker なし |
| outer sequence owner の comma | comma を owner へ残し、colon は RHS 一つまで parse |
| valid value 前の malformed inline run | non-empty Error 一件後 same-argument-slot retry |
| malformed block statement | shared statement recovery が sibling indent/dedent へ synchronize |

Missing は zero-width、Error は non-empty であり、accepted tail/chain は duplicate diagnostic なしに必ず finish する。

## 8. Boundary と state-restoration contract

introducer は post-colon trivia 前に active base indentation を snapshot する。inline/list stop、indentation baseline、`inline`、`ml_arg`、stop-set change は normal/recovery/rollback の全 exit で restore する。dedent、outer comma、matching close、wrong-indent newline、statement/root boundary は caller safe point で non-consuming である。

## 9. Yulang2 divergences

Yulang3 は lone-colon outer-tail ownership、inline argument、strict indented-block trigger を保つが、Pratt tree ではなく flat `OperatorChain` RHS を保存する。synthetic separator output を raw trivia へ置換し、brace-record-looking form を ordinary statement-block + colon syntax とし、RHS/inline/block slot へ typed recovery role を与える。

## 10. Known residual / deferred surface

shared `ASOB-G` hidden caller-boundary residual は characterization のままである。colon target association、call/block/record semantic interpretation、HIR/lowering、type inference、`with:`、other control/declaration/pattern/type colon family、diagnostics text、formatting はこの grammar page の外に残る。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_colon_application_tail`、`parse_inline_colon_arguments`、`outer_owns_inline_argument_sequence`、`commit_colon_application_tail`、`commit_colon_inline_argument`、`colon_inline_argument_error_retry`、`emit_colon_application_missing`、`emit_colon_application_error` を参照する。

fixture は `colon_application_ast_and_cst_keep_inline_arguments_in_the_terminal_tail`、`colon_inline_returns_a_live_if_companion_gap_after_its_first_argument`、`colon_inline_newline_arguments_have_ast_direct_and_bp_parity`、`colon_application_recovery_keeps_commas_and_retries_valid_values`、`colon_application_parses_an_indented_statement_block`。
