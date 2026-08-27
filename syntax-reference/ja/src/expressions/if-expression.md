# `if` / `elsif` / `else` expression

## 1. 状態・正本・最終確認

Authoritative な NUD-primary `if` / `elsif` / `else` 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 5469–6065 行にある。generic colon 追補の low-level layout/block machinery を reuse するが、arm structure と arm-colon recovery はこの追補自身が所有する。

design / implementation commit は `3aaf5d80`、`2b910d47`、`5cafd19a`、`876d11de`。後ろ二つは current nested/control context に必要な ambient / companion-frame authority を追加した。

## 2. 対象範囲と非対象

`if` は generic colon tail ではなく operand-starting `PrimaryExpression` である。一つの `IfExpression` は initial `IfArm` 一つ、sibling `Elsif` arm zero-or-more、optional `ElseArm` 一つを持つ。`if`/`elsif` body は arm-owned colon + exactly one inline OperatorChain または indented statement block、`else` はさらに bare OperatorChain 一つを許す。

brace arm body、`case`/`catch`、other colon-owner family、block 内 declaration coverage、conditional HIR lowering、branch typing/effect、operator association、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
IfExpression := IfArm { ArmContinuation ElsifArm } [ ArmContinuation ElseArm ]
IfArm := IfKw G* Condition Gcont ColonIntroducedArmBody
ElsifArm := ElsifKw G* Condition Gcont ColonIntroducedArmBody
Condition := OperatorChain under current-depth StopSet { Colon, LeftBrace, Elsif, Else }
ColonIntroducedArmBody := Colon G0 InlineArmExpression | Colon IndentedStatementBlock
InlineArmExpression := OperatorChain under IfContinuationStop
ElseArm := ElseKw Gcont ( ColonIntroducedArmBody | BareElseExpression )
BareElseExpression := OperatorChain under ordinary NUD-start layout and IfContinuationStop
ArmContinuation := HorizontalTrivia | NewlineTrivia where next_indent >= if_base_indent
IfContinuationStop := current outer StopSet plus Elsif plus Else
```

`elsif` は exact contextual word 一つである。`else if` は bare else body 内の nested `IfExpression` になる。

## 4. Judge・priority・owner boundary

operand-required NUD site では exact maximal word `if` だけを accept して cut する。`ifx` は ordinary identifier のままである。`elsif`/`else` は generic NUD word ではなく、active IfExpression companion frame だけが valid arm boundary で accept する。

condition parse は Colon/LeftBrace/Elsif/Else stop を加えるため、arm colon は `ColonApplicationTail` にならない。arm colon と single body は `IfArm`/`ElseArm` の direct child であり、inline arm body は generic colon inline-list loop を使わない。continuation は horizontal trivia または original if base 以上の newline だけを accept し、shallower/non-keyword continuation は outer owner へ残す。

## 5. Byte-exact CST の worked examples

追補は complete source-order CST shape を持つが byte-range 付き tree はない。ここでは range を作らない。

```text
if x: 1 else: 0
```

設計文書 6000 行は generic colon-tail node なしの `IfExpression` 一つ、`IfArm` 一つ、`ElseArm` 一つを固定する。

```text
if x: 1 elsif y: 2 elsif z: 3 else: 0
```

設計文書 6001 行は first arm、`ElsifKw` を持つ sibling `IfArm` 二つ、`ElseArm` 一つを固定する。

```text
if x:
  1
  2
else: 0
```

設計文書 6003–6004 行は Statement child 二つを持つ arm-owned `IndentedStatementBlock` を固定する。dedent `else` は同じ IfExpression へ戻る。

```text
else if ...
```

設計文書 5609–5611 行はこの spelling を `ElsifKw` sibling ではなく nested IfExpression を含む bare `ElseArm` body として固定する。

## 6. Parser 側 AST shape

`PrimaryExpression::If` は `IfExpression` を持つ。`IfExpression` は正確に ordered `arms`、optional `else_arm`、`base_indent`、`range` を持つ。

各 `IfArm` は正確に `keyword`、recovered `condition`、recovered `body`、`range` を持つ。`IfArmKeyword` は正確に `If` または `Elsif` である。`ElseArm` は正確に `keyword`、recovered `body`、`range` を持つ。`ElseArmBody` は正確に `Colon(ColonIntroducedArmBody)` または `Bare(Box<OperatorChain>)` である。

`ColonIntroducedArmBody` は正確に recovered `colon`、recovered `rhs`、`range` を持つ。`ArmBodyRhs` は正確に `Inline(Box<OperatorChain>)` または `Indented(IndentedStatementBlock)` である。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `if : 1` | colon 前に condition Missing 一件。colon/body は normal commit |
| EOF の `if` | condition Missing 一件。same EOF に colon/body Missing を cascade しない |
| EOF の `if x` | condition を保持し missing introducer/body を arm-body absence 一件へ aggregate |
| EOF の `if x:` | colon を保持し body Missing 一件 |
| wrong-indent post-colon newline | colon に body Missing。newline/following input は outer owner へ残す |
| value 前の malformed inline body | non-empty Error 一件後 same body-slot retry |
| body がない accepted `elsif`/`else` | keyword を保持し appropriate body Missing 一件。identifier へ rollback しない |
| duplicate later `else` | first ElseArm 後に finish し second keyword を outer recovery へ残す |

direct Missing/Error node は committed recovery record と one-to-one である。shared indented-block recovery は ColonApplication role ではなく If role を使う。

## 8. Boundary と state-restoration contract

IfExpression は `if_base_indent` を一度 capture し、全 `elsif` arm の間は companion frame 一つを維持する。own else body parse 前にその frame を pop し、AST/direct の normal/recovery/rollback exit は companion identity、stop、delimiter、indentation/layout state、ambient ownership を exact restore する。nested if frame は distinct identity を保つ。

## 9. Yulang2 divergences

Yulang3 は primary-expression placement、sibling `elsif` arm、optional else、colon/indent form、base-indent continuation rule を保つ。Pratt expression subtree ではなく flat OperatorChain を使い、synthetic wrapper なしの source-order direct CST と typed role-specific recovery を用いる。

## 10. Known residual / deferred surface

general `ASOB-G` caller-boundary residual は characterization のままである。brace arm body、case/catch reuse、block 内 declaration statement の拡張、conditional HIR lowering、branch/result type/effect semantics、association、diagnostics、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_if_nud`、`parse_if_expression`、`parse_if_arm`、`parse_else_arm`、`recognize_if_arm_continuation`、`recognize_arm_colon`、`commit_if_expression`、`commit_if_arm`、`commit_else_arm`、`commit_colon_introduced_if_body`、`emit_if_missing`、`if_body_error_retry` を参照する。

fixture は `if_expression_owns_arm_colons_without_colon_application_tails`、`if_expression_keeps_elsif_arms_as_siblings`、`if_expression_uses_one_companion_identity_across_every_elsif_arm`、`if_companion_frames_balance_across_ast_and_direct_recovery_exits`、`if_expression_is_binding_power_invariant`、`if_recovery_preserves_committed_keywords_and_body_retry`。
