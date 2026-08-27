# `forall` type

## 1. 状態・正本・最終確認

Authoritative な forall 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 13431–13980 行にある。current ambient-boundary behavior は 18358–19161 行の `ASOB-G`、malformed-newline behavior は 16557–17289 行の `TMN` と positional-fence authority に従う。

実装 commit は `b79df9d2`、`f7bacb34`、`57afb683`、`f8b95909`。このページは `063da888` を基準に確認した。

## 2. 対象範囲と非対象

forall は `for 'a 'b: T` を canonical type NUD position だけで contextual TypePrimary として追加する。ordered apostrophe-only binder、mandatory colon、full recursive body、bounded layout、phase-specific recovery を所有する。

statement `for`、LED/ML `for`、non-apostrophe binder、use-site wiring、type semantics、HIR/lowering、diagnostics text、formatting は対象外である。

## 3. BNF 相当の grammar

```text
ForallType := ForKw ForallTypeBinder { ForallTypeBinder } ForallColonTrivia Colon ForallBodyTrivia TypeExpression
ForallTypeBinder := ForallBinderBoundary ApostropheTypeBinderName
ForallBinderBoundary := NonEmptyTriviaWithoutPhysicalNewline | NonEmptyTriviaWithDeeperFollowingIndent(forall_base)
ApostropheTypeBinderName := Apostrophe UnicodeIdentifierBody
```

`forall_base` snapshot は accepted `for` の直後に取る。binder boundary は non-empty、colon/body gap は empty を許す。equal-or-shallower newline は forall-owned trivia にならない。

## 4. Judge・priority・owner boundary

canonical NUD position では exact maximal `for` が identifier より先に forall を accept/cut する。`forx`、`forall`、`for_` は identifier のまま。TypeApply LED position の exact `for` は forall を再scanせず ordinary identifier seed になる。

phase は FirstBinder、BinderOrColon、Body の三つ。binder 前は apostrophe binder または literal colon だけが progress を作る。binder 後は apostrophe が次 binder、non-binder primary が missing-colon body retry になる。raw forall は terminal で、body が path/call/apply/arrow を所有する。grouping だけが outer tail を後置できる。

## 5. Byte-exact CST の worked examples

追補には complete CST tree があるが byte-range 付き tree はない。ここでは range を作らない。

```text
for 'a: A -> A
```

設計文書 13641–13662 行は、`ForKw`、一つの `ForallTypeBinder`、colon-side trivia、body 内の arrow を持つ nested TypeExpression を `ForallType` が所有することを示す。

```text
for
  'a
  'b:
    Pair('a, 'b)
```

設計文書 13664–13697 行は各 binder が leading newline/indentation boundary を own し、deeper colon-to-body trivia は `ForallType` に属することを示す。

```text
(for 'a: 'a)::Result
```

設計文書 13897–13902 行は forall 後の `TypePathTail` には grouping が必要であることを示す。

## 6. Parser 側 AST shape

`TypePrimary::Forall(ForallType)` は `keyword`、ordered recovered `binders`、recovered `colon`、recovered boxed `body`、`range` を持つ。`ForallTypeBinder` は recovered leading `boundary`、apostrophe name、range を持つ。

delimiter close/ separator slot はない。missing whole binder は incomplete list item、missing boundary は complete binder の一部になる。これは CST ownership と recovery cardinality に対応する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| EOF/boundary の `for` | `TypeRole::ForallBinder` Missing 一件。colon/body cascade なし |
| adjacent binder | `TypeRole::ForallBinderBoundary` Missing 一件後 same-position binder retry |
| malformed first binder | ForallBinder Error 一件。binder または colon skeleton へ retry |
| accepted binder 後の EOF/boundary | `TypeRole::ForallColon` Missing 一件。body cascade なし |
| accepted binder 後の non-binder | missing ForallColon 一件後 full body same-position retry |
| binder/colon/body 前の malformed continuation | earliest retry target で選ぶ exclusive Binder/Colon Error 一件 |
| accepted colon 後の missing/malformed body | `TypeRole::ForallBody` Missing/Error 一件。boundary は owner のまま |

comma/semicolon は binder separator ではない。scan は active stop、close、caller boundary、qualifying newline、retry candidate の前で止まり、cause 一つにつき committed record 一つを作る。

## 8. Boundary と state-restoration contract

forall は delimiter/layout frame を push しない。bounded trivia probe と body call は既存 stop、delimiter、type-ML、owner、episode、positional-fence state と compose し、normal/recovery/rollback exit ごとに復元する。AST/direct は recognition、phase、cut、safe-point predicate を共有する。

## 9. Yulang2 divergences

Yulang2 parser code は contextual NUD `for`、binder repetition、full body recursion、terminality を持つが dedicated forall fixture はない。Yulang3 は binder を apostrophe-only に狭め、typed phase recovery/bounded gap を記録し、generic `InvalidToken` behavior を no-cascade Missing/Error record に置換する。

## 10. Known residual / deferred surface

general hidden-boundary residual は `ASOB-G` が記録し、このページは forall-specific exemption を追加しない。use-site integration、universal-type semantics、HIR/lowering、inference、diagnostics、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_forall_type`、`commit_direct_forall_type`、`scan_forall_keyword`、`scan_forall_binder`、`scan_forall_invalid_run`、`forall_recovery_candidate`、`forall_recovery_boundary_pending`、`parse_forall_body_for_ast`、`commit_direct_forall_body` を参照する。

fixture は `forall_type_primary_owns_a_non_delimited_binder_sequence_and_body`、`forall_is_nud_only_apostrophe_only_and_terminal`、`forall_recovery_keeps_its_phase_slots_non_cascading`、`forall_bounded_phases_defer_a_live_if_companion_before_consuming_trivia`。
