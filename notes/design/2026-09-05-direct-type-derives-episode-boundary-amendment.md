# Direct Type derives episode-boundary amendment

Status: Authoritative

Scope: source-free direct rewrite に、`TypeDeclaration` だけの
`DerivesClause` direct-CST construction を追加する。これは Gate 6 の shared derives
owner を完成・認定するものではない。旧 chasa parser、public/root dispatch、AST、HIR、header
projection、diagnostic record、`StructDeclaration`、Yumark は変更しない。

Drafted-by: primary with architecture review

Reviewed-by: independent compiler/recovery review and specification review, 2026-09-05

Approved-by: user, 2026-09-05

Supersedes: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
`DRV-T` にある rollback-owned episode frame / `ParseLocal` を読む**実装経路だけ**。
`DRV-G/J/T/R` の grammar、attachment authority、CST、recovery、scope exclusion は
supersede しない。

## 日本語要約（承認対象）

これは、旧パーサの既存 `DerivesClause` 文法を新しい direct `TypeDeclaration` へ**隔離して
構築するだけ**の C15 である。Gate 6、D11/RB-DRV、旧パーサとの置換、public dispatch、AST、
diagnostic、`Struct`、Yumark は完了扱いにしない。後続の shared derives owner が全 declaration
family と認定を閉じる。

難所は `derives` / `via` が「外側の RoleReference だけを止め、内側の型式では普通の識別子で
あり続ける」ことにある。そこで既存の全再帰へ伝播する `Stops` には入れず、current logical
TypeExpression episode だけへ immediate argument `TypeOuterBoundary` を渡す。

- Equality RHS は `DERIVES`、trailing RoleReference は `DERIVES | VIA | WITH`、header
  RoleReference はそれに `IMPL | EQUALS` を足す。
- trailing RoleReference に入る時だけ、既存 flat `STOP_WITH` をその role から除き、
  outer-only `WITH` へ移す。これにより `(Eq with X)` のような内側を誤って切らず、外側の
  `with` だけを返せる。
- same-slot candidate / malformed retry / tail / path はこの値を保つ。一方、group、call item、
  TypeApply argument、arrow RHS、forall body、record/row/variant payload など新しい TypeExpression
  に降りる edge では `NONE` にする。close から戻れば caller の値がそのまま再開するため、
  state / depth counter / stack は要らない。
- `Recover`、`Item`、`Stops`、cursor、token buffer、source replay は増やさない。`StatementLineHandoff`
  も別の immediate argument のままである。

`TypeDeclaration` は complete name と parameter scan の後だけ header `derives` を受ける。incomplete
name は受けない。accepted clause の後は既存 TND form judge へ同じ pending Item を渡し、`=` は
Equality、`with` / `impl` は future owner へ non-consume handoff する。RoleReference が Complete / Missing /
boundary まで malformed のどれでも、`with` / `impl` の前に余分な `DefinitionIntroducer` recovery を作らない。
trailing clause は Equality が選ばれた後だけに存在し、`type Id = derives Eq` は Missing RHS 一つと
valid clause 一つになる。Nominal には trailing phase を作らない。

clause 内の initial role、comma 後 role、`via` 前後の全 trivia gap には C14 の
`StatementLineHandoff` を渡す。ordinary の equal/shallow newline、braced sequence、Catch-through-inline
newline は元の Item を outer owner へ返す。zero-inline `CatchBracedArm` は外側 handoff ではないため、
header なら既存 EqualityRecovery へ、trailing なら clause 自身の role/target recovery 後に
Equality/outer continuation へ返す。二つ目の form recovery / Missing/Error は作らない。

direct CST は既存 `DerivesClause` / `DerivesKw` / `ViaKw` を `TypeDeclaration` の direct child として
emit するだけであり、wrapper、新 SyntaxKind、synthetic separator、AST field は作らない。exact
`derives` 一つは必ず clause 一つと mandatory role slot 一つを作る。実装前に fresh TypeExpression edge の
全 inventory、header/trailing attachment、`with` / `impl` / `=` handoff、nested fencing、braced/Catch、
Missing/Error cardinality、losslessness を focused fixture で固定する。

## 1. Allocation and authority

The authoritative derives surface is unchanged.

```text
DerivesClause := derives RequiredTypeExpression(RoleReference)
                 { , RequiredTypeExpression(RoleReference) }
                 [ via RequiredRawIdentifier(ViaTarget) ]
```

This C15 slice permits only the direct Type owner to construct that existing surface in an
isolated rewrite harness.  It allocates no new public grammar gate and cannot certify
Gate 6, D11, RB-DRV, AST/direct parity, diagnostic identity, or legacy parser replacement.
The later shared derives owner remains responsible for all declaration families and for
that certification.

The governing text is `DRV-G/J/T/R` in
`2026-08-20-yu-syntax-chasa-architecture.md`, the successor rewrite plan Gate 6, the
minimal token-transaction amendment, and the C14 `StatementLineHandoff` amendment.

## 2. Immediate Type-expression boundary value

`Derives` and `via` are contextual boundaries of the *current logical* TypeExpression
episode.  They must not be inserted into `Stops`: `caller_stops` is intentionally propagated
through current recursion and would therefore make a nested group, call, arrow RHS, forall
body, row, record field, or variant payload stop incorrectly.

The direct rewrite instead uses this lifetime-free immediate Copy scalar, separate from
`Stops` and separate from `StatementLineHandoff`.

```rust
#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct TypeOuterBoundary(u8);

const NONE: TypeOuterBoundary = TypeOuterBoundary(0);
const DERIVES: TypeOuterBoundary = /* bit */;
const VIA: TypeOuterBoundary = /* bit */;
const WITH: TypeOuterBoundary = /* bit */;
const IMPL: TypeOuterBoundary = /* bit */;
const EQUALS: TypeOuterBoundary = /* bit */;
```

This is a small bitfield scalar passed as an immediate parser argument, not parser state.
It neither stores input nor changes `Recover`, `Item`, the Rowan builder, a context/frame,
depth counter, cursor, token buffer, source range, or replay mechanism.  `Stops` remains
`u16`.

The only contexts which introduce a nonempty value are:

| current outer slot | value |
| --- | --- |
| Type equality RHS | `DERIVES` |
| trailing derives RoleReference | `DERIVES | VIA | WITH` |
| Type header derives RoleReference | `DERIVES | VIA | WITH | IMPL | EQUALS` |

`WITH` is outer-only for every derives RoleReference.  At the trailing RoleReference entry,
the applicable flat `STOP_WITH` is removed from that role's `caller_stops` and translated to
`TypeOuterBoundary::WITH`; punctuation and unrelated caller stops remain unchanged.  Thus
the equality RHS retains its existing `STOP_WITH` before an attachment is accepted, but no
flat contextual word stop leaks through a role's nested TypeExpression entry.  `IMPL` and
`EQUALS` are Type header RoleReference handoffs only.  They let a complete or recovered
header role return the original pending item to the existing/future Type form owner.
Equality RHS does not gain an `impl` or equals boundary from C15.

Every ownership decision for `derives`, `via`, `with`, `impl`, or the header's `=` uses this
value through one exact boundary helper.  Word bits match only a maximal lexical
`Identifier` Item with the exact text; `EQUALS` matches only the literal Equals Item.
`derivesx`, `viax`, `withx`, `implx`, and suffix-bearing spellings are ordinary Type syntax.
No raw `caller_stops` membership may decide one of these contextual boundaries.

Same-slot candidate, mandatory malformed scan, retry, NUD, tail, path continuation, and
return-to-caller preserve their incoming `TypeOuterBoundary`.  In particular, a malformed
outer path retry can return header `=` without consuming it.  A **fresh** nested
TypeExpression entry receives `NONE`.  The finite current inventory is:

- parenthesized group item and every generic delimited/call item;
- TypeApply argument;
- arrow RHS, including its candidate, malformed scan, and retry;
- forall body, including its candidate, malformed scan, and retry;
- record field RHS;
- bracket/effect-row item and its retry;
- polymorphic-variant payload and its retry.

Forall binder recovery itself remains in its current episode; its body is the fresh entry.
A leading bracket row item is fresh, while the tail after the completed row resumes the
caller value.  Every direct call to a mandatory TypeExpression entry or
`type_expr_from_nud` must be classified as preserve or fresh before code lands.  If an edge
cannot be classified, the change stops there; it does not add ambient state as a shortcut.

Thus a callee returning from a completed nested expression automatically resumes the
caller's outer boundary value through its local argument.  This gives unbounded nesting without
a depth limit or push/pop state.

## 3. Type declaration ownership

`type_decl.rs` owns attachment qualification and all Type form/line handoff.  A small new
`rewrite/derives.rs` may own only one accepted `DerivesClause`: direct Rowan construction,
comma role loop, raw `via` target, and its mandatory recovery.  The Type owner passes its
immediate `StatementLineHandoff` and baseline into this driver.  It does not own Type form
selection or a new delimiter owner.

Before every clause-local trivia consumption—the initial role, role-to-comma/`via` gap,
comma-to-next-role gap, and `via`-to-target gap—the driver applies one direct gap classifier.
The only current-direct non-line claim is C14's typed `ActiveStatementCompanion`; there is no
generic ambient query or stack.  An active caller boundary or that companion leaves the
original pending Item and its trivia untouched.  Empty/same-line and ordinary-layout
strictly-deeper gaps are the only continuation gaps.  Ordinary equal-or-shallower newline,
and every physical newline under `BracedStatementSequence` or
`CatchArmSequenceThroughInlineCanonicalStatement`, are outer-owned and hand off the original
Item.  `CatchBracedArm` is different: a physical newline rejects continuation but has no
outer statement-sequence claim.  A header clause returns the untouched pending Item to the
existing Type EqualityRecovery path; a trailing clause first completes only its own required
role/target recovery, then returns that same Item to the already-selected Equality/outer
statement continuation.  The latter never runs a second form recovery or emits a second
Missing/Error.  Neither phase attaches across that gap nor grants Nominal authority.  This
applies identically to initial role, comma role, `via`, and via target.  It keeps braced/Catch
statement separation out of the shared type parser without putting provenance in `Item` or
`Recover`.

### Header

Only a complete Type name, after the existing same-line parameter scan and before the
existing TND form judge, has header attachment authority.  An incomplete name has no such
authority.

The owner obtains one pending Item with its original leading trivia.  Existing C14 authority
is considered first: typed active companion, active caller boundary, equal-or-shallower
ordinary newline, braced statement-sequence newline, and the distinct Catch line rules.
Those rules retain the original Item for their exact handoff or EqualityRecovery route.  An
empty, same-line, or strictly-deeper ordinary-layout gap may then accept exact `derives`; all
other spellings and all rejected gaps proceed to the unchanged form judge.

After each accepted clause, the Type owner repeats that same attachment decision.  When no
further clause qualifies, it gives the same pending Item to the existing TND judge:

- exact `=` selects Equality;
- any accepted header clause outcome—complete RoleReference, one Missing RoleReference, or a
  malformed RoleReference ending at that boundary—followed by exact `with` or `impl` returns
  its pending Item and trivia directly, with no `DefinitionIntroducer` Missing/Error beyond
  the role's own recovery.  The isolated direct harness leaves that future owner unconsumed;
  it does not pretend to implement it;
- EOF, semicolon, active close, and the C14 newline cases retain their existing Nominal or
  handoff behavior;
- C15 neither creates colon nor brace form authority.

`derives` remains excluded from a declaration type parameter spelling.

### Equality RHS and trailing attachment

Only after Equality, including its current local recovery selection, has been chosen may a
trailing attachment exist.  Its mandatory RHS starts with `TypeOuterBoundary::DERIVES`.
An exact outer `derives` is therefore a boundary both before a missing RHS and after a
complete or recovered RHS.  The Type owner then applies the same qualifying-gap rule and
may construct repeated trailing clauses.

Consequently:

```text
type Id derives Eq = Int derives Debug
type Id = derives Eq
```

have header plus trailing clauses in the first case and exactly one missing RHS plus one
valid clause in the second.  Nominal has no trailing phase.  A fresh arrow RHS, forall body,
or delimited inner expression sees `NONE`, so its `derives` spelling remains ordinary type
syntax; after its close, outer visibility returns.

`StatementLineHandoff` remains a distinct immediate argument used by both the existing Type
form/attachment-gap decision and the clause-local gap classifier above.  C15 does not
create, reset, or fold it into `TypeOuterBoundary`.

## 4. Direct CST and recovery

Existing `SyntaxKind::{DerivesClause, DerivesKw, ViaKw}` are reused.  Each accepted clause is
a direct `TypeDeclaration` child: header clauses precede `=`, and trailing clauses follow the
RHS `TypeExpression`.  No attachment/list wrapper, synthetic separator, new SyntaxKind,
AST field, or source-backed result is created.

An accepted exact `derives` cuts one clause and creates one mandatory RoleReference slot.

- A boundary before the role emits exactly one direct missing TypeExpression and leaves the
  boundary pending.
- A malformed role uses the ordinary direct Type Error and same-slot retry; it does not add a
  second outer missing slot.
- Each leading, repeated, or terminal comma makes one mandatory role slot.  A following
  `derives`, `via`, `with`, close, separator, or EOF remains pending at its designated owner
  boundary.
- Adjacent non-comma Type primaries remain TypeApply, never an invented list separator.
- `via` is contextual only within an accepted clause and requires exactly one raw Identifier.
  Its missing/malformed/retry behavior is separate from RoleReference recovery.
- Consumed trivia/text is emitted once.  A pending Item retains its leading trivia unchanged
  until its owner accepts it.

One accepted `derives` keyword always yields one `DerivesClause`; no typed diagnostic record
or AST recovery product is claimed in this slice.

## 5. Required focused evidence

The implementation must add direct rewrite fixtures for:

- nominal/equality header attachment, header plus trailing attachment, repeated clauses,
  comma roles, and `via`;
- post-clause `=`, `with`, `impl`, EOF, semicolon, active close, and all C14 line handoffs;
  `type T derives Eq with:` and `type T derives Eq impl P` prove direct pending-item/trivia
  handoff with no extra Missing/Error; `type T derives with:`, `type T derives impl P`, and
  malformed-role counterparts prove the same handoff after exactly the role recovery;
- complete, missing, and malformed/retried RHS, including `type Id = derives Eq`;
- outer-only fencing through group, call/delimited item, TypeApply, arrow RHS, forall body,
  record field, bracket/effect row, variant payload, and path/retry;
- grouped arrow/forall/record/row return followed by a valid outer trailing clause;
- trailing-role outer `with` plus nested group/call/arrow/forall `with` controls, proving
  only the outer role returns it;
- header `type Id derives Eq::@ = Int` recovery returning the exact `=`, and
  `type Id derives (Eq::@ = Int) = Body` proving fresh nested suspension;
- initial-role, comma-role, role-to-`via`, and via-target gaps under ordinary deeper layout,
  ordinary equal/shallow layout, braced sequence, zero-Catch, and Catch-through-inline; the
  zero-Catch rows distinguish header EqualityRecovery from trailing own-recovery plus
  Equality/outer continuation;
- role and `via` Missing/Error cardinality, lossless text, direct child order, and boundary
  trivia ownership;
- ordinary `derives`/`via` outside their contextual owner, and exact-word collisions
  `derivesx`, `viax`, `withx`, and `implx`.

No existing C12--C14 expectation may be rewritten merely to accept C15 output.  Focused
post-write specification and sibling-regression review are required; no performance
measurement is triggered because this adds neither allocation nor a new scan/replay path.

## 6. Explicit exclusions and later owner

C15 rejects additions to `Recover`/state, `Stops`, `Item`, context/frame/depth/cursor/token
storage, source replay, public/root dispatch, AST/HIR/header/diagnostic output, Struct
attachment, new delimiter ownership, and incidental changes to `with`, `in`, `else`, or
`elsif` contracts.

Gate 6's later shared derives owner must close the complete Type and Struct owner matrix,
the D11/RB-DRV ledger, adoption/certification, and any public integration.  C15 is only a
construction callee on that route.
