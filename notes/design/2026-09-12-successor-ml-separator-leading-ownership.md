# ML separator-leading ownership

Status: Authoritative; M2 construction complete

Date: 2026-09-12

Approved-by: user selection of option A on 2026-09-12

## Decision

For every accepted ML application, separator leading between the completed
left expression and the admitted argument is direct native content of the
enclosing `OperatorChain`. `MlArgument` begins at the argument payload, not
at its preceding separator leading. This is uniform for identifier, braced,
parenthesized, literal and recovered arguments; it does not depend on the
surface spelling of an identifier or on a source-specific witness.

Thus the accepted shape is:

```text
OperatorChain := Left NativeLeading MlArgument(OperatorChain(Argument))
```

The separator leading belongs neither to `MlArgument` nor to its nested child
`OperatorChain`/`IdentifierExpression`. Multiple ML arguments remain sibling
`MlArgument` nodes. The argument child retains its payload and all following
child-owned leading, recovery, fixed tails and handoff behavior.

This applies to the CAST-T brace body control and the general `f x y` CST
contract. It replaces the narrower E5 operation which moved a leading Item
inside `MlArgument` for `x[a b]`: that isolated inside-leading expectation is
superseded, while E5's one-Item/no-rescan, IndexItem, close ownership and
sibling-ML continuation contracts remain in force.

## Owner and mechanics

`expression::operator_chain::ml_argument` owns this transfer. After the
existing ML admission decision and before opening `MlArgument`, it emits the
argument Item's remaining separator leading into the enclosing chain, then
moves the same Item into the existing nested expression entry. It preserves the
Item payload, origin, line entry, fence, ML-continuation capability and returned
successor unchanged. No scanner pass, source replay, context stack, recovery
state, synthetic token, node kind or diagnostic vocabulary is introduced.

Only accepted ML admission changes ownership of this leading. Rejected
arguments, caller/outer boundaries, fences and recovery leading retain their
existing owner. A malformed child still owns its recovery beneath
`MlArgument`; a protected successor remains pending exactly as before.

## Supersession and scope

This supersedes the leading-emission sentence in
`2026-09-03-yu-syntax-g4b-e5-index-ml-application-correction.md`, **Decision**,
which placed the admitted `b` Item's leading inside `MlArgument`, and the
corresponding E5 expected CST topology only. It does not supersede that
document's admission, IndexItem, `]` ownership, no-rescan or sibling-handoff
decisions.

It confirms the accepted outer-leading topology already specified by
`2026-08-20-yu-syntax-chasa-architecture.md` for general ML application and
the CAST-T brace worked example. It changes no grammar admission, recovery
role, layout policy, public API, AST product or parser phase topology.

## Required evidence

M2 construction must prove direct Rowan node/token order and ranges for:

- `f x y`, renamed/Unicode identifiers and sibling ML arguments;
- `x[a b]`, `x[a b c]` and `x[a b(c) d]`, retaining Index/Call close owners;
- the CAST-T brace body sample;
- braced, parenthesized and literal arguments;
- horizontal/comment/deeper-newline separators;
- malformed child recovery and protected caller close/EOF handoff; and
- the existing normalized/quote-carrier ML control.

Run focused ML, Index, Cast and normalized controls, one package check, scoped
format/diff, and independent compiler/recovery plus regression review. Zero
benchmark samples/processes unless a material performance uncertainty appears.

## Construction status

Completed on 2026-09-12. `ml_argument` now emits the admitted Item's remaining
leading immediately before opening `MlArgument`, then transports the same Item
through the existing child entry. The superseded E5 assertion and one stale
fixed-tail sibling assertion now require direct outer-chain separator trivia;
their retained Index and fixed-tail recovery contracts are unchanged.

Four ML controls, four Index controls, two Cast aggregate controls, nine
normalized Pratt controls, one normalized quoted-fence control and the repaired
fixed-tail control passed. `cargo check -p yu-syntax`, scoped formatting and
diff checks passed; it retained three pre-existing warnings. Independent
pre-write specification, compiler/recovery and regression reviews were clean
after one bounded stale-tail expectation repair, whose delta review was clean.
No benchmark process ran.

The CST-derived diagnostics interpreter, recovery-ledger retirement, public
cutover and unrelated expression recovery remain outside this construction.
