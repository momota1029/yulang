# Operation row keys: parser audit and exact remaining owner

Status: frozen source evidence and conditional obstruction; independent review NOT_RUN.
Author: `/root/npair_parser_row_key_separation`; no coauthors or descendants.
Sprint: `npair-parser-row-key-separation-20261018`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.
Parent conditions closed: **0**; parent OPEN. Original theorem, quantifiers,
accepted source domain, F1/FK1, N-Transport and complete Call remain unchanged.
No Operation semantic projection, `At`, native theorem or production authority
is established here.

## Actual result and application

The pinned parser files expose the row construction call and its ordinary and
recovery continuations, but do not establish that this call emits a positive
width opening token. The indispensable owner is
`crate::cursor::recovery::emit::emit_token_item`, called immediately after
`start_node(BracketRow)` at `type_expr/mod.rs:1609`. Its implementation and
the `Item` payload/token constructors are outside the exact read grant.
This assignment stops at that boundary as its contract requires.

Consequently the earlier explicit-row address/cache lemma remains conditional.
The audit does not replace it with a renamed theorem. It locates the unresolved
emission premise and shows why the pinned HIR consumer does not discharge it.
No authentic source collision was found or alleged.

For the particular Operation root lookup, reuse the prior cache argument:
each earlier cache seed is an explicit retained row, from this construction's
fresh local map; omitted rows do not seed it. Its required premise is
`key(earlier) != key(root_result_row)` for every such earlier seed. A proof that
all retained explicit rows have positive width would suffice for incomparable
row occurrences: ordered disjoint sibling subtrees cannot have the same start
when both have positive width. A proper ancestor and descendant cannot share
the same green allocation in a finite acyclic immutable tree. Thus combining
positive row width with the existing exact Eq characterization would also
cover ancestor pairs without assuming that all syntax nodes have distinct
starts. These are mathematical sufficiency facts, not established parser
emission facts. No external Rowan implementation was added to the dependencies.

## Pinned source chain

1. `full_parse.rs:317–342` invokes `cursor::parse_root` and stores the returned
   green tree under a fresh parse brand. `cursor.rs:84–98` starts a root node
   and delegates actual root statements to
   `crate::root_statement::parse_root_statements`. That callee is outside the
   pinned reads. The cursor does not itself supply a delimiter or row-width
   invariant, nor validate unique row starts.
2. `type_expr/mod.rs:780–800` recognizes a leading row through
   `token_kind(&primary) == Some(TokenKind::LBracket)` and forwards `primary`.
   The bracket-arrow tail calls the same row constructor at 1551–1564.
   `type_bracket_row_normalized` at 1595–1626 starts a BracketRow, calls
   `emit_token_item(open)`, delegates its body/close to
   `type_delimited_normalized`, and finishes the row on every returned exit.
   This establishes the placement and commonality of the emitter call. Neither
   the enum observation nor the function name proves the emitted token's text
   length, kind or persistence.
3. `source_annotation.rs:409–503` admits an optional leading BracketRow,
   recursively parses arrow results and groups, and moves effects into the
   owned argument/value carrier. `parse_group` at 505–527 enforces its listed
   parenthesis shapes. There is no clone of an effect-row carrier into two
   slots in these functions. This agrees with the prior one-pass cache proof.
4. `source_annotation.rs:529–586`, `parse_row`, copies the syntax node key and
   iterates its nontrivia elements. It **does not require an opening token, a
   closing token, or any element at all**. An empty element list returns an
   empty SourceEffectRow. This is a property of that consumer, not evidence
   that an authentic parser can produce such a row. Hence HIR admission alone
   cannot replace the missing emission premise with positive row width.
5. `declarations` at 146–148 rejects an ActDeclaration when
   `has_recovery(&node)` returns true. The implementation of `has_recovery`
   is not pinned here. Its name is not evidence of which recovered/empty-width
   forms it detects. No syntax-error-free source restriction is inferred.
6. `full_parse.rs:87–128` compares parse pointer, green pointer and start,
   hashes those same components, and mints a key from the parse-owned node.
   `source_identity.rs:36–51` transports each node's key into `source_nodes`;
   `parse_row` transports it unchanged. The HashMap is not an injectivity proof.

## Ordinary and recovery case coverage

| Visible case | Pinned construction/consumer evidence | Remaining premise |
|---|---|---|
| Ordinary empty `[]` or populated row | Common opening emitter; matching close emitted by `emit_delimited_close_token` (delimited.rs:124–126,1247–1249); row consumer permits delimiters and supported operands | Opening emitter produces a positive token; no executed input claimed |
| Boundary immediately after opening | delimited.rs:81–89 calls item/close missing helpers and returns to the same row finish | Actual opening emission; actual recovery output/detection |
| EOF after opening or during body | delimited.rs:110–115,182–187 invokes missing helpers inside the already-started row | Same opening emission; helper behavior is not inferred from its name |
| Missing close at caller/outer boundary | delimited.rs:169–180 calls missing helpers, hands item back, then row finishes | Same opening emission; no global recovery exclusion established |
| Separator without an operand, trailing separator | delimited.rs:221 onward and `type_after_separator_normalized` call missing helpers before continuing | Same opening emission and missing-helper output |
| Malformed non-NUD body and retry | delimited.rs:243–263 delegates retry; subsequent parsing returns to this row | Same opening emission; retry/error emitter semantics unpinned |
| Foreign/mismatched close | `retry_bracket_row_close_normalized` (982 onward) explicitly wraps rejected closes in TypeDelimitedForeignClose nodes | A direct TypeDelimitedForeignClose element is rejected by `parse_row`'s default arm; remaining emitted forms still require their owners |
| Nested row parsed inside a row body | Body can call `type_expr_from_nud_normalized` at delimited.rs:267 onward | A direct row-containing TypeExpression is rejected unless its sole nontrivia operand has Identifier/SigilIdentifier kind; do not infer arbitrary descendant coverage from this arm alone |
| Recovery after a leading row or after bracket-arrow row | mod.rs:1388–1395,1408 onward,1567 onward adds missing/retry actions after the row construction | Does not prove or erase the row's opening token without emitter evidence |
| Empty-width/shared-green row | Key Eq allows equal keys if parse/green/start all agree; parse_row does not independently reject emptiness | Authentic reachability unresolved; **not** a source counterexample |

The common constructor call makes opening emission the useful next seam:
establish it once at its real owner rather than repeat a separate assumed-token
proof for each recovery branch. Other `BracketRow` emitters reachable through
unpinned root/parser owners have not been exhaustively excluded. This audit
does not assert the leased module is the sole constructor in the repository.

## Prior evidence reused and rejected

- Reused: the frozen conditional cache proof by
  `/root/npair_explicit_row_address_invariant`, including local cache scope,
  traversal order and the self-family miss construction, only under its premises.
- Reused: exact Eq/Hash and HIR transport from the primary-authored injectivity
  candidate; the prior closeout's accepted major finding remains in force.
- Rejected as a proof: distinct-start assertions based only on bracket syntax,
  HashMap insertion, enum/function names, or presumed absence of recovery.
- The source_identity ambiguity test at full_parse.rs:381 onward manually
  splices green nodes. It was only read, never run; it is not authentic parser
  evidence and supplies no source-qualified counterexample.

## Exact TODO and stop boundary

`ROW-OPEN-EMISSION-1`, owned by Luna's next source assignment: pin and read
`cursor::recovery::emit::emit_token_item` and the exact `Item` token emission /
`token_kind` / LBracket payload constructors it delegates to. Establish whether
each actual opening item reaching `type_bracket_row_normalized` emits positive
text inside that row before any descendants, on all ordinary/recovery paths.
Falsifier: an authentic parser-produced earlier cache-seeding row and root
result row with equal parse/green/start, or an authentic reachable empty-width
row invalidating the proposed width invariant. An empty synthetic carrier or
assumed transition is insufficient. If relying instead on admission rejection,
pin the actual `has_recovery` implementation and prove it rejects the exact
case before `SourceOperationDeclaration` admission. Root construction coverage
may require `root_statement::parse_root_statements` and its actual delegation;
this is another read-authority boundary, not an inferred global guarantee.

No implementation TODO is justified yet: no authentic bad emission or key
collision has been demonstrated. The minimal next action is an exact source
read grant, not code, tests, a new semantic rule or a malformed-carrier probe.
After the source premise is independently established, apply it directly to
the frozen cache lemma. The original Operation semantic projection and parent
quantifiers remain open even if the root cache-miss fact is established.

## Frozen dependencies and resources

All hashes below were checked with `sha256sum`; no pin mismatch was observed.

| Dependency | SHA-256 |
|---|---|
| Sprint contract rev1 | `f9e0c7476e2cd03d0d83ef7c608807b01f2cdc9e9bb1677440692556f7d24b96` |
| cursor.rs | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| type_expr/mod.rs | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| type_expr/delimited.rs | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` |
| full_parse.rs | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| source_identity.rs | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| Prior conditional address artifact | `2796562ac2e359933ff5ac8ec58352a5b61b83264b5b88baa7ef8ce0065382ac` |
| Prior rejected unconditional injectivity artifact | `8ab47830c985e13a4823a8a707ad6ee0b3ff9bb970f68da752d517052f59eeb6` |
| Prior primary adjudication/closeout | `4efd9fccf44fd905a6e0e1446f019c18842d45f0dd27491aa63113fa06b8d3be` |

Requested Sol/high, cap 240s, Astra0, children0; observed model/effort and exact
runtime/CPU/RAM UNKNOWN. Charge the full reservation; no refund inferred.
Checks: static reads/search and dependency hashes only. Some broad initial
output truncated; conclusions use subsequent targeted reads. No tests, builds,
probes, compiler execution, Cargo, Git or network. No native execution evidence.
Only this artifact and the one assigned inbox were written; scratch paths none.
No production or shared-record writes, reviewer appointment or delegation.
Writer STOPPED after frozen submission; no descendants or unresolved child leases.
