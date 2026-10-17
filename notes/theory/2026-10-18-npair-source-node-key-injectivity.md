# SourceNodeKey injectivity for explicit Operation rows

Status: primary-authored source-identity derivation, pending fresh review.
Sprint `npair-operation-self-effect-decision-20261018`, contract revision 3,
SHA-256 `0ab0e6a7353810204825ffd05815b2a42195a0915c5380c72831061b7355cd94`.
Requested Luna/high, cap 90s; effective model/effort UNKNOWN. This is a local
address lemma only: parent conditions closed **0**, parent OPEN; no semantic
incidence or `At` claim.

## Result

For two distinct explicit effect-row nodes in the same authentic parsed
signature, the retained `SourceNodeKey`s differ. The proof uses source position
identity, not green-tree uniqueness or `HashMap` uniqueness. `SourceNodeKey`
equality requires the same parse brand, the same green allocation pointer, and
the same start offset. Distinct explicit row occurrences have distinct starts:
each denotes its own bracket-delimited syntax node in the one parsed tree; a
descendant row begins after the enclosing row's opening bracket, while separate
siblings occupy distinct source positions. Sharing a green allocation through
immutable subtree reuse therefore does not alias their keys.

The admitted HIR row retains the key of its actual row syntax node. The
Operation signature traversal recurses through nested Function values before
consuming each child effect row. Only the declaration-root Function receives
the self-family. Thus every earlier nested explicit row has a different key
from the explicit root result row. The root lookup cannot hit a nested-row
cache entry; it constructs the root view with the self-family prepended, its
own concrete members/tail, source position, owner and Operation provenance.
This removes the prior artifact's conditional distinct-key premise for
authentic explicit Operation rows under these admitted carriers.

## Evidence chain

1. In `full_parse.rs:70–128`, `SourceNodeKey` stores the parse `Arc`, green
   node and text start. Equality checks `Arc::ptr_eq`, green pointer equality,
   and equal start; hashing uses the same three identity components. `SourceNode`
   is minted by `ParsedFile::source_root` and its child descent, and `key()`
   retains the parse brand, `node.green().into_owned()`, and the node's start.
   Cloning preserves these identity components.
2. `source_identity.rs:26–51` walks that parse-owned root and each syntax-node
   child, recording exactly one source key for the concrete `SyntaxNode` in
   `source_nodes`. `module.rs` wires `try_source_keys(&parsed)` into lowering
   before source annotation admission. This map is only the transport for each
   concrete node's key; its uniqueness is not used as a proof premise.
3. The pinned `source_annotation.rs` turns an admitted `BracketRow` into one
   `SourceEffectRow`, setting `position` to the key looked up for that exact
   node. Separate row occurrences therefore retain their occurrence keys;
   repeated family spelling does not merge their positions.
4. The frozen address artifact establishes that `candidate_signature_value`
   recursively processes argument/result Function values, then consumes their
   explicit effects slots. The root self-family is passed only at the
   pointer-equal declaration signature. Therefore earlier nested row cache
   entries are indexed by their nested row keys, while the self-family root
   lookup uses the root result row key.
5. By item 1 and the distinct-start property of distinct bracket-delimited
   occurrences, these two keys cannot compare equal. The root lookup therefore
   misses. The existing root miss branch prepends the family, appends the
   written concrete members, preserves the tail, and creates the view with the
   actual owner, row position and `OperationOrigin`.

This argument concerns cache addressing and view construction only. It does
not prove that a source contribution belongs to this view, that `Support(view)`
is semantically admissible, or that the original Operation contract projects
any arbitrary complete-interface witness to the latent root field. The prior
Operation semantic boundary remains exactly open.

## Assumptions and limits

- The rows are actual distinct explicit `BracketRow` nodes in one authentic
  parsed source tree, not caller-synthesized `SyntaxNode`s or malformed identity
  carriers.
- `SourceNodeKey`'s exact Eq/Hash and parse-owned minting are established by the
  pinned source. No global injectivity claim is made across parse products,
  source revisions, arbitrary syntax nodes, or nodes without a source row.
- Rowan's tree structure supplies the source-position property used above:
  separate row siblings have separate positions; nested explicit rows begin
  after the enclosing `[` token. The existing parser/source-annotation
  contract assigns a `BracketRow` position from that concrete node.
- No tests, builds, probes, compiler execution or code changes were authorized
  or performed. The fresh independent source/compiler review is pending.

## Frozen dependency hashes

| Path | SHA-256 |
|---|---|
| `tasks/agent-loop/sprints/npair-operation-self-effect-decision-20261018.md` | `0ab0e6a7353810204825ffd05815b2a42195a0915c5380c72831061b7355cd94` |
| `notes/theory/2026-10-18-npair-explicit-row-address-invariant.md` | `2796562ac2e359933ff5ac8ec58352a5b61b83264b5b88baa7ef8ce0065382ac` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |

The solver constructor hashes remain pinned in the reviewed prior address
artifact. Runtime model and effort are UNKNOWN; no children or descendants. No
scratch paths.
