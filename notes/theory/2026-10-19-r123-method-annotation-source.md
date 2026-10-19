# R123: original member annotation sources in three independent parses

Status: **conditional source-constructor/index correspondence; review pending**.
Assignment `R123-PROOF`, revision1. Sole writer/author `/root/r118_proof_lane`;
no coauthors or descendants. Contract rev4 SHA-256
`77b3aa1b50738366590faac3524ac86c38603155fa74c6ffe8fe82c648bded63`;
baseline `beb54cec76867035901c1d1a2b9ec02858c945d4`.

## Parent, exact inputs and explicit parsed-tree premise

Apply only to R119's unsupplied original own-annotation/member-source input.
Its authentic executable member owner M, semantic target join T and successful
ordinary admission A remain OPEN, as do R85 adoption, all six effect parents,
Simple-sub/evaluator A/B and independent F1/FK1/foreign-continuation quantifiers.
No current method execution, endpoint typing or result is asserted.

The three sources use the contract's unchanged R100 role/signature/answer context:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    MEMBER
}
my answer = SecondInt::second 1 2
```

| Case | Actual MEMBER line | Bytes/no final LF | Specified source SHA-256 |
| --- | --- | --- | --- |
| U | `my second self selected = selected` |148|`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`|
| V | `my second self (selected:int) = selected` |154|`9785e53f0ac8782dfa8369e844054f0e18234b92973ddde01c6b9b236cde63cd`|
| C | `my second self (selected:[] int) = selected` |157|`335126c188f068f2682a94b5e0bf7b81687ec453b53ca62fedec4bdb9f760060`|

Let P_U/P_V/P_C be three **independently returned** ParsedFiles for those exact
sources. Premise S supplies their actual diagnostic success and intended node
kinds/parentage asserted by the targeted structural test. Premise R supplies
successful supported ShadowArtifact preflight/retention/association, including
allocation and unambiguous source mappings. Neither premise was executed or
observed by this author. Whole grammar/root-dispatch/lexer correctness is not
derived here. Rev4 explicitly fixes this boundary; no unlisted parser is read.

## Constructor-preserving tree and annotation ownership

The following pinned constructor facts explain the S tree without asserting
that inspecting local rules proves actual diagnostic-free parsing of all bytes.

- `impl_declaration_normalized` (impl_decl.rs168 onward) starts ImplDeclaration
  and delegates to impl_tail. The same-line colon constructs ImplDescription
  (impl_tail.rs234 onward); its brace body calls braced_statement_block_normalized
  (382–409). RoleDeclaration independently takes its own braced body route
  (role_decl.rs338–358). They are separate original enclosing occurrences.
- The braced statement constructor starts BracedStatementBlockExpression,
  emits its own brace/trivia and runs a Statement sequence (statement.rs578–628).
  The member remains a BindingStatement beneath its actual Statement beneath
  the implementation body. Binding construction (binding.rs185–254) creates
  BindingHeader, parses the target until Equals, closes the header, then creates
  a separate BindingBody. Inline body parsing is delegated; its returned shape
  remains S, not an uninspected expression-emitter theorem.
- Pattern's ML-tail rule (pattern/mod.rs1192–1241) emits each intervening space
  before a PatternMlApplicationTail and parses its argument at ML precedence.
  Consequently the second and third identifier occurrences belong to successive
  sibling tails; a recursive argument does not absorb the next sibling.
- U's second tail contains its plain selected IdentifierPattern. V/C instead
  contain ParenthesizedPattern → Pattern. `pattern/delimited.rs`'s Parenthesized
  owner (47,74 onward,215 onward) owns parentheses and local close/stops. Inside
  that Pattern, colon creates a sibling PatternTypeAnnotation **after that
  selected IdentifierPattern** (pattern/mod.rs1173–1191). It is not a child of
  self, target head second, body selected or the role signature.
- C's annotation type starts with `[`: type_expr/mod.rs780 onward starts
  TypeExpression and calls type_leading_bracket_row_normalized (1355 onward),
  which builds BracketRow (1608 onward) before its following type head int.
  type_expr/delimited.rs's immediate RBracket branch (100–130) emits the close
  without an item. Thus `[]` is a retained explicit empty BracketRow beneath
  selected's PatternTypeAnnotation, rather than an absent annotation or an
  inferred/solved empty effect. V has its own ordinary int annotation without
  that row; U has no such own annotation.

For each P separately, the original ownership spine is:

```text
ImplDeclaration / BracedStatementBlockExpression / Statement / BindingStatement
  BindingHeader / Pattern
    IdentifierPattern(second)
    PatternMlApplicationTail / Pattern / IdentifierPattern(self)
    PatternMlApplicationTail / Pattern /
      U: IdentifierPattern(selected)
      V,C: ParenthesizedPattern / Pattern
             IdentifierPattern(selected)
             PatternTypeAnnotation / TypeExpression
               C additionally retains BracketRow([]) before int
  BindingBody / original body subtree / IdentifierExpression(selected)
```

This is node ancestry, not raw child ordinals: raw children include trivia and
punctuation. The ordered source identifier list is second/self/selected. The
head second is the member name, not an extra executable formal. Self has no
own annotation in all cases. The role signature's second occurrence has its
own separate declaration annotation, unchanged in all parses. No signature
annotation is copied into the implementation tree. The body selected is outside
the header and is a distinct occurrence, regardless of equal spelling.

## Original parse brand and exact node-to-index chain

`full_parse.rs::parse_file` (317–340) checks the supplied header's source Arc,
obtains a green root and constructs ParsedFile with a fresh `parse_identity:
Arc::new(())`. ParsedFile cloning retains that brand; **independent parse calls**
do not share it, even for equal text/green content.

`source_root` (134 onward) returns SourceNode(original brand, actual green root).
`SourceNode::children` copies that brand while descending actual node children;
`key` (113 onward) stores the same brand, retained green node allocation and
original start offset. SourceNodeKey equality/hash (89 onward) use all three.
`owns_source_key` checks the original parse brand; it is not a text/range equality
test. Ownership alone does not prove membership of an arbitrary caller node:
the actual root/children constructors mint the keys used below.

Induct on the path from the returned root to the original Impl, member, header,
formal, annotation, row and body nodes. Each descent carries P's brand and the
actual subtree; each resulting key K_P(n) designates that original node. All
these original descendant keys satisfy P.owns_source_key. Across P_U/P_V/P_C,
keys differ by brand; no cross-parse opaque-ID equality is needed or claimed.

`source_identity.rs::source_keys` (26–34) starts with that source_root, repeatedly
records `(node.syntax().clone(),node.key())`, then visits its actual children.
This maps the existing syntax nodes to their constructor-minted original keys;
it does not parse identifiers again or invent a key from an offset/string.

`ShadowArtifact::from_parsed` (624 onward) retains P itself, checks structural
limits and empty diagnostics, and mints its separate artifact brand. `retain`
(1198–1273) performs a preorder walk over **all raw elements**, recording every
node/token's kind, range, node/token flag, original parent, raw ordinal and
ordered children. It records each node's original key in position_source_keys
and the key→PositionId index. Reverse pushing preserves raw child order on
pop; induction on this work stack gives exact original ancestry and ordered
binder/annotation containment in the retained positions. Tokens have positions
but no SourceNodeKey; their node parent and raw edge must be retained instead.

PositionId is branded by this ShadowArtifact and its index; it is not a HIR
parameter or executable member ID. `retain_source_position` marks duplicate
keys ambiguous, and `source_position` (833–842) rejects foreign brand, ambiguous
or missing keys instead of choosing an occurrence by text. Under R the original
member/formal/annotation/body keys map to their exact original positions.
The distinct formal/body selected nodes have distinct kinds/starts in S; their
keys and retained preorder indices are therefore distinct within each artifact.
Parent/child links preserve that the annotation belongs to the formal Pattern
and the body belongs to BindingBody. No guessed numeric range/index is needed.

The annotation inventory also records PatternTypeAnnotation/TypeAnnotationTail
positions, but its correspondence remains PendingTypedPortAndProfile; it does
not manufacture typed/executable roles or an annotation-to-formal certificate.

## What the role/impl declaration APIs actually provide

`pending_role_impl_sources` (shadow.rs919–928) scans retained positions and returns
only position/kind for RoleDeclaration and ImplDeclaration in retained order.
For each exact S tree there are those two original declaration nodes. It does
not enumerate member headers, formals or own annotation fields.

`with_associated_method_role_sources` (931–1049) builds its source-key/node map
from the same P, validates original node kinds, parse ownership, unique keys and
round trips to retained positions, then publishes borrowed
AssociatedRoleImplSource {source,node}. All validation precedes the callback.
For these fixtures there is no FieldTail; the answer's `::second` is PathTail,
so field-tail association roots supply no qualified executable member target.

The declaration node gives access to its original subtree, so callers can
traverse it to recover the binder/annotation structure above. The API does not
itself return an ordered executable binder vector, normalized own annotation,
annotation ownership judgment, role/member/impl semantic IDs, selected target,
typed body, lexical executable environment or closure. Successful association
is source-object correspondence; it is not member resolution or admission.

## Apply only the annotation-source premise to R119

Under S/R, R119's future producer can receive exact original keys for the
member, ordered self/selected formal occurrences, selected's own optional
annotation subtree and the distinct body occurrence. It must retain these
objects rather than reconstructing them from spelling/signature. This supplies
only that **source input**; it does not produce R119's admitted owner/vectors.

Charter §21 then prescribes the conditional roles if a future authentic
producer preserves those own source boundaries: self is Value in all cases;
selected is Value for U, Value for V, Computation(empty,int) for C. Explicit
empty source computation syntax remains distinct from absence/ordinary int;
a solved empty row or body use cannot choose the entry role. No executable
annotation object, runtime role, int endpoint constraint or selected method is
constructed by these syntax/index APIs. R119's original M/T/A remain required.

Current module::plan_root (1955 onward) handles direct OperatorChain and
BindingStatement; the actual ImplDeclaration takes UnsupportedItem before
nested-member descent. lower_plan (2031 onward) returns HirItem::Error on that
plan before parameter/body construction. Production carrier passes accept only
Binding/Expression (1298–1326); the Error supplies neither. LocalSource::form
(556–583) requires an already supplied Binding/DirectExpression plan and rejects
Unsupported. form_ordinary's later grammar switch cannot retroactively admit
the member. A standalone same-spelled binding or signature is not a substitute.
This is the bounded named-owner cut, not a repository-wide absence claim.

## Remaining evidence, falsifiers and mutual TODOs

- `R123-PARSED-1` / Luna's structural test/source reviewer: establish S/R for
  each exact independent parse. Parser refusal, wrong ancestry/order/annotation,
  absent/[] collapse, formal/body alias or foreign/missing/ambiguous key falsifies
  the proposed instance. Tests of fabricated trees do not establish actual output.
- `R123-R119-SOURCE-1` / Luna's R119 member producer owner: consume only the
  original own-annotation/key input. M's actual member admission, executable
  vectors/body environment, T, A and R85 adoption remain separate. A synthetic
  binding, signature annotation or closed-parent claim falsifies that application.
- `R123-API-1` / source reviewer: verify exact source-only declaration APIs and
  their borrowed original subtrees. Claiming they return executable binder/type/
  target facts without an additional constructor is a falsifier.
- `R123-REVIEW-1` / Luna: fresh compiler/source, spec and regression reviews,
  then only the separately authorized structural test. Producer/coauthor cannot
  certify this result, actual source emission or parent closure.

No code/test edit, method implementation or enlarged dependency is requested.
Preserve ordinary Simple-sub generation/accumulation/propagation, levels,
extrusion, qualifying intrusion, generalization and separate provider/residual/
witness lineages. Next step after freeze is Luna intake and independent review.

## Frozen inputs, authors and resources

All rev3's21 input hashes matched before writes; rev4 adds full_parse.rs, checked
at `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`.
Rev4's22-row immutable manifest fixes every direct source dependency; no unlisted
input was read. Core inputs: R119 proof
`8f5ac5abe7098d384c57f48e2d73b95c01aba4d3aca8c73c43a2a33d29ef4e7d`,
handoff `66843ab0eefe13f067d28414a4a6d59c736dab05d1790a94c03e273e0f3bbd85`;
charter `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`;
shadow.rs `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`;
source_identity.rs `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`.
R119's author is this reused worker; it supplies conditional obligations and
source-owner cuts, not independent review or full parser evidence. Contract/
integration owner Luna; compiler/test/charter byte authors UNKNOWN.

Current-session grant acknowledged before writes. Rev3's missing key owner/
body-emission boundary was reported before writes; outputs stayed unwritten
through the hold. Rev4 pins full_parse and explicitly makes returned-tree shape
the premise; no expression parser was silently read. Same420sec cap: first
clock10:26:39 UTC; Luna charged160sec at10:29:19, leaving at most260sec, without
renewal. Resume clock10:29:34. Preclock and no-write hold remain charged; exact
allocation-start/CPU/memory UNKNOWN. Requested Sol/high, requested concrete
version and observed model/effort UNKNOWN/UNKNOWN. Static listed text/hash reads
only; no tests/build/CLI/probes/formatter/Git, external contact or children.
Only this note and assigned inbox are new; no scratch/generated paths.
Final time/hash receipt is in the handoff. **Freeze rev1 and STOP.**
