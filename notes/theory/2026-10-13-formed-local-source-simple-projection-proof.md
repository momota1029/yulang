# Formed binding LocalSource: equivalence of the simple-body projection

Status: independently reviewed source-derived equivalence and F-success bridge; no new authority,
aggregate inference certification or parent theorem-status promotion
Review update supplied by primary: guarded-form equivalence PASS; new §6.1
composition bridge for cap-lifted formation is an unreviewed delta
Baseline supplied by primary: `593b81ff5d2c9da39a3ba459e3e3f1671049ea3c`
Branch: `research/simple-sub-intrusion`
Exclusive output: this note; leaf only, no delegation
Previous `2026-10-13-flat-local-source-formation-proof.md` stays frozen
Method: inversion of actual successful constructors followed by association
case induction; zero executable probes

## 1. Frozen statement and quantifiers

Fix one actual immutable `ParsedFile` produced by the public parser, one
admitted Binding `RootPlan` from that file, and its actual owner, root parameter
IDs, artifact, namespace, counters, source keys, and next occurrence counter.
Suppose the authentic `local_source::form` for that binding succeeds. Let b be
the exact sole OperatorChain child of that plan's BindingBody. Compare:

```text
Old(b): lower_simple_chain(parsed, b, namespace, counters, occurrence, scope)
Projection(b):
  Atom(a), where a is exactly lib.rs::direct_atom(b), if Some(a);
  Unsupported otherwise.
Consume(Atom(a)): the existing lower_leaf(a, namespace, counters, occurrence, scope)
Consume(Unsupported): SimpleChainLowering::Unsupported { range: range_of(b) }
```

The required conclusion is equality of Old and Consume for the same source and
same consumer state, on completed non-resource-failing runs. It includes the
exact resulting HIR expression, semantic error kind/range, copied-spelling
counter delta and source occurrence-map write. Lifting the replacement through
unchanged `lower_body`/`lower_plan` must preserve ordered errors, diagnostics,
root/parameter/ordinary/source occurrence IDs, scopes, namespace resolution,
and output ranges for every previously successful input in this domain.

Derive, rather than assume, that every syntax subtree reachable by the old
association is free of the four dynamic OperatorUse node kinds and supplies no
reachable StructuralInvariant/ExactOperatorEnvironment error. The claim does
not quantify over manually forged CSTs with parser kinds placed arbitrarily.
It preserves ordinary supported syntax and all existing binders. Closed
annotations include the currently accepted row variables, concrete effect
names, type variables, int, unit/groups and arrow forms; no annotation rule or
effect meaning is changed.

Resource failure timing, complete restoration, parser stack safety, and safety
of the whole module are excluded. Root parameter >=128 and annotation depth
128 safeguards stay. DirectExpression roots, default lowering, public
association, shadow-application behavior, unformed roots, complete Call,
inference, generalization, primitive semantics and F5 remain outside this
replacement. No production file is edited here.

This note gives a derivation from actual formation and parser owners, not a
checker whose input assumes operator absence. Its statement has the real
successful-formation precondition; no independent no-operator hypothesis is
added. It supplies no architecture adoption. The primary owns the Authoritative
2026-09-19 single-association-authority seam. Its subsequent audit, reported with
the §6.1 packet, found no new user approval necessary for the private opt-in
proof-supported optimization. This derivation grants no implementation authority.

## 2. Authentic input and the owning call chain

`ParsedFile` (`full_parse.rs:59–68`) has private source, environment, operator,
green-tree and parse-brand fields. The only production struct construction
found is `parse_file` (`317–342`), which builds the effective operator table and
calls `cursor::parse_root`. `green()` gives an immutable reference; source-node
projections only descend the retained tree. The sole `parsed.green = ...`
assignment found is in that module's `#[cfg(test)]` forged-tree test, not a
public construction path. External callers cannot wrap an arbitrary Rowan
tree into ParsedFile through this API. Clones preserve the same immutable
product. This establishes the stated authentic-input boundary, not a claim
that every parser input is accepted or that internal test forgery is impossible.

The public shadow adapter (`shadow.rs:38–45`) passes its ParsedFile reference
directly to `module::lower_module_with_local_source`. That lowerer creates
source/key inventories and sets only `local_source=true` (`module.rs:911–921`).
`lower_module_with_counters` makes its root from that actual green tree and
plans direct-root children (`923–952`). `plan_root` admits headers and
`lower_plan` creates the owner/root parameters, calls `form`, and subsequently
calls `lower_body` with the same plan (`1270–1319`, `1389–1459`).

The only flag assignments found in HIR production source are the separate
entrypoints `shadow_applications=true` at `module.rs:906` and
`local_source=true` at `919`. `LoweringCounters` is private and otherwise
default-initialized. No exposed combined-flags caller was found. Nevertheless
the replacement must preserve the existing shadow-application branch if a
future internal combined-flags caller exists: a projection can replace only
the simple-chain fallback, after that branch, not its successful result.

The supplied baseline hashes of these owners were frozen before derivation.
No independent branch/HEAD lookup was made because this packet prohibits Git
calls. The hashes, rather than an assumed live branch name, fix the evidence.

## 3. Actual constructor inversion: association-reachable subtrees

Association starts at b, not the root binding header. Its recursive owner
`collect_nested_items` nevertheless traverses nested block headers/types as
well as nested expression bodies. The following cases cover both categories.

### 3.1 Heads and dynamic chain children

`expr_from_nud_normalized` creates OperatorChain
(`expression/operator_chain.rs:123`); its identifier/integer NUD paths invoke
`emit_identifier_core` and `emit_integer_core` (`303–334`). Those helpers
create exactly the IdentifierExpression/IntegerLiteral wrapper and call
`Item::emit_remaining` (`cursor/recovery/emit.rs:205–223`). Item emission
reaches `emit_physical_text`/`emit_fragmented_part`, which emit **tokens only**
(`lexical/item.rs:915–929`, `1014–1046`, `1203–1262`). Thus these leaf nodes have
no child nodes, including no hidden OperatorChain or dynamic operator node.
Comments, whitespace and foreign physical fragments cannot create nested
syntax through these emitters. Foreign fragment splitting can yield multiple
tokens; the proof deliberately retains direct_atom's exact token-count filter.

Parser dynamic operator paths instead emit PrefixOperatorUse,
NullfixOperatorUse, InfixOperatorUse or SuffixOperatorUse nodes through
`emit_operator_use` (`operator_chain.rs:847,878,918,952`; `emit.rs:225–229`).
Successful form processes every scheduled OperatorChain's direct children:
its head must eventually be one of the supported expression cases, or an
IdentifierExpression before the first PathTail; every other tail must be
TypeAnnotationTail, MlArgument, CallTail or ColonApplicationTail
(`local_source.rs:490–633`). A dynamic use as head fails the expression match;
as a tail it fails the explicit tail-kind check. A head preceding PathTail is
explicitly required to be IdentifierExpression. Hence dynamic direct children
cannot survive successful formation.

### 3.2 Every supported expression wrapper

| Actual source shape and owner | Successful form's complete subtree coverage |
| --- | --- |
| Initial operation PathTail (`tails/fixed_access.rs:196–230`) | Its separator/member are parser-emitted tokens. Formation requires precisely ColonColon and Identifier after its trivia filter, plus IdentifierExpression head. No expression child or operator use is omitted. Later PathTails are rejected. Unresolved/Ambiguous/Private operation resolution does not change association. |
| MlArgument (`operator_chain.rs:796–815`) | Parser wraps `expr_from_nud_normalized`; form requires its sole child and schedules it. |
| CallTail (`tails/delimited_tail.rs:33–58`) | Parser's shared delimiter owner emits zero items for an empty call or nested OperatorChains via `expr_from_nud_normalized` (`expression/delimited.rs:128–143,245–260`). Form rejects tuple separators/multiple children; zero children is token-only, otherwise its sole child is scheduled. |
| ColonApplicationTail (`tails/colon.rs:50–103`) | The parser owns inline expression or an indented block. Form requires the sole child to be OperatorChain, rejecting the indented alternative, and schedules it. |
| TypeAnnotationTail (`tails/type_annotation.rs:28–44`) | Parser emits AsKw and a full TypeExpression; form parses the complete annotation using the closed grammar in §3.3. |
| ParenthesizedExpression (`expression/delimited.rs:57–75`) | Parser emits parentheses and shared delimiter items. Form rejects separators/multiple children; empty is token-only, otherwise the sole child is scheduled. |
| BracedStatementBlockExpression (`statement.rs:574–602`) | Parser emits braces and canonical Statement wrappers (`statement.rs:157–172`), separated by token-only BlockStatementSeparator (`1131–1149`). Form validates every wrapper/separator, requires final OperatorChain, and schedules every earlier BindingStatement and final expression. |

For expression children, apply finite proper-subtree induction. Successful
formation visits their supported chain/head/wrapper cases and rejects all
unsupported source alternatives. The work scheduler's exact-once descendant
derivation is in the separately frozen earlier note; the relevant transitions
are also directly visible in `local_source.rs:563–575,632,687–693,819–829`.

### 3.3 Nested private binding headers and closed types

`binding_statement_normalized` creates BindingStatement, BindingHeader and
BindingBody (`declaration/binding.rs:197–259`). An inline body is produced by
`expr_from_nud_normalized` (`392–404,423ff`). Successful local formation's
`body` requires the header/body pair and MyKw, Pattern, Equals header sequence
(`local_source.rs:224–255`), retains Private visibility, checks each header
through `plain_binding_header`, and schedules the sole body chain.

`plain_binding_header` (`module.rs:2171–2274`) admits only an IdentifierPattern
head, PatternMlApplicationTail parameters, and optional PatternTypeAnnotation
in local-source mode. A parameter is a sole IdentifierPattern or the exact
ParenthesizedPattern → Pattern → IdentifierPattern + PatternTypeAnnotation
shape. `identifier_pattern_name` requires the sole Identifier token.
IdentifierPattern parser emission is token-only (`pattern/mod.rs:662–665,
737ff`), application tails wrap Pattern (`1108–1129`), and annotations invoke
the type parser (`1082–1097,1294–1341`). ParenthesizedPattern's delimiter owner
is explicit (`pattern/delimited.rs:43–49,67ff`); any expression/fallback or
other pattern subtree fails the exact admitted-child shapes.

Formation parses **every retained annotation**: expression ascriptions,
local/root binding annotations, and local/root parameter annotations. Inversion
of successful `source_annotation.rs:349–375,399–552` gives only:

- TypeExpression with optional BracketRow and int Identifier token, type-variable
  SigilIdentifier token, ParenthesizedTypeGroup, or head plus TypeArrowTail;
- group with delimiter tokens and zero or one recursively parsed TypeExpression;
- arrow with Arrow token and recursively parsed result TypeExpression;
- row with its delimiter/separator tokens and TypeExpression operands each
  containing one Identifier or SigilIdentifier token.

The syntax type owner emits those atomic types as tokens (`type_expr/mod.rs:
878–895`), group/row wrappers as type-specific nodes (`1795–1815,1608–1626`),
and arrow wrappers with recursively parsed type RHS (`2214–2233,2240–2310`).
Even though other type/parser forms exist, successful annotation parsing
rejects their extra or unsupported elements. These accepted closed shapes
contain no OperatorChain/dynamic-use node. The successful marker parser also
excludes recovery, and the entire root form preflight excludes Missing/Invalid
nodes and Error tokens. No ignored header/type branch can hide a dynamic
association-reachable chain. Root headers themselves are not reached by body
association, but their successful parsing is retained rather than changed.

Together §§3.1–3.3 establish operator absence and well-formed association input
from owning constructors. They do not assume source spelling cannot denote a
dynamic operator: if the parser selected one, its actual OperatorUse node
would fail formation.

## 4. Association cannot fail in this domain

`associate_chain_expression` collects direct child nodes and Error tokens,
calls `ChainParser::expression(None)`, and checks complete cursor consumption
(`lib.rs:211–238`). Recovery is absent and §3 excludes dynamic uses throughout
the recursive traversal. Hence every direct item takes Value classification.
`item_expression` calls `value`, which constructs HirExpr::Value after visiting
nested items (`lib.rs:441–459,505–513`). `collect_nested_items` only descends
ordinary nodes or associates a strict descendant OperatorChain (`515–539`).
Finite subtree induction gives successful nested calls; header/annotation
descent reaches no additional expression chain omitted by §3.

For each chain, the initial item is Value; each remaining supported fixed/ML
tail goes through structural_continuation; TypeAnnotationTail does so because
minimum is None; ColonApplicationTail takes the terminal outer-tail case. The
terminal case's residual loop, if reached, also consumes every residual Value
without a dynamic call. Thus cursor advances to the full children length.
There is no dynamic recursive expression call with nonempty minimum and no
below-minimum early exit. `structural_continuation` receives Value from `value`
and explicitly inserts left before asking for first child (`lib.rs:474–492`),
so its Value-pattern and nonempty-child StructuralInvariant branches cannot
fail. `take` after `peek` cannot be empty. Nodes are actual nodes, not Error
tokens, so `ChainItem::node` cannot fail on this route.

The remaining error source is `definition` (`lib.rs:600–630`), called only
when classification/item handling sees Nullfix/Prefix/Infix/SuffixOperatorUse
or the dynamic operator branches run. Those cases are excluded by the
derived §3 property. There is **no per-chain environment lookup** before this
dispatch. Therefore the exact retained operator table cannot cause
ExactOperatorEnvironment here, and no missing operator-token check is reached.
This does not change or reconstruct that table for any other caller.

## 5. Projection equality and HIR trace

The old seam already computes `direct_atom(b)` before association
(`lib.rs:146–153`). The helper returns Some only when b has exactly one direct
child, that child is IntegerLiteral or IdentifierExpression, and its direct
tokens contain exactly one Integer/Identifier token after the existing filter
(`183–207`). §3.1 makes that sole child token-only. Association of this
single-item chain is consequently `HirExpr::Value { children: [] }`. Thus the
old `atom` and `Value`/empty-children checks both pass and call lower_leaf on
the exact helper-produced atom.

If direct_atom returns None, §4 still gives successful association; old
`lower_simple_chain` immediately returns Unsupported with `range_of(b)`
(`module.rs:2095–2110`). Projection therefore gives exactly the same result.
Groups, empty parentheses, blocks, operation PathTail, ML/call/colon tails and
ascriptions all take this branch at the root, because their head kind or direct
child count fails direct_atom. Nested supported forms affect association work,
but cannot turn the root into a direct atom. A token-fragmented sole leaf
failing the helper's token-count criterion is also Unsupported in both routes.
Do not substitute LocalSource's text or form for this exact helper.

`associate_chain_owned`/association perform no HIR occurrence minting,
namespace resolution, source-identity writes, error emission or spelling-counter
updates. The helper's atom is the same kind, spelling, token range and source
node. Reusing `lower_leaf` preserves its exact source occurrence write,
copied-spelling delta, integer output, root-parameter-first lookup, complete
namespace lookup, and UnresolvedName/AmbiguousName semantic error
(`module.rs:2116–2168`). Association's temporary HirExpr is never published by
the old simple route; skipping its construction changes no successful HIR data.

Keep missing-body, indented-body, recovery, child-count and chain-kind validation
in their original order in `lower_body` (`1564–1640`). Consume the carried
projection only at the existing simple fallback after any shadow-application
branch. The same Unsupported range drives the same one outer lowering error;
nested names remain undiscovered by this semantic route. The same lower_leaf
result drives the same later `lower_plan` error/diagnostic handling. Formation,
carrier insertion, ordinary Lambda/body occurrence allocation, scope push and
restore stay ordered exactly as before. The private projection itself mints
no identity and emits no counter/map/error writes. Therefore replacing that
fallback preserves the complete old successful HIR trace, including identities
allocated before and after it.

## 6. Exact typed handoff and remaining scope

The proposed internal `SimpleBodyProjection = Atom(OwnedAtom) | Unsupported`
must be produced together with a **successful formed binding result**, using
the existing direct_atom on that binding's actual body chain. It is not a
public atom constructor or a flag-derived promise. Carry it through
Binding `lower_plan` into `lower_body`; only successful form can supply it.
Do not re-infer it from the emitted carrier's node.text, form or name
resolution. Consumer validation still chooses the actual body chain before
using the phase result; the packet is tied to the same immutable plan/body.

DirectExpression is dispatched before Binding form (`module.rs:1361–1386`)
and can occur even when local_source=true. Its `lower_direct_root_expression`
must retain the old association route. Default/public association, source-only
identity mode, shadow-application mode and unformed roots likewise retain the
old route. This is why blanket dispatch on `counters.local_source` is invalid.
Future combined flags must retain shadow success and use the phase result
only in the simple fallback. No code establishing this typed seam exists yet.

Projection needs no new recursive tree traversal or HirExpr allocation. Reuse
the root chain already selected for work scheduling. direct_atom examines at
most two direct child nodes before its leaf test; for a sole candidate leaf
it scans direct tokens and copies the selected spelling exactly once, as the
old seam did. Non-atom composite roots stop after the child/head check. This
removes the old otherwise-discarded recursive association/ownership work for
formed binding simple fallback. It does not remove formation/source-key/header/
annotation scans or prove whole-module/parser safety. In particular the
DirectExpression route remains separately recursive. Existing infallible
allocation behavior and changed allocation-failure timing are not certified.

No source-qualified counterroute to this projection equality was found in the
inspected constructor cone. The original internal depth-erasure result remains
separate. Section 6.1 supplies its necessary larger-input composition premise;
the downstream implementation blocker still requires independent delta review,
the exact authorized implementation, and primary-owned focused verification.

### 6.1 Composition with the exact cap-lifted formation F

This is the necessary additional source/implementation bridge for the earlier
internal scheduling result, not another theorem with an assumed no-operator
precondition. Freeze F exactly as defined in that note §1: erase the expression
depth fields/arguments and these three refusals in local_source.rs:
`depth > 128`, `depth + tails.len() > 128`, and
`depth + parameters.len() + 1 > 128`; optionally remove only block's redundant
`has_recovery(&statement)` disjunct. Preserve lexical Restore/Publish guards,
root parameter cap, annotation depth preflight, all syntax/private-visibility
checks, source/identity checks, parameter ownership, and descendant schedules.

For every authentic ParsedFile P and actual admitted Binding plan r from P,
including every larger finite source not admitted by the old expression cap,
assume F succeeds for r with its actual parameters/namespace/identity state.
Let b again be r's actual sole BindingBody OperatorChain. The conclusion is:

1. All association-reachable subtrees of b satisfy the operator-absence and
   association structural-totality properties established in §§3–4.
2. Projection(b) equals the simple-body result of associating that same b and
   applying the old atom/empty-Value tests, in the finite mathematical execution
   without resource failure. Executing Projection requires no such association.
3. Consuming that exact projection at the binding's validated simple fallback
   avoids recursive HirExpr association/construction/destruction for every
   F-success binding, including these larger inputs. Its projected ordinary
   body is exactly existing lower_leaf(Atom) or Unsupported at range_of(b).

Proof of (1): successful F leaves every retained constructor check satisfied.
None of the inversion premises in §3 is one of the deleted depth tests.
Specifically, identifier/integer heads remain authentic token-only parser
outputs; dynamic heads/tails still fail the supported kind checks; an initial
PathTail still requires the exact token/member and identifier-head shape;
ML/call/colon/group children are still selected and scheduled by the same
sole-child checks; every block Statement/separator/header/body still satisfies
the same structural and Private conditions; every ascription and root/local
annotation still passes the same complete closed-type parse and depth-128
preflight. Allowing more local parameters changes how many accepted header
parameter cases occur, not their grammar, owner or annotation checks.

The root recovery check remains before construction. The earlier note §§3/6
proves every scheduled statement is a descendant of that root and the root
predicate excludes the same recovery kinds throughout it. Thus optional removal
of the statement scan loses no recovery premise, including at greater depth.
The identity checks and lexical guards remain; they neither insert foreign
syntax nor reconstruct a body from names. The prior scheduling derivation
supplies finite proper descent, exhaustive scheduled-child processing, and
single-write retained slots for F success. Its argument does not impose an
expression-height bound. Subtree induction in §3 therefore applies at every
finite height, using the unchanged grammar facts above. This derives operator
absence for authentic F success directly; it does not transfer it by claiming
the old capped form also succeeded.

Proof of (2): §4's case induction uses only finite proper descent, nonempty
supported chains, recovery/operator exclusion, minimum=None, cursor movement,
and the actual association branches. It never compares a numeric depth.
Exact-operator-environment lookup remains exclusively behind the excluded
dynamic cases. §5's atom split uses only the actual root chain's direct child
count/kind and direct_atom's token filter; token-only leaves ensure the
corresponding old Value has empty children. The original 128 expression
refusals supply none of these premises. Hence §§4–5 instantiate for F success
at larger finite depths and widths. Structural totality here does not assert
that executing recursive association on such inputs fits a host stack; that
is precisely the construction avoided in (3).

Proof of (3) and exact implementation obligations: the implementation must
compute and emit the phase result only with successful F formation, after all
formation/completion/root-annotation checks. If it introduces a private
`RootBodyPlan`, that plan must be parser-derived from r's actual body b already
selected for formation. Its construction must be confined to that successful
binding-form result, retaining b's provenance and existing direct_atom output;
no public constructor, arbitrary Rowan input, carrier-text reconstruction,
scope reconstruction or flag-derived validity is permitted. Failed formation
must emit no usable RootBodyPlan/projection. The private product is carried
through the same Binding lower_plan to lower_body, not rediscovered from a
global local_source switch or a LocalSource arena shape.

Preserve old body validation and shadow-application dispatch; consume the plan
only at that same binding's simple fallback. Atom delegates to lower_leaf with
the unchanged namespace, scope, counters and ordinary body occurrence;
Unsupported uses range_of(b) and the unchanged outer-error handling. Neither
branch invokes associate_chain_owned or builds an associated HirExpr.
direct_atom examines only direct root children and leaf tokens; it does not
recursively traverse the larger group/block/tail subtree. No discarded recursive
association tree is therefore constructed or dropped at this seam. Formation's
flat expression storage, checked identities and retained bounded annotation
storage are accounted for by the earlier internal theorem; ordinary root
parameter Lambda construction remains bounded by the retained root cap.

There are two different observable claims. For inputs on which the original
capped opt-in entrypoint completed successfully, the earlier scheduling
projection and §5 yield exact successful trace preservation. For additional
F-success inputs formerly refused by a deleted cap, the original entrypoint
returned StructuralProjection and had no successful HIR trace to preserve.
The new route instead has the precisely defined projected ordinary-body result
above and the complete F-formed source carrier. This composition neither
equates that new success with the old refusal nor copies a failed attempt's
partial identities. Resource/identity checks can still stop the private attempt.

This supplies the missing mathematical bridge for eliminating the formed
Binding downstream association seam **once the exact phase result is actually
consumed as specified**. It does not establish that consumption in unmodified
compiler code. Fresh independent delta review and source-to-implementation
checking remain required. DirectExpression/public/default/unformed routes,
parser construction, solver/inference/Call/F5 and allocation/resource gates
remain separate; no whole-module or arbitrary-depth parser safety follows.

## 7. Frozen hashes, checks and commit packet

SHA-256 at initial read and rechecked before handoff; compiler/parser/semantic
dependencies are unchanged:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/lib.rs` | `51e5fa543cd65ced879a7561e0d602e686a072378cde5ec16a20b4afb875fc0a` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/cursor/recovery/emit.rs` | `2570ef138c22c68ce4275e7612d9901a20316c43c1726691baa151e05e92f168` |
| `crates/yu-syntax/src/lexical/item.rs` | `b6bbeefe6ef5c21e46c34cf97aed96b19703e6b55a1869f6396bc0458f06416b` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` |
| `crates/yu-syntax/src/expression/delimited.rs` | `2d6f43b2b02a560d7ad1aa76929969908df34fe6d884783b34baa9edc5f81b08` |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs` | `9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd` |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs` | `349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf` |
| `crates/yu-syntax/src/expression/tails/colon.rs` | `df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982` |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs` | `edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a` |
| `crates/yu-syntax/src/statement.rs` | `dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03` |
| `crates/yu-syntax/src/pattern/delimited.rs` | `4c13f29d73981071381e4371afca4e73bbeb847e4d44abc77bd36ba4949a82b6` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| 2026-09-19 simple-module-resolution design | `494a6973ced88a031688213990ea380e64cb74fea3bb1396236a8d1bb911f11a` |
| 2026-09-19 associated-chains ownership amendment | `e78d2d9865e35828e38c353ee77c359850d8be1884828f75aa931be2bf1556f3` |
| 2026-10-11 top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Prior scheduling proof, initial producer freeze | `e7824bd3bdf3fb224f8655eabab2d6ba74ced96dff9ba40de0f2860b9d805cd9` |
| Prior scheduling proof, final current metadata/review version | `8c7b87d373b172d2a61672a5244e02bdae71ea3b71df511e0f99302533a771bb` |

During this packet the primary reported HEAD advancement/push to
`06eb3e80c7dd8032b6d9ef39b357714dc43da536`, changing only the prior note's
header/review appendix and shared task records. Its independent review PASS
and pending-projection metadata are primary-reported evidence, not this
producer's certification. The prior derivation premises and all compiler,
parser and governing semantic hashes remained unchanged. This packet retains
its assigned 593b81 baseline and records the changed prior-note dependency
hash explicitly; it does not modify that previous lease.

Checks: bounded static `cat`, `sed -n`, `rg -n`, `rg --files` searches/reads and
SHA-256 comparisons; one leased-note write. Relevant core formation/annotation
files were read in full in the preceding stable-hash packet; this packet reads
the actual association, consumer, public ParsedFile and exact accepted parser
constructor ranges above. One guessed `expression/braced.rs` locator was absent;
the actual owner `statement.rs` was located and inspected. No Git calls,
builds, tests, probes, measurements or delegation. One static leaf under the
15-minute budget; zero heavy processes and zero measured samples. Configured
normal requested routing is Sol/high; observed effective runtime settings are
unknown. No Astra assignment.

The primary reported independent compiler_referee PASS for the guarded-form
derivation, with the explicit missing F-success composition premise. Section
6.1 is the newly supplied delta and remains unreviewed. It does not reinterpret
that bounded PASS as coverage of F. The primary also reported that the authority
audit requires no new user approval for this private optimization. No shared
gate/status file was changed and no implementation permission is inferred.

Delta checks/resource use: static reread and hash comparison of the four HIR
owners and both proof notes; exact depth-independent premise audit above;
leased-note edits only, at most eight minutes, no tests/builds/probes,
measurements/Git calls/delegation. Compiler/parser/semantic dependency hashes
remain as listed. Prior proof hash remains `8c7b87d...`; the initial projection
artifact hash before this delta was
`f52c24755ec0014b2fd325bcba4c0d1b908f9d123790ac1966dcbf02fb2ca75c`.

Next action: primary obtains fresh independent delta review of §6.1's necessary
F-success bridge before an implementation packet for the exact typed seam.

Commit packet: sole path
`notes/theory/2026-10-13-formed-local-source-simple-projection-proof.md`;
baseline `593b81ff5d2c9da39a3ba459e3e3f1671049ea3c`; dependency hashes above;
status guarded-form equivalence PASS as reported by primary, F-success
composition delta unreviewed, not production conformance;
static checks only; proposed message
`research: bridge cap-lifted formation to simple body projection`.
Shared-record delta for primary/curator: record the guarded-form review and
pending independent F-success delta review; preserve the prior source-depth
implementation gate and all
ordinary/public/direct-expression/Call/inference/F5 exclusions until integrated.

## 8. Primary review and implementation correspondence

The guarded-input projection derivation passed a fresh independent
`compiler_referee` review. A separate fresh delta review passed §6.1's
larger F-success bridge at producer SHA-256
`f8b9ca2553d95cda8299f1e491a7a4f24f1de58f0ea2bdc8a157fc4997ede373`,
with no remaining findings. An independent conformance audit confirmed that
this proved private opt-in specialization requires no new architecture
approval; ordinary carrier migration and the first-slice public association
remain within their separate authority scopes.

The primary then assigned the exact two-file implementation. Fresh independent
semantic and static performance reviews passed the frozen code, with no
findings. The actual code emits the phase result after complete formation and
root annotation, carries it only through the same Binding, and consumes it
after existing body validation and shadow dispatch. The depth erasure and
recovery-scan removal match the internal scheduling proof. The retained root
parameter and annotation safeguards, public/default/direct-root routes,
identities and ordinary error/leaf consumers remain as specified.

The [integration record](../progress/2026-10-13-flat-local-source-projection-integration.md)
contains current code hashes and exact compile checks. The source hashes in
§7 are the pre-implementation proof baseline, not a claim that the implemented
owners still have those bytes. This source-to-code correspondence does not
certify runtime small-stack behavior, whole-module/parser resource safety,
solver semantics, complete Call, general L4, principality or F5 cutover.
