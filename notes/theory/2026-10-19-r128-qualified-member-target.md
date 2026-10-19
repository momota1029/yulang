# R128: qualified head, ordinary Apply edges, and the first candidate gate

Status: candidate finite source correspondence, with explicit parse/availability
premises; independent review pending. Assignment `R128-PROOF`, revision 1.
Author and sole writer: `/root/r128_proof`; no descendants or coauthors.
Session: `current-conversation-2026-10-19-r128-resume`. Luna's live exact grant
supersedes the stale startup snapshot's producer-unassigned scheduling text;
it changes no semantic authority. Requested model/effort: Sol/high
(`gpt-6.1-sol`/high); observed model/effort: UNKNOWN/UNKNOWN.

Frozen contract: `qualified-member-target-20261019-r128-rev3`, SHA-256
`0b7a1e2b625a1d95d62cbf63e19ef5c51d6ea1427baffc6b1820ed02b82a5273`.
Baseline/origin supplied by Luna:
`8bad5d05f17b433b2c5164b91248462de3f7a6fe` (no Git inspection performed).

## Parent and actual result

The parent is R119 P1/P3's `R119-TARGET-JOIN-1`: approved unique target
evidence must connect the original role-qualified member occurrence to the
authentic ordinary executable member owner, preserving its two source-owned
ordinary Apply edges. Its original source domain and quantifiers remain intact.
R119's M (authentic member producer), T (target join), and A (complete
candidate/runtime admission) are independent. This note addresses T evidence.

For the exact 148-byte fixture below, the inspected LocalSource constructor
retains the two ordinary edges in the shape
`Apply(Apply(Operation(Unresolved), Integer(1)), Integer(2))`, provided the
actual returned source tree has the stated shape and formation succeeds.
Its qualified head is resolved exclusively through Act effect/operation
namespaces. No Role/Impl executable member identity is produced by that route.
For the unchanged whole module, the earlier Role/Impl `HirItem::Error` blocks
`solve_mode` before the `answer` preflight call. The head-specific preflight
rejection is consequently a conditional source-code fact, not an observed
solver failure for this source. No solver or runtime was executed.

This is a finite owner/data-flow argument, not a reviewed theorem, method
dispatch implementation, native execution result, or production authority.

## Exact source and original keys

The source is the contract's unchanged LF text, without a final LF; supplied
SHA-256 `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Let P be the returned ParsedFile for these exact bytes. **S** means its actual
diagnostic-free tree contains the original declarations and final binding with
the head/tails described here; **H** means the selected pinned HIR constructor
successfully returns its authentic artifact, with the source identity and
LocalSource formation enabled as below. These premises are not silently inferred
from local parser rules. No parse, HIR construction, or test was run by this
author. The pinned existing `exact_role_impl_member_source_reaches_original_occurrences`
test specifies original Role `0..51`, Impl `52..114`, and member `78..112`
and their authentic ancestry; its presence is a test contract, not this lane's
execution evidence. R119/R123 do not prove unrestricted whole-parser correctness.

For each actual node n in P define K(n) by descending
`P.source_root().children()` and calling `key()`. In
`full_parse.rs:69–138`, the key retains P's parse brand, the actual green node
allocation and its start. Equality requires all three. Thus these are original
same-parse keys, not invented numeric IDs, spelling identities, or foreign
reparse keys. `source_identity::{source_keys,try_source_keys}` walks those actual
children and records `(SyntaxNode,K(n))` (`source_identity.rs:26–49`). Induction
on tree descent gives the authentic key for every head, tail and argument below.
The key constructor does not itself prove S.

Within S, name the final body chain C, its family IdentifierExpression F,
its PathTail Q, its first and second MlArgument tails U/V, and their child
OperatorChains E1/E2. Their meaningful spellings are `SecondInt`, `::second`,
`1`, and `2`. Authentic node keys and actual node ranges govern the proof;
whitespace ownership belongs to the parser constructors. No manually guessed
coordinate is used as a node identity.

`operator_chain.rs::expr_from_nud_normalized` starts OperatorChain at line 123.
Its PathSeparator branch (688 onward) calls
`fixed_access.rs::path_tail_normalized`, which starts PathTail, emits the
separator and original segment, closes that node, then resumes tail scanning.
For this spelling the segment is the Identifier `second`; the separator becomes
ColonColon in the retained CST. These local constructors explain Q, without
equating a role signature occurrence with the qualified occurrence.

`is_ml_argument` (761 onward) requires a nud item with leading grammar space
and enabled ML mode. `ml_argument` (785 onward) emits that leading trivia,
starts MlArgument and parses one child with `MlMode::None`, then resumes the
outer chain with `MlMode::All`. Consequently `1` and `2` form two separate
outer tails U/V in source order, not one nested argument swallowing the other.
The pinned delimited-tail owner constructs CallTail for parenthesized calls;
this fixture's two space applications use MlArgument, not that route.

## LocalSource construction and provenance

In `module.rs:1141–1151`, the opt-in local-source constructor initializes
the identity/key maps and sets `counters.local_source = true`. For an admitted
binding, `lower_plan` allocates its DefinitionRootId and calls
`local_source::form` at 2094 onward, storing the resulting carrier under that
actual root. Ordinary `lower_module` instead enables ordinary source carriers;
the first pass at 1298 onward forms a carrier for each actual Binding through
`form_ordinary`. These are separate constructor configurations. An ordinary
configuration need not populate Act namespaces; the opt-in one calls
`source_annotation::declarations` before planning root items (1175 onward).
Neither configuration fabricates an admitted root for the nested Impl member.

The final simple binding `answer` is a direct-root BindingStatement. Its
admitted header has no formal parameters; `form` schedules its actual body C
with its own Definition owner (`local_source.rs:557–644`). In
`Builder::expression` (848–979), let the initially allocated result slot be v.
The first tail is separated from the ordinary tail list iff it is PathTail;
therefore Q is consumed as the qualified head, leaving `[U,V]`.

The reverse-tail loop has the following exact two steps:

| Step | Slot written and source key | Form and retained operands |
| --- | --- | --- |
| V first | v at K(V) | `Apply { callee: u, argument: a2, source_form: MlArgument }`; schedules E2 at a2 |
| U second | u at K(U) | `Apply { callee: h, argument: a1, source_form: MlArgument }`; schedules E1 at a1 |
| Qualified head | h at K(Q) | `Operation { resolution: resolve_operation("SecondInt","second") }` |

Each callee and argument is allocated separately by `slot()`. Each tail's
`only_child` selects its own E1/E2; neither child is swapped, flattened or
replaced by a role-signature endpoint. The LIFO work schedule changes when
children are filled, not the already recorded operand pointers. The integer
leaf constructors fill a1/a2 from their original source nodes. This proves the
two-edge constructor consequence under S/H; it does not infer receiver meaning
or adopt R85's receiver-first method proposal.

`Builder::set` (819–846) obtains the source through the original key map,
records the occurrence/source mapping, and retains that key, actual node range,
scope, named group and form in the expression slot. Thus the outer edge owns
K(V), inner edge K(U), operation head K(Q), and leaves their original keys.
`form_ordinary` (503–553) stages identity, orders occurrences and appends the
stage on success. Index/occurrence allocation order is not source semantic
identity. A foreign parser's same-spelled key cannot substitute for K(Q).

## Operation namespace and declaration identity

`source_annotation::declarations` (145 onward) filters the actual root children
to **ActDeclaration only**. Role/Impl are filtered out of that declaration
namespace; they are not converted to effects. It registers each accepted Act
family as `SourceEffectId { module, declaration: K(act) }`. It subsequently
reads signature-only BindingStatements from that Act's body (224–324): no
BindingBody and no parameters are accepted there. It constructs an
`Arc<SourceOperationDeclaration>` whose identity is
`SourceOperationId { family: that SourceEffectId, declaration: K(member) }`,
retaining its own name/signature positions, visibility and parsed signature.
The namespace key is `(family_id, member_spelling)`.

`Builder::resolve_operation` (1091–1102) first looks up the family spelling;
no family yields Unresolved, non-singleton yields Ambiguous. For a unique
family it looks up the member, similarly requiring uniqueness and non-Private
visibility before returning that exact declaration Arc. The output kind is
SourceOperationResolution, not ModuleDef, DefinitionRootId, selected Impl ID,
executable member ID, or target certificate. It never consults a role lookup
or the ordinary definition namespace.

There is no ActDeclaration in S for the unchanged role/impl fixture. The
default counters begin with empty namespaces and `declarations` adds no
family; therefore `resolve_operation("SecondInt","second")` is Unresolved.
This is not the Private branch despite the role signature's `my`: that
signature was never entered into the Act operation namespace.

The independent control `act SecondInt: / our second: int -> int -> int`
can populate an Act family/member with those distinct source keys, and then
resolve its qualified head through the normal Operation route under its own
parse/formation premises. It has no executable member body or role selection.
No opaque identity across P and the separate control is compared. That control
cannot supply a missing identity for P or falsify the T obstruction.

## Exact solver caller: first unmet condition

`shadow_apply.rs::solve_mode` (385–423) first collects only registered source
effect declaration placeholder error IDs. Its item traversal proceeds in HIR
source order. A HirItem::Error is skipped only when its errors are nonempty
and **all** belong to that registered declaration-error set.

For each remaining item the caller can invoke `candidate_source::preflight`
only with both an expression and an authentic owner:

1. Binding supplies `binding.value()` and
   `SourceRootId::Definition(binding.definition_root().clone())`.
2. Expression supplies itself and an actual owned expression root obtained
   from `hir.expression_root(expression.occurrence())`; errors map to
   Unsupported and missing roots do not create an owner.
3. `hir.local_source_for(&owner)` must return `Ok(Some(source))`. Ownership
   is checked by `source_carrier_for`; Supported carriers yield that source,
   Unsupported carriers yield None, and absent carriers fall back only to
   the definition's authentic opt-in `local_sources` map (`module.rs:968–988`).

If those conditions were reached for the actual `answer` Binding under H,
its Definition owner would obtain its actual retained carrier and call
preflight. Retaining the carrier during HIR construction alone does not mean
that item is reached during this loop.

For S/H the first root child Role, and next Impl, are neither OperatorChain
nor BindingStatement. `plan_root` (1955–1982) constructs
`Unsupported(UnsupportedItem)`, and `lower_plan` (2031–2068) emits an
`HirItem::Error` with its actual direct-root error. The module loop constructs
all items and retains later binding carriers; it does not remove these error
items. No Act declarations exist to register their errors as placeholders.
At the first such Role item the early skip fails, the expression/owner pair
is `(None,None)`, and the fallback match returns Unsupported. The earliest
unmet caller condition is an admissible/skippable first item. Impl would
produce the same obstruction if encountered, but is already later. The
`answer` LocalSource lookup, its preflight and whole-module `hir.errors()`
gate are not reached on this code path. This is a deduction from the pinned
constructors under S/H, not a recorded execution failure. No claim about an
uninspected upstream adapter filtering declarations is needed.

Conditionally, if `candidate_source::preflight` were invoked on this retained
carrier, its Operation branch (478–483) accepts only Resolved(declaration)
whose signature has no outer effects, is Function-valued, and passes annotation
preflight. Unresolved reaches its Unsupported arm. This conditional is
independent of the earlier item rejection, and is not reported as running.
Later emission (1201–1219) consumes that same operation declaration Arc,
prepares its signature, emits empty immediate-effect facts and creates
`Action::Operation { declaration, owner, occurrence, target, level }`;
the action consumer at 1692 calls `candidate_operation`. An unresolved
operation is invalid there. None of these consumers selects an Impl member.

The whole-module `hir.errors()` check at 415–420 is later than the item loop.
It permits only specifically retained UnsupportedExpression errors and
registered effect-declaration UnsupportedItem placeholders. It is an
independent complete-admission gate, not the first failure assigned here.
Collection, session solving, runtime publication and native evaluation are
still later and unobserved. Candidate_context's replay-operation vocabulary
is not a source Role/Impl target producer; no identity is inferred from its
use of the word operation.

## Application, reused work, missing premise and falsifier

Apply this result directly to `R119-TARGET-JOIN-1`: the existing qualified-head
constructor preserves ordinary operand structure but supplies
Operation(Unresolved), so it supplies no approved unique join to the authentic
ordinary executable member. Merely fixing argument association or pointing at
the same-spelled Act control cannot discharge T. M's authentic member
owner/vector/own-annotation/body producer and A's complete admission remain
independent prerequisites; bypassing the earlier error does not establish
either or create the missing semantic join.

R119's reviewed closeout and conditional downstream Apply preservation are
reused within their M/T/A premises. R123's original-key and own-annotation
distinctions are reused within its S/R premises. Neither provides actual
method-target emission. Their conditional binder result is not upgraded to
source/native execution. Charter §§21/24 distinguish own parameter entry and
receiver role; neither grants method lookup, dispatch, operand meaning or R85
adoption. R85 remains Draft/unadopted as recorded in the pinned R119 authority
receipt; the unpinned R85 text is not reopened here.

Stable mutual TODO `R119-TARGET-JOIN-1`, owned by Luna and a future approved
role-target/ordinary-admission source owner: after semantic adoption, establish
the unique original-qualified-occurrence → selected original Impl member →
authentic executable root correspondence, using the same-parse source keys
and both retained edges. First missing code fact is a target producer/validator
in `module::plan_root/lower_plan`, `local_source::Builder::expression` and
its target consumer. Minimal future implementation TODO is provisional or
approved only by a separate grant; no production edit is authorized here.
Falsifier: an existing authenticated route in the frozen owners producing
that ordinary executable target for this unchanged source. Wrong source key,
operand loss/reordering, foreign identity, or attributing failure to an
unreached gate also falsifies this finite account.

Stable source observation TODO `R128-SOURCE-OBSERVATION-1`, Luna's separately
leased implementation lane: inspect the actual unchanged fixture's answer
carrier, original operation/tail/argument keys and both operands; independently
parse the Act control. Its focused structural test may discharge that finite
S/H observation, subject to review and the contract's gated execution. It does
not execute `solve_mode` or establish A. Parser recovery, unavailable original
carrier, changed provenance/order or a different resolution is its falsifier.

R119 M/T/A, R85 adoption, all six distinct effect-hygiene parents, and original
Simple-sub/evaluator A/B remain OPEN. Generation, accumulation, propagation,
levels, extrusion, qualifying intrusion and generalization are untouched.
No F1/FK1 independent continuation quantifier is restricted or proved by this
finite source example. No withdrawn bypass, provider/witness/residual collapse,
or weaker ordinary inference is proposed.

## Frozen dependencies, checks and stop

All 20 contract input SHA-256 pins and the contract hash matched during the
read-only hash inventory at 2026-10-19T11:53:53 UTC. The frozen contract table
is the complete direct-dependency hash manifest; no new semantic/source input
was added. Historical proof authors: R119 and R123 `/root/r118_proof_lane`;
R119 closeout and contract owner Luna. Code author identities are not established
by these reads and remain UNKNOWN. Current candidate author is `/root/r128_proof`.

Checks: constructor/source reads and SHA-256 inventory only. No compiler,
tests, build, CLI, probe, formatter, Git, external contact or descendants.
No production/test/central records changed. Start acknowledgement is the
current-session live parent grant plus this worker's active receipt; exact
launch timestamp and CPU/memory observations are UNKNOWN. Cap 480 seconds;
charge the full allocation conservatively without resetting or borrowing.
Review is NOT_RUN by this author, who is ineligible to independently certify
the combined result.

Only new paths are this note and
`tasks/agent-loop/inbox/20261019-r128-proof.md`; no scratch paths were created.
The artifact hash is recorded in the one frozen handoff, avoiding a self-hash.
Stop condition reached: finite trace and precise first gate accounted for;
further work requires Luna's review/intake or separately authorized evidence.
Worker STOPPED after the handoff hash receipt, all writes stopped; no descendant
leases exist. This is a candidate milestone pending independent review and
integration, with no parent closure claim.
