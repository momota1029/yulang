# R106 exact method/role source entry and executable binder boundary

Status: **candidate source correspondence argument, awaiting the finite source
observation and fresh independent review**. Assignment `R106-PROOF`, revision 1.
Sole author: `/root/r106_proof`; no coauthors or descendants. Sprint contract:
`tasks/agent-loop/sprints/method-role-source-entry-20261019-r106-rev1.md`,
SHA-256 `edd6c951b46b3f1993c57b5f5cdec4928652cfb313120bd60d9e64c6ebc922bf`.

## Parent and application

The unchanged parent is R100's R85 P2/P3/P4 obligation, restated in the frozen
R100 proof note's “Parent application and exact limit.” P2 requires the selected
authentic member's original executable binders, annotations, body and lexical
environment. P3 requires that member in receiver-first ordinary
`Apply(Apply(C_member,E_receiver),E_argument)`, retaining whole operands and
caller provenance. P4 requires complete candidate/root/target metadata and
ordinary constraints before publication. The R85 semantic proposal is Draft
and unadopted. No semantic authority follows from this note.

R100 established a reviewed bounded consumer cut, conditional on the exact
source publishing direct RoleDeclaration/ImplDeclaration roots. Its outstanding
`R100-ENTRY` premise can be reduced to a finite actual-source observation for
the unchanged fixture. A passing reviewed R106 test can supply that observation
without proving static completeness of the whole parser or inspecting a new
dispatcher owner. The HIR case split uses the actual published root kinds;
it does not require reconstructing the internal dispatcher call trace.

This producer has inspected the frozen pre-edit inputs only. **No R106 test
execution or post-edit source output was observed by this producer.** The
observation is pending, owned by Luna's sole authorized command after fresh
CLEAN post-output reviews. The implication below is the present result;
Luna's immutable command/implementation receipts are required before recording
its antecedent as observed. This is a finite evidence handoff applied to the
parent, not a new conditional replacement for P2/P3/P4.

## Exact finite observation

Let S be exactly the contract's 148 ASCII bytes, with LF between lines and no
final LF, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The required observation E is a successful execution of the reviewed test
`exact_role_impl_member_source_reaches_original_occurrences`, using one actual
ParsedFile P and one retained ShadowArtifact A from P. E must establish the
exact RoleDeclaration/ImplDeclaration direct roots and their associated
original source nodes; locate the nested implementation BindingStatement;
and check its head `second`, ordered `self` and formal `selected` pattern
occurrences, plus the distinct body IdentifierExpression `selected`. Each
checked node key must come from P, round-trip to its retained position in A,
and preserve kind, range, spelling, parent and child order where exposed by
the public APIs. Source equality must use S. A second parse of equal text
cannot supply any checked identity.

E establishes output reachability and retained source identity for this exact
source/environment. It is not a universal parser theorem, a static proof that
every source invokes a named constructor, or an execution observation of an
implementation member. No guessed SourceNodeKey or numeric PositionId is
part of the claim. A successful association alone cannot establish lexical
binder resolution or the body's result type.

The following expected facts are **R100 constructor-derived facts**, not newly
observed output. E must validate their relevant occurrences against P and A:

| Occurrence | Expected source range | Required owner distinction |
| --- | --- | --- |
| member BindingStatement / BindingHeader | `78..112` / `78..103` | nested Statement / header child |
| target Pattern / head IdentifierPattern `second` | `81..101` / `81..87` | header target / first pattern head |
| first PatternMlApplicationTail / Pattern / IdentifierPattern `self` | each `88..92` | first target tail and its children |
| second PatternMlApplicationTail / Pattern / IdentifierPattern `selected` | each `93..101` | second target tail and its children |
| Equals | `102..103` | header token after target |
| BindingBody / OperatorChain | `103..112` / `104..112` | member body / body chain |
| body IdentifierExpression / Identifier `selected` | each `104..112` | chain child / expression token |

The role signature's `second` (`24..30`) and qualified call's `second`
(`138..144`) are different source occurrences. The body `selected` is not the
formal IdentifierPattern at `93..101`, even though their spellings agree.
Node-only child order is not a raw child ordinal: trivia remains in A.

## Why the observation joins the reviewed source cut

The following are source inspection results at the frozen input hashes:

1. `full_parse.rs:69–138` brands SourceNodeKeys with P's parse Arc, green
   allocation and start offset. Root construction and child descent mint keys;
   cloning P preserves the brand. `source_identity::source_keys` traverses those
   parse-owned producers. Equal source text or equal range is insufficient.
2. `ShadowArtifact::from_parsed` (`shadow.rs:624–686`) preflights P's immutable
   root, requires empty syntax diagnostics, retains P, and returns A even when
   its separate lexical skeleton is unsupported. Thus successful retention
   witnesses diagnostic-free syntax publication; skeleton success is not a
   necessary source-entry premise.
3. `ShadowArtifact::retain` (`1198–1273`) records every actual raw node/token,
   its exact kind, range, parent and ordinal, then visits reversed child pushes
   in original order. Every retained node gets P's key when available;
   duplicated keys become ambiguous. `source_position` (`835–847`) rejects
   foreign, ambiguous and missing keys. Tokens have PositionIds and parent
   ownership, not individual SourceNodeKeys.
4. `pending_role_impl_sources` (`919–928`) enumerates retained role/impl syntax
   occurrences. `with_associated_method_role_sources` (`931–1049`) checks their
   same-parse keys, node kinds and exact retained round trips before publishing
   borrowed original nodes. This is not a RoleId, semantic member inventory or
   executable member closure. The field part selects FieldTail owners; the
   fixture's `::second` is a PathTail and gains no field bridge from this call.

R100's local constructor analysis explains the expected member ownership:
`impl_declaration_normalized` calls `impl_tail_normalized`; its braced body
contains a Statement and BindingStatement. `binding_statement_normalized`
opens the BindingHeader, parses its target, consumes Equals, then opens the
BindingBody. `pattern/mod.rs:1192–1241,1407–1455` constructs ordered sibling ML
tails: recursive argument precedence prevents `self` from swallowing the next
formal. The inline body branch preserves its own body occurrence. These are
constructor-derived syntax facts. E would establish that the exact published
fixture actually has the relevant occurrences, instead of assuming entry.
Unpinned expression/type constructors used historically by R100 were not
reopened or inspected here; their bounded result is reused from R100's reviewed
closeout, not upgraded to new direct source evidence.

**Application:** E supplies precisely the exact-fixture published-root and
same-parse occurrence premise needed by R100's inspected consumer case split.
After E is recorded, the fixture-specific `R100-ENTRY` obligation is satisfied
to this bounded observation scope. Its former demand to lease another parser
dispatcher owner is unnecessary for this finite test route. General parser
dispatch completeness remains unclaimed and is not a new blocking gate.

## First missing executable binder premise

The current pinned HIR owners make this boundary explicit:

- `lower_module_with_counters` (`module.rs:1153–1275`) plans direct root nodes.
  Only Binding plans receive DefinitionRootIds; DirectExpression and Unsupported
  plans receive none. There is no descent into this impl member in that loop.
- `plan_root` (`1976–2025`) admits an OperatorChain or a direct BindingStatement;
  every other node kind yields UnsupportedItem. Hence the observed direct
  RoleDeclaration and ImplDeclaration take Unsupported plans.
- The complete alternate branch of `lower_plan` (`2052–2204`) converts an
  Unsupported plan to HirItem::Error. Only its Binding branch mints the ordered
  HirParameterIds, records original parameter keys, calls LocalSource formation,
  pushes parameters into the body scope and wraps the body in Lambdas.
- `local_source::form` (`556–643`) rejects Unsupported plans. Its admitted
  Binding route preserves each parameter's own source and annotation and
  introduces each parameter into its lexical table before scheduling the body.
  Retained nested syntax alone cannot enter that route.

Thus E activates the reviewed source cut for the actual fixture but **does not
create executable binders**. The first missing premise is
`R100-P2-MEMBER`: materialize this exact nested implementation BindingStatement
into an authenticated executable member root with the original `self` and
`selected` HirParameterIds, their own annotations, and a body environment in
which the actual body occurrence resolves to its owning formal. Syntax order
does not license assigning semantic receiver/formal roles from a signature.

P3 selected target/ordinary receiver-first Apply and P4 complete candidate/runtime
admission remain independently OPEN. R100's reviewed later cuts are reused only
within their inspected path: generic structural association does not select
C_member, PathTail is not ordinary qualified-member admission, and an effect
Operation head is not role dispatch. Candidate/runtime source files are not
R106 pins and were not reread. R100 closeout's exclusion of the unpinned R84
contribution and its correction of the monomorphic-preflight overstatement
remain binding; neither excluded claim is used here.

Ordinary body checking, method lookup/selection/dispatch, result `2`, original
Simple-sub/evaluator A/B and semantic adoption gates remain OPEN. Generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization remain required. F1/FK1 and foreign-continuation quantifiers
remain independent. No provider/residual/witness lineage is collapsed, no
withdrawn bypass is restored, and ordinary inference is unchanged.

## Mutual TODOs and exact falsifiers

| Request / owner | Required evidence and falsifier |
| --- | --- |
| `R106-ENTRY-OBSERVE` / Luna and separately leased test author | Freeze reviewed implementation and obtain the sole authorized command receipt. A failing test, different source/root/range/order, foreign parse pairing, or association failure falsifies E. Before that receipt, E is pending and R100-ENTRY must not be reported observed. No retry or repair is authorized by this proof packet. |
| `R100-P2-MEMBER` / Luna to authorize the module::plan_root/lower_plan → LocalSource owner after semantic adoption | Minimal provisional implementation/evidence TODO only: authenticate this actual nested member's executable root, original parameters/annotations and body resolution. Required input is E plus the approved semantic contract. An already complete pinned consumer producing that member falsifies the present missing-constructor cut; a standalone same-spelled binding, signature-derived binder or spelling-only body resolution fails the required evidence. Proposed outputs need a new exact lease; no production edit is approved here. |
| `R100-P3-TARGET` / future approved qualified-call/ordinary-admission owner | After P2, connect the selected original member to the two whole ordinary operands with caller provenance. An effect Operation head, reordered operands or a synthetic member fails this premise; an independently established existing exact consuming path would refute the missing-path assertion. |
| `R100-P4-ADMIT` / future candidate/runtime owner | Establish actual member-body/end-point constraints, generation/accumulation/propagation and complete admission. Copied signature endpoints, incomplete metadata or an Act placeholder exemption fail this premise. R106 grants no new source pins or code rights. |

R95's reviewed bounded bridge and corrected HIR-span/provenance-range law are
reused only under successful same-parse retention/association hypotheses. Its
three historical passing tests are not rerun or evidence for this new fixture.
R100's reviewed constructor/consumer result is reused at its actual premises.
R85 hypothetical transitions, equal-spelled substitutes and R84's excluded
unleased evidence are rejected as closure evidence.

## Frozen inputs, resources and stop

All 18 direct input rows and the contract hash matched before source inspection.
The exact manifest is the frozen revision-1 contract above. The R100 proof
author is `/root/r100_member_proof`; R100/R95 closeouts are Luna's receipts.
Compiler/test source authors are UNKNOWN. R106 author claims only this note
and its exact handoff. No implementation coauthorship or independent
certification is claimed.

Checks: read-only cat/sed/rg/sha256sum inspection and finite branch analysis.
No test, build, compiler/runtime/CLI, formatter, Git, external contact or
executable probe occurred. Requested model/effort: **Sol/high**; observed
model/effort: **UNKNOWN/UNKNOWN**, since no runtime metadata was exposed.
Clock receipt during work: `2026-10-19 06:31:28 UTC`; pre-clock duration,
CPU/memory and exact remaining seconds are UNKNOWN. Work remains subject to
the cumulative 600-second cap; no allocation was reset or expanded.

Exact new paths: this note and `tasks/agent-loop/inbox/20261019-r106-proof.md`.
No scratch/generated paths, descendants or descendant leases exist. Next
in-envelope stage after freeze: none. **Writes stop at the frozen handoff.**
Luna owns observation, fresh review, intake, adoption and any next lease.
