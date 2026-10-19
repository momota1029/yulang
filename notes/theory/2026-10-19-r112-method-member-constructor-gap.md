# R112 exact member: source entry applied to the HIR constructor gap

Status: **candidate finite source-correspondence obstruction; independent review pending**.
Author and sole writer: `/root/r112_proof`; no coauthors or descendants.
Assignment `R112-P2-MEMBER-PROOF`, revision 1. Contract revision 3:
`tasks/agent-loop/sprints/method-role-p2-source-application-20261019-r112-rev3.md`,
SHA-256 `ed7510f30473a7ea5c990cf12b13502e3c57e7a26e3a463ddc7402a5e17a273a`.

## Claim, scope and parent application

The original R100-P2-MEMBER premise requires the actual selected implementation
member's executable binders, original annotations, body and lexical environment.
Its parent R85 P2/P3/P4 obligations are preserved at the pinned R100 proof
§Parent application and exact limit and the Draft R85 contract §§2–4. P3 requires
the authentic member in receiver-first ordinary Apply with whole operands and
caller provenance; P4 requires complete target admission before publication.
The parent is OPEN, and R85 remains Draft and unadopted.

R108 supplies the formerly missing finite R100-ENTRY premise for the exact
148-byte, no-final-LF fixture with SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`.
Its reviewed observation identifies one authentic ParsedFile, the direct
RoleDeclaration and ImplDeclaration roots, and the original member ancestry,
raw child order and distinct formal/body `selected` occurrences in that parse.
This note consumes that result; it does not repeat a parser construction proof
or rerun the test.

**Finite conclusion:** on the inspected production `module::lower_module`
route, whenever lowering reaches the relevant item, that exact ImplDeclaration
becomes an UnsupportedItem plan and then a HirItem::Error. It acquires neither
a member DefinitionRootId nor HirParameterIds, executable body or member
lexical environment, and neither production carrier pass forms a LocalSource
for it. An availability failure can terminate the route earlier; no successful
publication or runtime observation is assumed. The identical plan distinction
also applies to the exact RoleDeclaration. This is a constructor obstruction
for the exact fixture and complete named owners, not a universal absence claim
over all compiler modules or a refutation of the proposed role semantics.

Applying R108 to R100 removes the old conditional entry premise from this
finite obstruction. The remaining positive P2 obligation is now located at
the authentic nested-member materialization seam; more parser evidence cannot
provide its missing executable owner. P3/P4 do not follow from this obstruction.

## Production owner derivation

All line references below name the two pinned current source files.

1. `module.rs:1103–1112`, production `lower_module`, initializes source identity
   and source keys, sets `ordinary_source_carriers = true`, then calls
   `lower_module_with_counters`. The proof uses this production entry, not a
   test helper's configuration.

2. `lower_module_with_counters`, `module.rs:1173–1184`, creates the syntax root
   from the supplied ParsedFile and enumerates **direct node children**:
   `root.children().enumerate()`. Let I be R108's authentic ImplDeclaration
   (`52..114`) and let i be its index in that node-only enumeration. Its exact
   production ordinal is `u32::try_from(i)`; on conversion failure lowering
   returns IdentityExhausted. On success `plan_root(I, ordinal, ...)` is called.
   R108's retained raw ordinal uses `children_with_tokens()`; that raw ordinal
   is not substituted for i. Same-parse direct-root identity supplies the
   correct node, while the actual production enumeration supplies its ordinal.
   No numeric ordinal or opaque source key is invented here.

3. The complete `plan_root`, `module.rs:1976–2025`, first recognizes exactly
   OperatorChain as DirectExpression. Its next test rejects every node kind
   other than BindingStatement with
   `RootPlanKind::Unsupported(HirErrorKind::UnsupportedItem)`. I is an
   ImplDeclaration, so this return precedes `plain_binding_header`, DefId
   allocation and admitted parameters. The returned RootPlan retains I,
   its range and the production ordinal. There is no nested-member descent
   in this branch. The RoleDeclaration follows the same return. The ordinary
   top-level `answer` binding is a separate root, not the implementation member.

4. `namespace`, `module.rs:2027–2050`, processes only Binding plans, so it adds
   neither declaration nor the nested member as a module executable definition.
   In the lowering loop `module.rs:1230–1260`, ExpressionRootId allocation is
   guarded by DirectExpression, and DefinitionRootId allocation is guarded
   by Binding. For Unsupported the definition root is None. Thus even though
   a root-loop HirOccurrenceId is minted, it is not a member DefinitionRootId,
   ExpressionRootId or binder. Recording source definitions also requires
   Some(definition), which this root lacks.

5. Complete `lower_plan`, `module.rs:2052–2204`, takes the non-Binding branch
   immediately. Unsupported emits the corresponding lowering error attached
   to `HirErrorAttachment::DirectRootItem(plan.ordinal)` and returns
   `HirItem::Error` over the plan range (`2078–2090`). An ErrorSink availability
   failure exits rather than manufacturing a binding. All executable-binding
   work occurs after this return: DefinitionRootId extraction, HirParameterId
   creation, optional legacy LocalSource formation, parameter insertion into
   ScopeStack, `lower_body`, and Lambda wrapping. None is reached for I.
   In particular equal spelling of the two `selected` occurrences cannot
   create the missing lexical binding.

6. The item is pushed into `items` at `module.rs:1293`. The production binding
   carrier pass is gated at `1298` by
   `let HirItem::Binding(binding) = item else { continue; };`.
   The production expression carrier pass is gated at `1310` by
   `let HirItem::Expression(expression) = item else { continue; };`.
   I's Error satisfies neither gate. Its outcome slot remains None and is
   flattened away, rather than becoming a Supported or Unsupported carrier
   with a manufactured SourceRootId. No call to `local_source::form_ordinary`
   is made for it. These production gates, not test-helper Error arms, establish
   the carrier exclusion. The cfg-specific Act placeholder branch at
   `1273–1292` requires ActDeclaration and supplies no alternate route for I.

7. `finalize_ordinary_admissions`, `module.rs:1527–1656`, consumes staged ordinary
   admission records and requires an existing HirItem::Binding at each owner
   index before replacing its expression. It cannot turn this Error into a
   member binding. The same module's `local_source_for`, `979–988`, looks up
   authentic existing source carriers or definition-owned local_sources; it
   does not allocate an authentic member root on lookup.

## LocalSource boundary and absence of a substitute producer

The complete boundary `local_source.rs::form_ordinary`, `502–554`, stages
identity and invokes `form` with an already supplied plan, SourceRootId and
HirParameters. `form`, `556–642`, accepts Binding or DirectExpression and
returns invalid for Unsupported before constructing its Builder. For an actual
Binding it preserves parameter IDs and original source keys/annotations, pushes
lexical resolutions for those parameters, emits Lambda forms, and schedules
the binding's own body. This is precisely the authentic work missing upstream;
the boundary is not a method-member discovery operation. Its nested-expression
machinery is reached only after that accepted input, which I never supplies.

The member therefore has no authentic executable source on this production
route from which to generate its body constraints, accumulate or propagate
them, or feed later candidate/native consumers. This statement asserts absence
of this member's producer, not absence of all constraints in the fixture.
No solver, candidate or runtime source outside the two pins was inspected,
and no runtime/native execution is claimed. R100's later P3/P4 cuts remain
prior evidence within their own hypotheses; they are not new findings here.

The exact falsifier is an owner-local route in these pinned owners that consumes
this same nested member and creates its authentic executable binders/body/
environment despite these branches. Inspection of the complete plan/lower
branches and carrier gates finds no such route. A same-spelled top-level
binding, role signature, retained SyntaxNode, root-loop occurrence or assumed
Apply transition does not satisfy that falsifier. A newly required owner or
alternate producer requires Luna's boundary decision before further inspection.

## Preserved premises and minimal mutual TODO

`R112-P2-MATERIALIZE` requests evidence for original R100-P2-MEMBER. Owner:
Luna for authority/adoption, then a separately assigned `module::plan_root` /
`module::lower_plan` and LocalSource constructor owner. First missing evidence:
an approved source judgment plus an authentic producer retaining this nested
member's ordered executable binders, annotations, body and lexical environment.
Required inputs are this exact same-parse source entry and the original P2
contract. Proposed output is a separately leased source-to-constructor
correspondence, or the smallest provisional implementation TODO if approved.
Exact falsifier: an existing owner-local authentic member constructor, or a
claimed new producer that substitutes a signature/same-spelled binding, loses
the two formal identities, or cannot resolve the original body occurrence in
the original lexical environment. This TODO grants no implementation lease.

Luna's mutual TODO is to obtain fresh post-output spec and independent source
review of these frozen bytes and adjudicate the result. The producer is
ineligible to certify it. Existing R100 implementation assessment remains
NO_SAFE_ROLE_CODE_SLICE; it is reused without a new implementation/test lane.
Next related producer step inside this envelope: none after freeze.

Original Simple-sub/evaluator A/B and their accepted domains/quantifiers remain
OPEN. F1/FK1, including foreign continuations, remain independent; no local
frame result closes them. Residual/provider/witness lineages remain distinct.
Generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization remain required. No withdrawn bypass, weakened ordinary
inference, R50 adoption, semantic role lookup, selected method type, result 2,
production repair or parent closure is asserted. Six effect-hygiene fronts
remain open. Historical R106/R107 command failures supply no source proof;
R108 supplies only its reviewed exact-entry result.

## Frozen inputs, authors and checks

Every listed direct input and contract hash was freshly checked and matched:

| Input | SHA-256 |
|---|---|
| R100 rev6 contract | `d595f4878b9f931214e5da0cba6d7e53cf3e2e0ca243ecad784e55cac1611dec` |
| R100 conditional proof | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R100 proof handoff | `1a692cb7f3c31e83bf60ee90763216ef3253f2c357747c9258eff16e2f8cec19` |
| R100 implementation assessment | `60a1a90c37b5c8377addf12cd07d9703f98a093a9c1eeb86fb5db2b81f847596` |
| R108 exact-source closeout | `cfc0e6a45b329e099f1263833bc7c0160c8d0e034bf7596ffef1dc5da10666e8` |
| R108 test `shadow_method_role_source.rs` | `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a` |
| R85 Draft contract | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |
| `module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| R112 rev3 pre-edit CLEAN receipt | `d09a51bb95d32ce674789970fd7f811b93ffa4e259aa7a0e713b82a0c4bcddd3` |

Prior proof/handoff author: `/root/r100_member_proof`; implementation assessment
author: `/root/r100_member_impl_audit`; R108 closeout and sprint authority: Luna;
R112 pre-edit reviewer: `/root/r112_pre_spec`. Source/test authors and unexposed
prior contributor identities remain UNKNOWN. No coauthorship or new authority
is inferred from reading their artifacts.

Requested model/effort: `gpt-6.1-sol` / high. Observed model/effort:
UNKNOWN / UNKNOWN; no runtime identity metadata was exposed. Static text/hash
inspection only; no tests, builds, compiler, runtime, CLI, formatter, Git,
external contact, source/test edits or descendants. Source pin set unchanged.
Cap: 300 seconds, cumulative and unexpanded; exact launch-to-clock time,
CPU/memory and remaining resource use UNKNOWN. First explicit clock receipt:
`2026-10-19 07:31:29 UTC`; pre-clock work remains charged. No executable
test/check budget used. Resource closeout appears in the single handoff.

Exactly two new paths: this note and
`tasks/agent-loop/inbox/20261019-r112-proof.md`. No scratch/generated paths or
descendant leases. **STOP at handoff freeze: writes cease.** Fresh independent
review and Luna intake are pending; no parent or production gate is closed.
