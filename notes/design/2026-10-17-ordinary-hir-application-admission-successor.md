# Ordinary HIR admission for associated applications: successor contract

Status: repaired concrete proposal for independent review; not adopted. The user selected
direction A as a drafting target. This text alone grants no code, test, language
semantics or production authority.

Sprint: `choice-a-group-root-ownership-repair-20261017`, contract revision 1,
SHA-256 `21f4e33adebb4e92894bfe5fbc96eb96dac49135bbb06f65c18d0211991c332e`.
Successor artifact revision 4; revision 3 is preserved in Git commit
`a640dd909132b2be1d1bbbe35a4249e16642b84b`.
Parent remains the original Yulang inference/execution goal with the original
A/B claims, quantifiers and source/native correspondence unchanged.

Source constructor input: [Choice A CST/source-key audit](../theory/2026-10-17-choice-a-call-cst-source-key-audit.md),
SHA-256 `e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`,
candidate proof pending fresh review. Its fixed source is
`my id x = x; my apply f = f 1; my answer = apply id`.

## 1. Contract decision

Direction A admits a defined structural subgrammar of recovery-free applications
into canonical ordinary binding-body HIR. An admitted `Apply` records the
existing parser association and source operands only. Its existence does not
assert that the callee is callable, choose a Call typing rule, solve a type or
effect, establish source T, or authorize production inference.

For a supported application node itself, ordinary HIR emits no
`UnsupportedExpression`. An unresolved or ambiguous operand receives the same
`NameResolution`, error kind, source range and value attachment as ordinary
atom lowering, once, in the specified source order. Such operand errors are
newly materialized compared with the old whole-body refusal. The fixed
three-binding source therefore has zero structural HIR errors if all names
resolve as established by the constructor audit. This is an admission result,
not a successful solver result.

## 2. General admitted source grammar

The grammar is inductive over the associated `HirExpr` tree, not a source-text
specimen list. `Atom` means exactly one childless `IdentifierExpression` or
`IntegerLiteral` whose CST node maps uniquely to the retained parse. `E` is:

```text
E ::= Atom
    | Group(E)
    | Apply_ml(E, E)
    | Apply_call(E, E)
```

`Apply_ml` is one `MlArgument` continuation and `Apply_call` one `CallTail`
continuation. Each continuation must associate to exactly two children in
callee/argument order. Nested applications follow the authoritative association
recursively, including left-associated callees such as `(f x) y`. A Group is
admitted only when a `ParenthesizedExpression` contains exactly one supported
expression and no comma/tuple punctuation. Group is retained as structural
provenance and introduces no semantic grouping rule. Parentheses around atoms
may be represented by the existing atom source node when association elides the
wrapper; whenever a Group HIR node is retained, it receives its own source key
and occurrence.

No recovery node, missing required child, ambiguous source-node mapping, or
unsupported child occurs in a successful tree. Infix/prefix/suffix/unknown
operator nodes, tuple or comma arguments (including one-tuples), empty/unit
arguments, strings, lambdas, blocks, and other non-Atom/non-application forms
are outside this grammar. The whole enclosing application is refused
atomically; existing ordinary `UnsupportedExpression` attachment and range are
retained, and no hidden operand is name-resolved. This is a deliberate bounded
HIR grammar, not a claim that those source forms are invalid in Yulang.

There is no arbitrary syntax-depth constant borrowed from shadow lowering.
Projection uses an explicit worklist and visits each reached CST/HIR node once.
The number of pending and retained entries is linear in the accepted expression
subtree. Arithmetic and occurrence-ordinal conversions are checked; each new
collection reserves before publication. The actual hard identity ceiling is
the existing `u32` occurrence ordinal. Exhausted identity or allocation
capacity returns the existing availability failure for the enclosing module;
it does not publish partial HIR. A later implementation receipt must report
actual allocation strategy and measured fixture counts. No universal parser,
solver or termination bound follows here.

## 3. Ordinary and opt-in API behavior

`lower_module` is the canonical ordinary entry point. On an admitted body it
retains `ResolvedExpr::Apply { source_form, callee, argument, errors, range }`
for each associated application. `source_form` is exactly `MlArgument` or
`CallTail`; callee and argument match the associated left-to-right HIR children.
Application structure contributes no error ID. A resolved atom has its usual
`NameResolution`; an unresolved or ambiguous atom receives its usual resolution
and exactly one ordinary lowering diagnostic. An unsupported/recovery-bearing
expression keeps the existing error form and diagnostics.

The ordinary route continues to form exactly the existing `SourceCarrierOutcome`
for every admitted binding, with the existing direct-expression outcomes, source
identity sidecar and availability behavior. Apply admission changes the
canonical `ResolvedExpr` tree and its ordinary error sink. It may add the exact
source-key mapping for a retained body-root occurrence that previously
represented an unsupported expression without a mapping, and mappings for
newly allocated canonical-HIR descendants. It neither skips nor changes carrier formation,
Supported/Unsupported classification, carrier forms, root/parameter ownership,
existing mappings or pre-existing carrier occurrence IDs. The carrier and
canonical HIR may represent the same parsed node with distinct occurrence IDs;
both IDs map to that exact same parse-branded `SourceNodeKey` and belong to the
same HIR artifact. They are separate projections, not a one-to-one occurrence
crosswalk.

The opt-in `lower_module_with_local_source`/shadow route retains its current
source-carrier and placeholder-error behavior in this contract. Its
`UnsupportedExpression` IDs remain authentic evidence that semantic lowering
is pending there. The two separately branded module artifacts are not occurrence-
identity equal merely because they came from one ParsedFile.

The fixed literal lowers to `id = Lambda(x, Name(Parameter(x)))`,
`apply = Lambda(f, Apply_ml(Name(Parameter(f)), Integer(1)))`, and
`answer = Apply_ml(Name(ModuleDef(apply)), Name(ModuleDef(id)))`. The two outer
body occurrences are the existing body-root occurrences. This does not identify
any application result with an accepted function type.

## 4. Errors, recovery and publication

The existing pre-body causal-error gate remains first. If a binding already has
a header/item error that suppresses its body, it does not inspect application
operands. `has_recovery` remains before structural projection. Missing,
Invalid, Error, retry/recovery, comma/tuple and unsupported operator shapes
refuse the complete enclosing expression using the existing cause and
attachment; the lowerer never resolves only the visible subset of operands.

For an admitted shape, only the structural-application `UnsupportedExpression`
that the old ordinary path emitted for that body is removed. No other pre-existing
`HirError` is removed, reclassified, reordered relative to other retained
records, or cloned. Operand diagnostics are emitted once in the existing
atom-lowering source order, with
`HirErrorAttachment::Value(DefId)` and the exact operand range. Each
`Apply.errors` is the ordered, duplicate-free list of authentic error IDs within
that retained subtree; for the fixed literal it is empty. Parent aggregation may
reference a child error ID but cannot create another `HirError`.
`HirModule::errors()` remains the authoritative error collection.

Within every resulting module, `HirErrorId` and `HirDiagnosticId` remain dense
phase-local vector indices in the existing emission order, and all cross-references
point to the records at those final indices. Every retained non-admission error
and diagnostic keeps its exact payload (origin, attachment, range, kind and
diagnostic association), multiplicity, and relative order with other retained
records. Newly discovered operand errors are inserted according to ordinary
source/lowering order. Because IDs are assigned from the final vector positions,
removing an earlier application-admission error or adding a newly visited
operand error may change the numeric IDs of later retained errors and
diagnostics. Numeric equality across pre- and post-admission module products is
not guaranteed; corresponding retained records are matched by their full
payload and ordered multiplicity, never by numeric ID. No sparse IDs,
tombstones, or alternate ID storage are introduced. This preserves the
authoritative dense-index invariant while stating its observable consequence.

The implementation preflights the complete expression and all unique source
keys before replacing the old unsupported body. It constructs a private result,
then publishes the node and error-sink delta together. Structural mismatch
falls back to the old unsupported result; identity/allocation exhaustion aborts
module lowering with no partially published module. Existing item order,
retained error payloads/order and attachment ownership remain unchanged; final
dense IDs are assigned from the resulting vectors as described above.

## 5. Identities and allocation order

Every retained expression node maps to its exact parse-branded `SourceNodeKey`;
keys are not reconstructed from spelling/range or matched by text. An Apply
maps to its `MlArgument`/`CallTail` node; leaves map to their exact
IdentifierExpression/IntegerLiteral; retained Group nodes map to their
ParenthesizedExpression. Callee and argument always have distinct source keys.
Equal text or coincident ranges do not merge nodes. Source parse brands,
`HirArtifactToken` brands, HIR occurrence IDs, parameter IDs and DefIds remain
distinct identity domains.

For each admitted body the existing body-root occurrence belongs to the
outermost retained canonical HIR node, preserving that already allocated
identity for every grammar constructor:

| Retained root | Preserved body-root occurrence maps to |
|---|---|
| `Atom` | Its exact `IdentifierExpression` or `IntegerLiteral` key |
| `Apply_ml` / `Apply_call` | Its exact outer `MlArgument` / `CallTail` key |
| `Group(E)` | Its exact `ParenthesizedExpression` key |

Do not elide a retained Group to give its inner Apply the root ID. For
`my z = (f x)`, Group owns the existing body-root ID and parenthesized key;
the inner Apply, callee and argument receive distinct appended occurrences and
their exact keys. Existing association-level elision around an atom remains
only where the association adapter actually elides the wrapper; in that case
the retained Atom owns the root ID and its own exact key. Existing
binding roots, lambda and parameter identities, ordinary root order and all
previously observable ordinary HIR occurrence ordinals remain unchanged. The
existing ordinary source-carrier pass then runs with the same roots, source
keys, traversal, outcomes and occurrence allocation as before; all previously
published carrier occurrence ordinals therefore remain unchanged too. Only
after that pass completes are additional canonical-HIR child/Group occurrences
allocated from the same artifact, deterministically in source preorder. Each
new HIR occurrence is unique and maps to the exact same parse key used by the
corresponding carrier node when one exists; it does not reuse that carrier
occurrence ID. No additional canonical-HIR child occurrence is allocated for a refused or
recovery-bearing shape. The full module remains unpublished until the canonical nodes,
additional IDs and source mappings succeed.

When the old body was an unsupported expression, the preserved body-root
occurrence may have no entry in `HirSourceIdentity::occurrences`: ordinary
`lower_body` returns an unsupported projection before `lower_leaf` records an
atom mapping. The root's mapping must be the exact key for its retained
constructor from the table above. Stage this mapping together with all new
descendant mappings. Preserve every existing entry: if the root already maps
to this exact key, keep it without staging a duplicate; if it maps to another key, return
`HirAvailabilityError::InconsistentIdentity` without overwrite. Do not use
`record_occurrence`'s overwriting insertion as the publication mechanism.
Build one occurrence-only `empty_stage`, reserve all required capacity, and
publish it through the existing atomic `HirSourceIdentity::append_stage` only
after ordinary source-carrier formation and before the `HirModule` is returned.
Any reservation, collision, or ordinal failure returns the specified
availability error and publishes no module or partial mapping.

The ordinary lowering loop currently constructs `ResolvedExpr` values before
`form_ordinary` allocates carrier occurrences. To preserve both established
carrier ordinals and the required final allocation order, keep accepted
application projections private until the legacy ordinary and carrier passes
finish. Preserve error-sink emission order while staging their resolution and
error references in source order, then finalize canonical HIR child IDs and the
atomic identity stage after carriers. This is an internal finalization boundary;
it does not change public HIR shape, diagnostics, or the selected admission
grammar. The pinned construction paths establish feasibility: unsupported
`lower_body` returns before `lower_leaf` records the body mapping;
`form_ordinary` stages and merges carrier identities before module publication;
`append_stage` rejects duplicate occurrence IDs and reserves before extending.
The exact Group key is available through the same existing source-key map:
`source_keys(parsed)` records every parse-owned syntax node, and the
`ParenthesizedExpression` carrier branch resolves that exact node through the
checked `self.key` lookup before retaining a Group. This establishes key
availability for an actual mapped Group node, not general parser acceptance or
the fixed-literal source audit. Implementation must add an explicit preflight
for same-key versus conflicting root mappings and use `append_stage` for
non-overwriting atomic publication.

## 6. Apply producer/consumer contract

All affected `ResolvedExpr::Apply` routes must be checked against this split
between ordinary structural admission and opt-in pending structure:

| Owner/API | Required behavior under this contract |
|---|---|
| `yu_hir::module::lower_module` / ordinary binding lowering | Produce error-free structural Apply only for the grammar above; preserve old errors for every refused form. |
| `lower_module_with_local_source`, shadow lowerer, `LocalSource::form` | Keep current opt-in carrier, placeholder IDs and no-partial-projection behavior; do not silently consume/clear ordinary diagnostics. |
| `HirModule::shadow_resolved_call_inventory` | Accept authentic ordinary Apply with empty `errors`, as well as opt-in Apply with valid existing IDs. It reports structure/identity only; empty errors do not mean typed Call. Continue rejecting foreign, missing, duplicate or ambiguous occurrences. |
| ordinary `ConstraintBatch::collect` in `yu_solver::lib` | Do not infer or emit Call typing from ordinary Apply. Preserve its current non-complete/error body status until an independently approved Call source rule exists. |
| `CandidateInference`/`shadow_apply` and candidate source crosswalk | Remain feature-gated/private-candidate paths. Their result is not standard inference or theorem evidence. This contract does not widen candidate semantics, its ownership/resource limits, or candidate acceptance. |
| test-only Apply source crosswalks and equality/traversal consumers | Preserve exact operand order, source form, artifact ownership, recovery causes and refusal behavior; update assumptions that equate Apply with nonempty errors only where ordinary HIR is explicitly accepted. |

The unconditional `ResolvedExpr::Apply` enum variant is reused; no new type,
term, callable judgment, desugaring, constraint recipe or syntax meaning is
introduced. Its public documentation must distinguish structural source
admission from semantic Call lowering. An implementation audit must search the
whole repository for every producer and exhaustive consumer before editing.

## 7. Exact supersessions and preserved authority

Only after explicit user approval of this exact reviewed text, the implementation
may supersede these specific clauses, and only for the grammar in section 2:

1. `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md`:
   its flat ordinary expression product and the clause excluding application
   syntax from ordinary simple-module bodies and requiring
   `UnsupportedExpression` for otherwise supported Apply or retained Group
   forms in section 2's grammar. The scope is limited to those constructor
   forms in binding bodies; all refusal behavior outside the grammar remains.
2. `notes/design/2026-10-10-ordinary-hir-successor-carrier.md`: only its promise
   to leave ordinary application admission, application-owned HIR diagnostics
   and canonical-HIR application occurrence structure unchanged. Its binding
   and expression `SourceCarrierOutcome`s, Supported/Unsupported results,
   carrier forms, source identity mappings, root/parameter/artifact reuse,
   availability failures and every pre-existing carrier occurrence ordinal
   remain in force unchanged. The added canonical-HIR child occurrences are
   allocated after those carrier ordinals and map to exact parse keys without
   replacing carrier IDs.
3. `ResolvedExpr::Apply` and `ResolvedExpr::Group`'s opt-in-only documentation,
   and any `shadow_resolved_call_inventory` restriction that rejects ordinary
   structurally admitted nodes, solely to permit structural observations of
   accepted Apply/Group nodes. Opt-in placeholder/error ownership remains
   unchanged.
4. The September 19 dense phase-local error/diagnostic ID clause remains in
   force within each resulting module. This proposal makes no change to that
   invariant. The exact compatibility rule for this admission change is that
   numeric IDs for later retained records are not guaranteed equal across the
   old and new module products: dense indices are recomputed from each final
   ordered vector, so removing an application error or inserting an operand
   diagnostic can shift those values. This consequence is part of the exact
   user-approval request; no expected-output or implementation changes before
   that approval.

The September 18 association rules, September 19 nested-chain ownership
amendment, September 20 direct-root behavior, lexical/name-resolution rules,
recovery policy and operator environment remain unchanged. Direct-root
application admission is not included: it retains the separately approved
direct-root contract. No rule about function/call typing, effects, generalization,
solver acceptance, native behavior, error recovery beyond the listed boundary,
or any original theorem is changed.

## 8. Required implementation regression contract

After final approval and a separate exact code/test lease, the vertical
regression set must establish:

1. The fixed source has zero HIR errors, exactly two retained body applications,
   correct formal/module resolutions and exact distinct operand source keys.
2. General inductive cases: multiple left-associated ML tails; CallTail with one
   supported operand; nested application in callee and argument; Group over
   Atom; root Group over Apply (`my z = (f x)`); nested retained Groups at
   accepted depths; identical spellings at distinct source positions and
   repeated parse artifacts. Each Group retains its key and is not elided.
3. Existing ordinary items, DefIds, parameters, roots and ordinary HIR
   occurrence ordinals stay stable when a body gains Apply children. Existing
   carrier outcomes, carrier structure, source-key mappings and carrier
   occurrence ordinals also stay stable. New HIR-only child IDs are unique,
   artifact-branded, source-ordered and allocated after the carrier pass.
   The preserved body-root ID maps to the exact key for its outer retained
   Atom, Apply or Group constructor; in particular a root Group maps to its
   `ParenthesizedExpression`, not its inner Apply. Matching existing mappings
   are retained and a conflicting mapping fails without overwrite. Descendant
   mappings are exact and added atomically; refused/recovery bodies gain no
   application mappings.
4. Error and diagnostic vectors are dense and internally cross-referenced in
   each resulting module. Retained record payloads, multiplicity and relative
   order are unchanged; IDs are resolved to final vector positions. A fixture
   with an application admission error before a later unresolved name asserts
   the later diagnostic's unchanged semantic payload and its newly dense ID,
   without asserting numeric equality with the pre-admission product.
5. Unresolved/ambiguous atoms keep their exact resolution and one diagnostic;
   applications do not duplicate or suppress it.
6. Recovery, malformed delimiters, one-tuples, unit/empty calls, operator
   operands, lambdas, blocks and unsupported forms preserve old refusal,
   attachments and diagnostic order and allocate no child occurrences.
7. Source identity inventory accepts ordinary empty-error Apply but rejects
   foreign/missing/ambiguous keys and duplicate occurrences. Ordinary carrier
   outcomes and opt-in local-source placeholders/error ownership remain
   unchanged.
8. Checked ordinal/collection exhaustion fails atomically. A stress fixture
   reports CST node count, admitted Apply count, worklist peak, storage growth
   and failure disposition; no shadow-only bound is reported as universal.
9. The regular solver does not emit a Call typing constraint from the new HIR
   alone. Any candidate-only path is labelled and tested separately, without
   promoting its result to standard inference.

No tests or compiler runs were performed while drafting. Existing red CI format
checks, if encountered later, must be reported separately from new code checks.

## 9. Open gates and required approval sequence

Fresh independent spec, compiler and architecture reviews must examine this
exact artifact, the frozen source audit, current `module.rs`, `local_source.rs`,
`source_identity.rs`, the ordinary-carrier authority and direct dependency pins
in that order. The compiler review includes the raw-source constructor audit.
Repair blocking/major findings in a new frozen revision and review those bytes;
there is no additional source-review pass beyond this combined bundle.

Then ask the user to explicitly approve this exact successor contract, the
named supersessions and the stated downstream numeric error/diagnostic-ID
shifting consequence in section 7. Direction A alone is not this approval. No
compiler or test lease starts before that answer.

Even after adoption, the following remain OPEN: generated Call constraints,
accumulation/propagation and actual consumer; semantic Call and source T;
SV-CONSUMER-1; OPRESP-DEFAULT-1/OPRESP-ENTRY-1/C-OMIT; NPAIR formation/replay,
N-Transport, N-Subtract-Elim; F1/FK1 and the original A/B quantifiers;
soundness, principality, termination and production promotion. A HIR regression
can close only its exact admission/identity behavior.
