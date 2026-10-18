# Ordinary Call source-to-consumer contract audit

Date: 2026-10-18  
Sprint: `choose-sigma0-formation-and-call-consumer-contract-20261018-r12`, revision 2  
Contract SHA-256: `3979435e2e0cadf26d0aaace57c1ba7924021d2d73eb256acaf0e1c2ca015f5d`  
Baseline: `2a3f2a47d5013761f0e0717b0c6073c54c62d36`  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, fixed `c`, original quantifiers, **OPEN / closure 0**  
Outcome: source/consumer evidence; `NO_SAFE_CODE_SLICE`  
Authority: rev2 steering permits reversible proof-motivated interpretation
proposals by default when they preserve observable behavior, original premises
and domain; fresh independent review is required before integration. This
packet recommends review of the evidence-only bridge below. It grants no
production-code lease and adopts no new Call semantics.

## Scope and conclusion

This audit maps an ordinary source application through retained HIR, standard
collection, the existing candidate constraint path, propagation, and the
available Call metadata. It preserves the complete original Call contract and
does not infer a Call typing rule from a candidate relation or structural
occurrence. No production Apply/Group typing change is authorized by r12.

**`NO_SAFE_CODE_SLICE`.** The earliest missing premise is an adopted original
source rule for a general ordinary `Apply`/`Group` occurrence that derives the
complete typed Call judgment from its authentic source operands and all of the
original contextual/provider/output premises. The selected original Call
formation cases apply to actual emitted `Gen-Call-0` records; they do not assert
that every ordinary HIR Apply has such a record. No complete standard consumer
maps such an ordinary judgment through source generation, propagation, and
actual `ExecuteCallable` result/future consumption. A constraint rule alone
would not fill that bridge.

The first missing semantic/source bridge is therefore not a particular type
equation in the solver: it is the source-owned, complete ordinary Call rule and
its authentic producer-to-consumer interface. Until that is supplied by the
rule owner and related to a real consumer, a code change would select which
Apply forms count as calls, omit some retained original premises, or leave
candidate constraints without the required semantic consumer.

## Adopted premises retained

The [complete Call contribution definition](2026-10-07-complete-call-contribution-definition.md)
adopts `C-Call`/`CallMem` only for an authentic reference to the complete
original predecessor Call operation. That operation retains the original
callee computation, independently supplied whole argument carrier, dispatch
to the actual returned provider and real entry/role, returned-provider and
future-use interface, and every complete original alternative with its
evidence. Its structural clause is callee Bind followed by receiver execution
at the same returned provider/current configuration. Callee-pending and
receiver-pending cases retain distinct ordered suffixes. `SpecCall_e` consumes
that actual complete operation; independent complete `C0` remains required.

The [original Call formation definition](2026-10-07-original-call-formation-definition.md)
adopts `OSig-Demand` and `OC-CallEff` for actual emitted `Gen-Call-0` records,
at their original dependent tuple and scope. This preserves the record's
source position, checking occurrence, call occurrence, static root, scope,
complete source origin and separate invocation/elimination leg. A Call without
such a record keeps its existing derivation; the definition neither asserts
that every ordinary Call has a record nor rejects one that does not.

The [contextual Function membership definition](2026-10-08-contextual-function-membership-definition.md)
keeps same-provider whole-carrier acceptance and the complete observation and
future contract at the actual provider/configuration. Contextual guards,
independent admission, complete result typing and source ownership do not
follow from a printed Function shape, an endpoint pair, successful comparison,
or retained HIR identity. The [inference principles](2026-10-11-yulang-inference-top-level-principles.md)
require natural source constraints and ordinary propagation; they do not
authorize a special generation-time acceptance rule or speculative search.

These are all retained obligations, not code fields that can be dropped to
fit the current candidate path. In particular, this audit supplies no original
`F_c`, `Sigma.Lambda/G/W/Z`, `A_decl` output/license, domain/admission,
actual consumer, `F1/FK1`, `N-Transport`, Call soundness, principality, or
termination closure.

## Source-to-consumer map

| Stage | Existing owner/evidence | What it establishes | Missing for the adopted complete Call |
| --- | --- | --- | --- |
| Source/HIR constructor | `yu_hir::ResolvedExpr::Apply { occurrence, source_form, callee, argument, errors, range }` and `Group { occurrence, inner, range }` in `crates/yu-hir/src/module.rs` (around 478). `yu_hir::shadow::Form::Apply` and `Form::Group` retain structural operands; the resolved inventory in `crates/yu-hir/src/shadow.rs` borrows exact HIR occurrences. | Authentic retained node/operand identity and source association; Group structure is preserved. | No type, callability, source `Gen-Call-0` membership, complete operand interface, typed Call rule, output, license, provider/role, or semantic meaning. HIR's own Apply comment explicitly leaves Call typing unsupplied. |
| Standard collection | `ConstraintBatch::collect` calls ordinary `collect_mode(..., false)`. In `crates/yu-solver/src/lib.rs:1109-1115`, Lambda body Apply/Group and root Apply/Group are `CollectedBodyStatus::Error`. At `:1520-1538`, the structural walker retains each Apply and operands with `ApplicationTypingRuleUnresolved`; Group is traversed to its child. | The standard path does not generate a successful Call constraint for these nodes; it retains pending structure separately. Group traversal preserves child inventory but supplies no grouping typing rule. | No standard Apply/Group value/effect recipe, typed source Call, or successful body recipe. Replacing `Error` requires the missing adopted source rule plus consumer correspondence. |
| Candidate source constraint generation | `crates/yu-solver/src/candidate_source.rs` walks retained source. For `LocalSourceForm::Apply`, it reserves callee/argument/result value and effect endpoints and retains `CandidateRelation::Apply`; `Group` retains `CandidateRelation::Group` (`:1075-1144`, `:1214-1225`). This path is candidate/feature-gated and has explicit shape/annotation exclusions. | A candidate relation with authentic occurrence and endpoints; for Apply, the operand and result components/effects. | Candidate relation is not the original source rule. It does not establish source domain completeness, contextual checking, whole-carrier admission, original provider dispatch, complete `C0`, or Call formation. Group-as-endpoint forwarding is likewise not an adopted original Group rule. |
| Candidate call inputs | `crates/yu-solver/src/candidate_call.rs:241-278, 387-425` lists the original `Gen-Call-0` formation inputs and `PendingCallSupplier`s. `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, `ReceiverDispatchAndCompleteResultFutureInterfaces`, formal registration/route/exposure, and applicable module-name source typing/admission and receiving-export correspondence remain suppliers. | Candidate source call records can retain occurrence/operand identities and explicitly enumerate unresolved suppliers. `PendingCallConstruction::original_formation_inputs()` is an inventory of required inputs. | The inventory has no constructor that supplies the listed original inputs and no semantic certificate. Its names do not discharge any supplier. |
| Candidate constraint admission | `InferenceSession::admit_candidate_fact` in `crates/yu-solver/src/shadow_apply.rs:1731-1850` checks source-input identity when present. For Apply it forms a negative Function demand from the argument, argument effect, invocation/return effect and result; it admits a callee-positive <: demand-negative value constraint with occurrence/cause provenance via `ConstraintStore::admit_and_record_provenance` and `constrain_live_value`. | Concrete candidate constraint generation and consumption by the existing live value-bound store. With candidate graph effects enabled, an invocation effect row is created and the `argument_effect`/return effect fields are included in the negative function demand. | The constraint is not the full original Call judgment or its proof of source correspondence. The optional candidate `NativeInterface` and directional-introduction metadata are retained before admission but have no semantic Call consumer. They do not establish dispatch/result/future execution or original `CallMem`/`C0`. |
| Propagation | The live value solver consumes the admitted lower/upper pair and propagates bound transitions (`constrain_live_value` and downstream live propagation). Existing candidate tests exercise these candidate rows, including pending Application state. | Propagation of the generated candidate constraint through the candidate graph. | No propagation theorem or source/native map for the complete original Call follows. Propagation cannot supply a missing source premise, domain, license or actual result/future consumer. |
| Available semantic Call consumer | The adopted original definitions name `ExecuteCallable`, `CallMem`, and `C0` as semantic interfaces, with the exact premises above. The current candidate path stores an optional `NativeInterface`; its own comment states it has no semantic consumer. | The formal contract identifies what a legitimate consumer must preserve. | No standard source-to-`ExecuteCallable` consumer is reached from the ordinary Apply constraint. No matching producer/consumer bridge currently discharges the complete original Call contract. |

## Prior implementation and evidence reused

The reviewed 2026-10-17 ordinary-HIR repair fixed structural lowering and
ownership for the adopted Atom/Group/Apply grammar, but its contract explicitly
kept standard `ConstraintBatch::collect` in Error for Apply/Group and the
pending state `ApplicationTypingRuleUnresolved`. The frozen prior handoff
`20261017-ordinary-hir-call-projection-preservation` concluded that structural
operand incidence does not provide an independently typed original reference,
whole-carrier/context, license/provider/response/future contract. This audit
reuses that source/HIR finding and the existing current owner code rather than
reopening HIR lowering or reintroducing a withdrawn bypass.

The inspected `yu-core` shadow tests show partial structural projection:
`generate_source_calls` preserves direct-Use call identities only under its
selected unannotated declaration boundary; grouped/computed callees are not a
complete inventory. Its `UnresolvedPremise` list includes emitted
`Gen-Call-0` membership, complete clause/joint witness, initial descriptor
relation, finite source-base emission conformance, and complete invocation
interpretation. These tests were read, not run. The earlier unary Name/Name
boundary audit also records that source skeletons and structural incidence do
not imply a typed Call or ordinary consumer.

No Simple-sub bypass was restored: no rule skipping Call formation, no
constraint-only acceptance, no inferred Group transparency in standard
inference, and no dropping of source, context, output or provider premises.

## Exact missing owner request and falsifier

**First missing premise:** an adopted, complete source rule for ordinary
`Apply` (and any explicit Group rule it depends on), whose hypotheses identify
the authentic source operands and scopes and derive the complete original Call
judgment under the unchanged contextual/provider/output/license obligations.
The rule must say whether its source conclusion requires an emitted
`Gen-Call-0` record; the existing original formation rule cannot be silently
extended beyond that domain.

**Required owner evidence:** the original source-rule owner must provide the
exact premises/conclusion and source-domain guard, plus its authentic producer
map into the current HIR occurrences. The complete-Call/native owner must then
show how the same tuple, whole argument carrier, actual returned provider and
entry/role, all original alternatives, complete result and future-use
interface reach the actual consumer. The standard collection/constraint
owner can only receive an implementation lease after those rules and maps are
available and independently accepted. These are evidence requests, not a
lease or permission to write those owners.

**Falsifier of this boundary:** produce from already adopted rules and current
source constructors a complete ordinary Apply derivation whose premises map to
the standard collection and actual `ExecuteCallable` consumer, retaining every
item above without a new semantic choice or source restriction. A candidate
equation, a green test, a retained pending row, a `Gen-Call-0`-only special
case, or a proposed new rule does not falsify the boundary.

## Provisional bridge proposal (not adopted)

For Luna's independent semantic/source review, the smallest proof-motivated
bridge worth checking is an evidence-only rule schema over an already derived
original complete Call:

```text
e : authentic ordinary source Apply at (B,X,xi,Delta), with its exact callee,
    argument, scope, parent/child incidence, and source result origin
Q_e : authentic complete original Call for that same occurrence and tuple
SpecCall_e : Q_e unfolds to the original complete Call operation
C0_e : independent complete typing of Q_e's whole unchanged interface
IF_e : source interface/owner formation at the same occurrence and tuple
Adm_e : the independently justified context, provider/entry/role, whole
        argument carrier, admission/license, complete output, and future maps
--------------------------------------------------------------------------
Ordinary-Apply-Call-Bridge
typedApply_e : original typed Apply/Call derivation retaining Q_e, SpecCall_e,
               C0_e, IF_e, Adm_e and all original dependent indices
```

Every premise above is independent and must be supplied by its existing rule
owner; this schema does not claim any is currently derivable. `e` is identity
evidence only, not a replacement for `Q_e` or `IF_e`. A source `Gen-Call-0`
record can satisfy `Q_e` only where the original formation rule already
applies. This schema adds no direct-Use shortcut, endpoint-only admission,
Group-transparent typing, inferred callability, or generation-time solving.
It supplements any already valid original Call derivations and preserves every
existing source case; it does not assert universal applicability or restrict
the original domain. Whether the full source judgment itself is a new adopted
case remains an authority/review question, not a conclusion of this packet.

**Potential reversible engineering route if reviewed and authorized:** retain
an occurrence-keyed, default-off bridge record beside the existing pending
Apply inventory, populated only from an actual `typedApply_e` derivation; pass
the exact tuple to a separately leased complete-Call consumer adapter. Until
that producer exists, the record cannot be populated and standard
`collect_mode(..., false)` must keep its current Error/diagnostic and
`ApplicationTypingRuleUnresolved` behavior. Removing the bridge record/adapter
would restore the current behavior because neither becomes a source of
constraints or a semantic acceptance path. This is only a rollback shape, not
an implementation authorization or claim that a provisional probe is needed.
If independent review confirms that the record merely transports an already
derived original judgment and cannot affect acceptance, diagnostics, source
domain or parent quantifiers, the reversible record is recommended for
adoption under rev2's default-to-adopt direction. The source rule schema still
needs its owning original-rule evidence; this recommendation does not adopt
missing semantic premises by naming them.

**Falsifier for this proposal:** an independently reviewed source derivation
shows that `Q_e`, `IF_e`, admission or a dependent output/future map is either
not required by the governing original Call rule or cannot be formed for a
source instance already admitted by current rules. The former rejects this
schema; the latter leaves the exact source-owner gap open and blocks code. A
code path that drops any displayed premise also falsifies correspondence.

## Status

This is a source-evidence contract, not an implementation plan or theorem
claim. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
**OPEN / closure 0**. No test, build, compiler execution, or Git action was
performed. Independent review is pending; the author does not certify this
audit. See the frozen handoff for direct source hashes, checks, budget and
write-stop evidence.
