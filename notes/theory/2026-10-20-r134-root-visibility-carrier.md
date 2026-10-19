# R134: admitted root visibility and the retained source carrier

Status: candidate source-based rejection derivation and conditional repair invariant. No implemented postimage, independent certification, inference acceptance, runtime completion, parent closure or production authority.

Contract: `tasks/agent-loop/sprints/root-visibility-carrier-20261020-r134-rev2.md`, revision 2, primary-supplied SHA-256 `135efff25bc666458bb6310605f5ee0002f4eeafeaff5e3a662c4e2258683e72`. Sole author/runtime identity `/root/r132_ordinary_proof`, new exact assignment from Luna `/root`; requested Sol/high, observed model/effort UNKNOWN/UNKNOWN, numeric session ID and R134 baseline UNKNOWN. Cap 420 seconds. The assignment forbids commands; the primary supplied the current-source excerpts, exact active route/root, source hashes and proposed delta. This note's current-source claims are conditional on that supplied receipt, not a fresh file read or inner-call runtime trace by this author.

## Fixed source and exact rejection

The witness is the unchanged R133 identity projection: 210 bytes, SHA-256 `b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f`, external sample lines 46-53 with two trailing LF bytes:

```yu
// one generalized function used at three types
my identity x = x
our int_identity = identity 7
our bool_identity = identity true
our string_identity = identity "ok"
int_identity
bool_identity
string_identity

```

The primary's current excerpts establish these separate routes:

1. The active `lower_module_with_local_source` sets `counters.local_source = true`, then calls `lower_module_with_counters`. Root plans are processed in original source order.
2. For an admitted binding under that flag, `lower_plan` calls `local_source::form` directly.
3. In `form`, an admitted root obtains its body from `body(&plan.node)`. This is where the current MyKw-only guard applies.
4. The later ordinary carrier route `form_ordinary -> form -> body` is distinct. `ordinary_source_carriers` is false by default for this entrypoint, so that wrapper is not the active call path responsible for this fixture's failure.

`module.rs::plain_binding_header` admits the visibility tokens as MyKw -> Private, OurKw -> Our, PubKw -> Public. At the current `local_source::body` header guard only MyKw passes. Consequently an admitted Our or Public root has a source-body visibility disagreement between the admission owner and the carrier extractor.

The first binding is `my identity x = x`; its MyKw passes this guard. The next binding, `our int_identity = identity 7`, is admitted with Our visibility but its OurKw fails the MyKw-only body guard. It is the **first rejected root on this exact source route**, not a rejected identity callee, a FreshUse error, a solver conflict or an evaluator failure. The following Our roots encounter the same guard only if processing reaches them; they are not claimed observed failures.

The primary reports the existing failed smoke at line 43, first selected int_identity run, with `candidate lowering unavailable: StructuralProjection`. The supplied route maps the unsupported body failure through `lower_plan` to StructuralProjection, then `prepare` wraps it before `CandidateInference::solve`. The displayed error alone does not identify the root; source order plus the supplied actual guard/call route does. No runtime stack through inner source constructors was captured or replayed here.

This falsifies an unconditional claim that the present entrypoint successfully forms this exact fixture. It does not refute R133's explicitly conditional identity behavior: R133 required successful authentic carrier construction, and this is the failed prerequisite and its owning symbols.

## Root-only repair contract

The approved proposed delta is to pass the **already admitted HirVisibility** into root-only body extraction, and require the actual header token to match it exactly. It keeps the same BindingBody child, original header, visibility, parameters, source identities and root schedule. It keeps Builder::block's explicit `visibility != Private` rejection before private body extraction. It changes no import/export/lookup or inference semantics.

Write the required match relation as:

| Admitted root visibility v | Required first header token k |
| --- | --- |
| Private | MyKw |
| Our | OurKw |
| Public | PubKw |

This table is a proof description of the existing admission relation and proposed exact check, not a new language rule or a replacement parser. No wildcard or mismatched pair is allowed. Other malformed body/header checks remain in place. The root caller supplies v from its actual admitted binding; a guessed visibility or unrelated header is not a valid premise.

### Conditional lemma and proof

Fix one original admitted root plan P with its original syntax node n, definition/root identity d, parameter vector p, visibility v, and actual BindingBody child B. Assume the existing admission is authentic and successful, so the header token k of n satisfies the table for v. Assume the implementation changes only the root visibility-check path as contracted and retains the existing body/parameter/source construction.

Then:

1. **Visibility agreement.** The new root check accepts exactly the header token already licensed by admission. MyKw/Private takes the old accepted branch. OurKw/Our and PubKw/Public remove the identified extractor disagreement. The check never accepts an inconsistent visibility/token pair.
2. **Body preservation.** After that check, body extraction selects the same original BindingBody child B with all other structural checks unchanged. The proof does not replace B, erase an annotation, reparse a synthesized statement or alter source bytes. Passing the visibility gate alone does not imply every later structural check succeeds.
3. **Identity and parameter preservation.** The root constructor continues with the same original P,n,d,p and B. Visibility is a checked input to extraction, not an identity allocator, parameter rewrite, namespace update or new root constructor. Thus the original root source key, definition identity, admitted parameter identities/annotations, retained Lambda ownership, occurrence allocation/order and body-source linkage follow the same existing construction after the gate. Existing My roots have the same successful path; newly admitted carrier results retain their own original identities. This is not an assertion that different source programs or changed visibility tokens have equal source IDs.
4. **Schedule preservation.** The module processes the same original root plans in the same order and publishes no synthetic root. The proposed check changes neither the source schedule nor the distinction between binding roots and expression roots. This is structural source-order preservation, not a proof that inference/evaluation completes after repair.

Proof is case analysis on the three admitted visibility cases followed by the unchanged constructor suffix. For Private, the required token is precisely the old MyKw. For Our and Public, exact matching accepts their existing admission tokens while preserving the suffix's original inputs. An inconsistent token fails before the suffix. None of these cases introduces another source judgment or changes the algorithm's constraints, levels, extrusion, qualifying intrusion or generalization.

### Local restriction remains independent

Builder::block first calls `plain_binding_header` and rejects every visibility except Private **before** its call to private body extraction. Therefore:

- a nested MyKw binding continues through the old Private/MyKw body rule;
- nested OurKw and PubKw remain rejected by the existing local visibility guard;
- root-only extraction must not be substituted at the block/private-initializer callers or be allowed to bypass that guard.

The proof uses this actual upstream Private check, not a claim that a more permissive shared helper alone protects local source. Any change that removes/reorders this guard, redirects locals to an unguarded root extractor, or relaxes mismatched/malformed headers falls outside the proved delta and requires Luna before writing. Root visibility and local admission remain separate authorities.

## Source/native and parent application

The present failed prefix ends at source-carrier extraction, **before native candidate constraints or scheme/FreshUse routing exist for the complete witness**. R133's literal/Apply/Lambda constraint, per-use map and selected runtime observations cannot be cited as executed evidence across this failure. After the exact root repair, those remain conditional downstream obligations, not automatic consequences of an accepted header.

The direct parent application is concrete: R133's missing constructor-success premise is now localized to `lower_plan -> local_source::form -> body`, first at Our int_identity, and the proposed check has an explicit preservation argument. This removes the need to investigate FreshUse or runtime caching to explain this error. It does not establish actual repaired carrier publication, conflict-free identity admission or any of the three requested results; those still require the frozen postimage review and authorized finite checks.

R64-SRC-ANN-ARG-1 and R65-CURRENT-OPERAND-1 retain their original annotated computation-formal, whole-ascription p_A, joint-context/prior-evidence obligations and remain OPEN. Their My root visibility never supplied those typed premises. Original every-finite-prefix/shared-assignment and repeated/live-entry quantifiers, F1/FK1 and foreign continuations remain untouched. Simple-sub A/B, all hygiene/source-law, R85/R99, adoption and production gates remain OPEN. No permissions/providers/witnesses or original/copy lineages are identified by this extraction lemma.

Reused R133 work is limited to its exact source projection, conditional constructor-success premise and downstream owner inventory. Its current source hashes are inherited conditionally through the primary receipt. R133 is a candidate authored by this same worker, so it cannot independently certify this result. R132 countdown and ordinary-runtime arguments do not explain or repair this earlier source rejection. Historical tests and failures remain evidence only at their actual entrypoints/premises.

## Mutual TODO and falsifiers

**R134-ROOT-VISIBILITY-DELTA-1**, owner Luna/implementation: implement only the admitted-root visibility parameter and exact token match, leaving private local extraction/guard and the original constructor suffix unchanged. Required review evidence: actual postimage shows the active lower_plan root path receives its own admitted visibility; the same BindingBody child, root/source/parameter identities and schedules flow onward; local Our/Pub and mismatched root headers remain rejected. Falsifier: the first root/active-route explanation is wrong; a shared-helper relaxation bypasses local Private; body/params/identity/order change; malformed or mismatched headers pass; imports/exports/lookup semantics change; any extra owner change is needed. This leaf requests no production edit and claims no implementation postimage.

**R133-CONSTRUCTOR-THEN-CONSUMER-1**, owner Luna/verification: after reviewed repair, obtain actual unchanged-fixture carrier/constraint/admission and selected-result evidence through the authorized entrypoint. A later failure belongs to its actual owner and is not hidden by this lemma. Any continued StructuralProjection must be localized anew; success at header extraction does not certify FreshUse, native admission or runtime values.

Proof artifact and the one handoff are the only writes. Source/dependency hashes, author/runtime receipt, finite resource accounting and frozen content hashes are in `tasks/agent-loop/inbox/20261020-r134-proof.md`. No commands, local file reads, compiler/tests/builds/formatter/CLI/Git, implementation edits, external contact, scratch paths or descendants. STOPPED / WRITES_STOPPED / NO_DESCENDANTS at frozen handoff; fresh independent review belongs to Luna.
