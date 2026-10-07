#!/usr/bin/env python3
"""Validate/render the successor obligation ledger; this is not a proof checker.

The data is the primary's deduplicated audit. Edges describe the named sufficient
proof route. CLOSED means only the stated scope; conditional premises are never
inferred from this graph, a passing finite checker, or a solved source example.
Run --write to regenerate the two navigation artifacts, otherwise check them.
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "6fb5d7f697d5d592e0a39532ddb4967b54e18090"
REVALIDATED = "269fdca64dbd4c1b971d5d59eaa3f558f221aefa"
STATUSES = {
    "CLOSED", "CONDITIONAL-CLOSED", "IMPLEMENTATION-ONLY", "OPEN-PROOF",
    "OPEN-SEMANTIC", "BLOCKED-BY-USER-DECISION",
}
REFS = {
    "attack4": "notes/progress/2026-10-07-successor-frontier-attack4.md",
    "charter": "notes/design/2026-09-29-scc-intrusion-redesign-charter.md",
    "direction": "notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md",
    "fview": "notes/design/2026-10-05-inferred-function-call-views.md",
    "nested": "notes/design/2026-10-06-nested-block-function-source-realization-addendum.md",
    "compat": "notes/design/2026-10-03-concrete-compatibility-boundary.md",
    "core": "notes/design/2026-10-02-typed-computation-core-elaboration.md",
    "boundary": "notes/design/2026-10-02-typed-boundary-realization-draft.md",
    "source": "notes/design/2026-10-05-source-contracts-and-common-allowance.md",
    "adequacy": "notes/design/2026-10-02-source-interface-adequacy-theorem.md",
    "ordinary": "notes/design/2026-10-02-ordinary-computation-semantics-package.md",
    "fmp": "notes/design/2026-10-04-structural-fmp-fence-completion.md",
    "puredec": "notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md",
    "scoped": "notes/design/2026-10-03-scoped-constraint-solving.md",
    "contexts": "notes/design/2026-10-03-source-context-finite-closure.md",
    "residual": "notes/design/2026-10-03-open-residual-factorization.md",
    "phi": "notes/progress/2026-10-05-residual-admission-source-premise-audit.md",
    "common": "notes/design/2026-10-04-common-allowance-context-preimage.md",
    "use": "notes/design/2026-10-04-certified-callback-and-constrained-use.md",
    "coverage": "notes/design/2026-10-05-callback-coverage-and-source-joins.md",
    "dirproof": "notes/progress/2026-10-06-directional-joint-source-judgment.md",
    "drel": "notes/progress/2026-10-06-directional-full-relation-and-gate-delta.md",
    "sv": "notes/progress/2026-10-06-directional-source-view-instantiation-construction.md",
    "svcompose": "notes/progress/2026-10-07-source-view-to-original-attachment-composition.md",
    "attachattack": "notes/progress/2026-10-07-attachment-coverage-adversarial-attempt.md",
    "assocctor": "notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md",
    "associnvert": "notes/progress/2026-10-07-original-association-inversion-attack.md",
    "assockernel": "notes/progress/2026-10-07-original-association-source-kernel-audit.md",
    "rs": "notes/progress/2026-10-06-directional-recursive-generalization-supplier.md",
    "k": "notes/progress/2026-10-06-recursive-source-validation-construction.md",
    "qrmap": "notes/progress/2026-10-09-qr-capture-map-identity-theorem.md",
    "sourceuseqr": "notes/progress/2026-10-09-shadow-source-use-current-qr-crosswalk.md",
    "pg": "notes/progress/2026-10-06-source-generalization-eligibility-attack.md",
    "profile": "notes/progress/2026-10-06-source-profile-admission-construction.md",
    "init": "notes/progress/2026-10-06-independent-initial-admission-construction.md",
    "call": "notes/progress/2026-10-06-source-call-generation-construction.md",
    "assoc": "notes/progress/2026-10-06-attach-law-construction-attempt.md",
    "lic": "notes/progress/2026-10-06-attach-c-licensing-inversion-falsification.md",
    "sig": "notes/progress/2026-10-06-original-signature-constructor-derivation.md",
    "s22": "notes/progress/2026-10-06-section22-guard-authority-closure.md",
    "mixedrole": "notes/progress/2026-10-06-source-formal-relation-mixed-use-falsification.md",
    "event": "notes/progress/2026-10-06-directional-event-output-link-construction.md",
    "mixed": "notes/progress/2026-10-06-function-mixed-effect-production-correspondence.md",
    "state": "notes/progress/2026-10-04-local-state-capture-observation.md",
    "multishot": "notes/progress/2026-10-05-local-state-multishot-playground.md",
    "optiona": "questions/2026-10-05-production-function-denotation/approved-answer.md",
    "option2": "questions/2026-10-05-production-function-bound-membership/approved-answer.md",
    "inlet": "questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md",
    "release": "questions/2026-10-05-handler-protection-release-crossing/approved-answer.md",
    "rebuild": "notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md",
    "lifecycle": "notes/progress/2026-10-05-scc-generalized-boundary-contract.md",
    "newrec": "notes/progress/2026-10-07-successor-recursive-synthesis.md",
    "recdreflection": "notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md",
    "recbridge": "notes/progress/2026-10-07-rec-desc-observation-finite-bridge.md",
    "reclookup": "notes/progress/2026-10-07-rec-desc-captured-name-lookup-stop.md",
    "newassoc": "notes/progress/2026-10-07-successor-source-association-falsification.md",
    "newglobal": "notes/progress/2026-10-07-successor-global-synthesis.md",
    "review": "notes/progress/2026-10-07-successor-full-attack-review.md",
    "sound3": "notes/progress/2026-10-07-sound-publication-synthesis-round3.md",
    "operandcandidate": "notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md",
    "shadowinit3": "notes/progress/2026-10-07-shadow-initialization-retention-round3.md",
    "shadowexecq1": "notes/progress/2026-10-07-shadow-exec-self-q1-boundary.md",
    "freshcapture": "notes/progress/2026-10-07-shadow-current-qr-freshening-capture.md",
    "legacycrosswalk": "notes/progress/2026-10-07-shadow-legacy-call-solver-crosswalk.md",
    "argframe": "notes/progress/2026-10-07-shadow-calltype-argframe-marker.md",
    "oraclestate": "notes/progress/2026-10-07-frozen-oracle-state-frame-mechanism.md",
    "initworldw0": "notes/progress/2026-10-07-shadow-calltype-argframe-marker.md",
    "argframeconstruct": "notes/progress/2026-10-07-shadow-calltype-argframe-marker.md",
    "frameleaf": "notes/progress/2026-10-07-calltype-captured-env-frame-leaf.md",
    "fiber4": "notes/progress/2026-10-09-original-call-fiber-construction-round4.md",
    "incidence4": "notes/progress/2026-10-09-original-call-fiber-adversarial-round4.md",
    "ownerpair": "notes/progress/2026-10-09-original-kowner-underdetermination-round1.md",
    "assocconstruct5": "notes/progress/2026-10-07-original-association-constructive-round5.md",
    "assocorder5": "notes/progress/2026-10-07-original-association-adversarial-round5.md",
    "producerchronology": "notes/progress/2026-10-07-original-association-current-producer-crosswalk-round1.md",
    "importaction1": "notes/progress/2026-10-07-world-open-import-action-round1.md",
    "aggregate3": "notes/progress/2026-10-07-aggregate-obligation-attack-round3.md",
    "round3review": "notes/progress/2026-10-07-successor-round3-review.md",
    "principal3": "notes/progress/2026-10-07-actual-export-synthesis-round3.md",
    "resultbridge": "notes/progress/2026-10-07-all-view-result-checking-bridge.md",
    "call3": "notes/progress/2026-10-07-call-original-rule-round3.md",
    "world3": "notes/progress/2026-10-07-world-recursive-rule-round3.md",
    "selfinit": "notes/design/2026-10-07-recursive-self-init-executable-boundary.md",
    "selfproof3": "notes/progress/2026-10-07-self-init-and-conformance-round3.md",
    "selfanswer": "questions/2026-10-07-recursive-self-initialization/approved-answer.md",
    "selfreceipt": "questions/2026-10-07-recursive-self-initialization/receipt.md",
    "round2review": "notes/progress/2026-10-07-successor-round2-review.md",
    "kernel2": "notes/progress/2026-10-07-successor-original-kernel-construction-round2.md",
    "coind2": "notes/progress/2026-10-07-successor-recursive-coinduction-round2.md",
    "projection2": "notes/progress/2026-10-07-successor-effective-projection-round2.md",
    "ctxpacket": "notes/progress/2026-10-07-ctx-finite-sealed-packet-boundary.md",
    "alphaimpl": "notes/progress/2026-10-07-shadow-interface-alpha-round2.md",
    "orbitimpl": "notes/progress/2026-10-07-shadow-atom-orbits-round2.md",
    "livedrain": "notes/progress/2026-10-06-bounded-live-closure-work-count.md",
    "solveduse": "notes/progress/2026-10-07-shadow-solved-application-use-retention.md",
    "applycross": "notes/progress/2026-10-08-shadow-apply-endpoint-crosswalk.md",
    "headerjoin": "notes/progress/2026-10-07-shadow-annotation-header-membership.md",
    "sccendpoints": "notes/progress/2026-10-07-shadow-scc-use-definition-endpoints.md",
    "sccoutgoing": "notes/progress/2026-10-07-shadow-scc-outgoing-use-view.md",
    "pendinguse": "notes/progress/2026-10-08-shadow-pending-use-instantiation.md",
    "localbind": "notes/progress/2026-10-09-shadow-local-binding-source-identity.md",
    "callscheme": "notes/progress/2026-10-07-shadow-call-current-scheme-boundary.md",
    "shadow": "crates/yu-core/src/shadow_typed_evidence.rs",
    "shadowtest": "crates/yu-core/tests/shadow_typed_evidence.rs",
    "shadowhir": "crates/yu-hir/src/shadow.rs",
    "shadowcore": "crates/yu-core/src/shadow_derivation.rs",
    "owner": "notes/progress/2026-10-06-shadow-call-parameter-declaration-owner.md",
    "retention": "notes/progress/2026-10-07-shadow-nested-unary-retention.md",
    "bindergroups": "notes/progress/2026-10-07-shadow-pending-binder-use-groups.md",
    "sourceuses": "notes/progress/2026-10-07-shadow-retained-source-use-groups.md",
    "solver": "crates/yu-solver/src/lib.rs",
    "hir": "crates/yu-hir/src/lib.rs",
    "oracle": "notes/progress/2026-10-06-frozen-oracle-presolve-application-types.md",
}
NODES: list[dict] = []
MANUAL_CLOSED_LEMMAS: dict[str, list[str]] = {}


def n(key, status, title, requires, premises, result, refs, authority="required-before-cutover", closed=()):
    NODES.append(dict(id=key, status=status, gate=title, requires=requires.split(),
                      premises=premises, minimal_lemma_or_closed_scope=result,
                      references=refs.split(), production_authority=authority))
    if closed:
        MANUAL_CLOSED_LEMMAS[key] = list(closed)


# Existing reviewed lemmas are retained at their exact scopes.
n("FMP", "CLOSED", "Pure structural arbitrary-tree to regular witness", "",
  "Normalized pure fragment, rigid permissions, exact recursive descriptor and mandatory records; no arbitrary Phi/effect/optional-Record predicate.",
  "Regular witness exists with the reviewed 8^N bound. Retire selector/one-anchor subtargets as prerequisites of this theorem.", "fmp")
n("PURE_DEC", "CLOSED", "Effective decision for the pure finite input", "FMP",
  "Finite head/label/atom alphabet and decidable rigid permission queries.",
  "Bounded regular-graph enumeration is sound and complete only for the FMP fragment.", "puredec")
n("EQ_RES", "CONDITIONAL-CLOSED", "Scoped equality and retained-residual factorization", "",
  "Independently interpreted predicates, fixed scopes and finite canonical contexts; contractive structural cycles.",
  "Equality quotient/relative MGU and unchanged residual preserve the exact joint relation. No flexible joint SAT/public projection theorem.", "scoped residual")
n("WHOLE_REL", "CONDITIONAL-CLOSED", "TD/FC and DREL-1 whole-relation preservation", "",
  "One original binder tree and full independently interpreted relation, including active protection predicates and recursive operators.",
  "Total derived coordinates, covered factorization and directional inlining preserve all unchanged queries on that same relation. Query success is not obtained.", "drel coverage")
n("DIR_LOCAL", "CLOSED", "Selected directional source seed and certified replay", "",
  "Selected unannotated source formal, seed-at-exposure and source upper occurrence; replay facts are already certified.",
  "S1/S2 generate protection at the upper output only; S3 removes physical delivery-order dependence. Existing provider protection remains; genuine later seed applicability is outside scope.", "direction dirproof")
n("SV", "CONDITIONAL-CLOSED", "Exact source receipt, actual rebind, capture and read", "",
  "Approved apply/step source, independently typed original invocation, one compatible original profile, original admission/response semantics.",
  "Prospective argument.result.(u,p0) at receipt; SourceViewInst only at actual Return/rebind; capture/read at reached transitions; Pending on suspension/divergence; finite original resumptions covered. Later composition ties that exact typed read incidence to the complete Call operand, without converting it to original static (s,c).", "nested sv svcompose")
n("RS_LX", "CONDITIONAL-CLOSED", "Actual-derivation provenance and lexical import supplier", "",
  "Finite actual rule-occurrence derivation and resolved binder ancestry, with retained semantic rule premises.",
  "Whole RS/RS-active/RS-use ledger and LX ownership/import map preserve source scopes, rigid captures and upper/lower direction. No semantic Generalize eligibility or discharge inferred.", "rs")
n("REC_K", "CLOSED", "Constructor-guarded immutable mutual provider knot", "",
  "Selected my f x = g; my g y = f source and its immutable constructor-guarded provider interpretation.",
  "K constructs the actual mutually captured providers without a validated member environment. Paired future histories and contract emission are separately conditional in REC_KV; unguarded initialization is outside scope.", "k")
n("REC_KV", "CONDITIONAL-CLOSED", "Paired recursive histories and same-provider contract schema", "REC_K",
  "KP has independently paired argument/context subrelations for future calls and raw resumptions; KV has independently interpreted original local and complete membership predicates.",
  "KP pairs finite prefixes/future calls on those inputs; KV emits the same-provider semantic contract conjunction. Neither constructs its independent predicates or proves the conjunction satisfied.", "k")
n("CALL_REL", "CONDITIONAL-CLOSED", "Source Call and complete invocation operand", "",
  "Original decorated Name/result/actual provider-entry/consumer interpretation on fixed X and xi; typing remains an independent predicate.",
  "Construct J_f >>= ExecuteCallable(actual_f,Delay(J_x)) with callee evaluation, receipt, entry Force/rebind if needed, body, consumer, return and retained pending suffix/current resumed state. New contribution naming is no separate gate.", "call source newassoc")
n("PCINIT", "CONDITIONAL-CLOSED", "Open-context structural initial/history schema", "",
  "Independent descriptor, profile, import/world, response and carrier interpretations.",
  "Source-owned initial puncture/receipt/entry schema and local inversion exist before solving; semantic validity and inhabitedness do not follow.", "init profile")
n("PG1", "CONDITIONAL-CLOSED", "Source projection endpoints and fixed captures", "",
  "Independently checked projection views at original scopes; only id source is unconditional surface coverage, Make/Relay braces remain conditional.",
  "Source-selected repeated endpoints and fixed pick capture reconstruct the whole kernel; actual Generalize and designated-export Direct remain.", "pg")
n("USE_GRAPH", "CONDITIONAL-CLOSED", "Certified ordinary fresh copy, graft and use query", "",
  "Complete source relation, legally eligible binders, fixed imports and retained Direct evidence grammar.",
  "Finite graph of the actual ordinary use exists. Retire a separate new m_V calculus, not the all-valid-view success sequent.", "use")
n("ALLOC_COMMON", "CONDITIONAL-CLOSED", "Selected common/all-view extension classes", "",
  "Guarantee-only, source-allocation or matched abstraction grammars and their original typing/admission assumptions.",
  "Reviewed A-extension/V_alloc and paired-grammar common/use results close only their declared classes; arbitrary legal public views remain outside.", "source common coverage")
n("TRANSPORT", "CONDITIONAL-CLOSED", "Indexed typed profile/D transport and live filtering", "",
  "Supplied original typed Flow, Observe, normalized Receive and exact boundary/owner/handler identities under one xi.",
  "Relational-image composition, identity, union distribution and candidate live-filter commutation; no new boundary, grant, K discharge or alias merge.", "boundary")
n("S22_DIRECT", "CLOSED", "Selected direct/derived guard consequences", "",
  "Source-certified introduction and an actually derived comparison; declared assumptions distinguished from new obligations.",
  "Forbidden variable comparison and selected kappa <: Int reject; uniform fixed-root specialization fails on an admitted counter-instance. Cartesian support K alone is insufficient. General insertion remains open.", "s22 charter")
n("REF_SIM", "CONDITIONAL-CLOSED", "Decorated source-reference complete-history realization", "",
  "Finite typed source derivations with independent complete descriptor/owner/world/local construction and admission certificates.",
  "Source/reference constructor simulations cover finite histories in both directions on the same tuple. This is not raw-source formation or Option 2 production completeness.", "core source adequacy")
n("REUSE", "CONDITIONAL-CLOSED", "Complete boundary substitution and rebuild lifecycle", "",
  "Complete equal simultaneous interfaces, unchanged external inputs, interface-only downstream observation, valid references and atomic publication.",
  "Downstream inference reuse is justified under these hypotheses. Reverse mutation of solver state is retired; complete producer and actual publication correspondence remain.", "rebuild lifecycle")
n("SC_ROLE", "CONDITIONAL-CLOSED", "Selected completed-source DREL-2 role substitution", "",
  "Exact completed apply f x = f x source entails rho_f=NonHandlerFormal at the original root and retains every original kernel.",
  "Entailed substitution preserves the whole relation and provider/result packets. No generic mixed-use selection or replacement-kernel equivalence.", "rs mixedrole")
n("FH", "CONDITIONAL-CLOSED", "Simultaneous finite-history local invariant", "REC_K",
  "Fixed original scoped (xi,w); initial W and every transition/member check pointwise there; new event witnesses are compatible scope-authorized extensions, including siblings; exhaustive admission cases.",
  "Induction on finite derivation size preserves W/local checks for both actual members without an already validated CompleteMem environment. Does not construct local certificates or derive ordinary DescMem.", "newrec review")
n("CI_ALPHA", "CLOSED", "Decidable alpha-isomorphism of supplied finite interfaces", "",
  "Finite complete faithfully serialized typed presentation; finite sort/scope/binder preserving renamings with rigid identities fixed.",
  "Enumerate all allowed renamings and minimize full encoding. Equal minima iff finite presentations are alpha-isomorphic, including cycles. Reviewed default-off Rust now implements the supplied-record slice with inverse certificates and explicit node/candidate exhaustion. Complete actual interface generation and semantic equivalence are not certified.", "newrec review alphaimpl round2review")
n("CI_USE", "CONDITIONAL-CLOSED", "Alpha-equal interface preserves arbitrary finite joint fresh uses", "CI_ALPHA",
  "Independent equivariance/covariance for every primitive/admission/constructor/evidence/recursive/query operation; complete identity-observer accounting; original and client coordinates rigid.",
  "Operator conjugacy and coherent (use,local) renaming preserve/refelect the whole jointly constrained finite use family and unchanged Direct queries. No all-view query existence or source interface producer.", "newrec review")
n("PATH_QUERY", "CONDITIONAL-CLOSED", "Finite supplied typed Path/Inc query", "TRANSPORT",
  "Caller-supplied finite typed graph and normalized receipt endpoints, canonical nonzero-sized identity tokens, one original context, exact current activation sets.",
  "Finite reachability and the exact same-event/same-view owner join plus current handler/owner/original-receiver activity filter are implemented, focused-tested and independently reviewed after the event-token and zero-sized-witness repairs. Source facts, normalized receipt correspondence, canonical identities and activity sets remain supplied premises; grant, release, handler selection and source-wide completeness are outside scope.", "shadow shadowtest review", "shadow-only; no production authority")

# Atomic open judgments: no large completed-profile or validated-environment placeholder.
n("SEED_SOURCE", "OPEN-PROOF", "Directional applicability over all source introductions/uses", "DIR_LOCAL RS_LX",
  "Current directional policy; exact original source variable, exposure, output occurrence and provenance.",
  "For each admitted formal/import/annotation/generalized and computed use, derive ProtectedVarAt at that exposure and complete upper-use occurrence; prove late applicability rather than replaying final component membership.", "direction dirproof fview")
n("INTRO", "OPEN-SEMANTIC", "Semantic introduction classification and source-coordinate realization", "RS_LX S22_DIRECT",
  "Actual source derivation; original binder tree, lexical identities and declared request assumptions.",
  "Map each actual generated/instantiated coordinate to ordinary flexible, inference existential or rigid opened binder with its introduction scope and same-origin dependencies; Name copying alone never reclassifies it.", "s22 rs charter")
n("GUARD_INSERT", "OPEN-PROOF", "Origin-relative oriented insertion preservation", "INTRO S22_DIRECT PRIMITIVES",
  "Original permission relation P, fixed caller tuple/fresh instance and actual directed bound B(z)<:v; no equality cast.",
  "At v=z,c,R_h prove P_before iff P_after on original incoming constraints, or derive required rejection before commit. Distinguish dependent interface transport from specialization; do not invent z<:c from support.", "s22")
n("GUARD_TERMINAL", "OPEN-SEMANTIC", "Source meaning of terminal Top and declared bounds", "INTRO DESC_CLAUSES",
  "The actual z<:Top terminal and original uniform permission relation, with declared assumption/new obligation provenance.",
  "Give the selected terminal a source non-refinement certificate or required rejection. Legacy terminal success, empty support and constructor levels supply none.", "s22 compat")
n("GUARD_COVER", "OPEN-PROOF", "Every derived comparison re-enters its original guard", "GUARD_INSERT GUARD_TERMINAL",
  "All actual structural decomposition, replay, aliases, opening/grafting and extrusion rules with retained origins.",
  "For each child comparison derive its source/guard context and preserve original permissions, including ground narrowing; prove exhaustive generation and no unchecked derived route.", "charter contexts s22")
n("DESC_CLAUSES", "OPEN-SEMANTIC", "Complete ordinary descriptor and local constructor clauses", "CALL_REL SIG_RULES PRIMITIVES",
  "Existing ordinary Return/Request/Bind/Call equations and structural type clauses are retained; original profile, world and admission predicates may occur by their declared names.",
  "Specify the missing exhaustive DescMem_R(o;xi,W), whole CarrierMem and local constructor clauses, including returned recursive Function handles, original role/entry/consumer/authority and all future eliminations. Independently supply CalRet, including current-world and latent/future returned-provider facts; DelayIntro for the whole inert carrier; Phase_r for every actual receipt, entry, body/native, designated-consumer and return phase, with exhaustive finite/zero-step prefixes and future developments; and BindTyped for the complete ordered pending suffix at every admitted response/current state and returned-provider future use. Construct CI-Operands joint captured-environment/provider/current-world and both operand typing facts; CI-Bind every original ordered interface; CI-ArgFrame for every retained CalRet witness, preserving its evidence while jointly extending argument typing at the actual returned C1 and ArgCompatible with that actual provider (C0 typing alone is insufficient); CI-Receipt the complete first independent receipt/authority inputs; and CI-StepFrame complete next-phase inputs and their incident Bind interfaces jointly at the actual current returned world. Keep one coherent original-scope evidence family, not separately selected existential worlds or witnesses; no bridge assumes whole invocation/Call membership. These are independent clause/instance obligations, not source-image membership or adoption of the displayed candidate laws; SEM_JOINT must justify their common interpretation.", "source core k call3 round3review operandcandidate")
n("ADMISSION_CLAUSES", "OPEN-SEMANTIC", "Independent source response/resume/future-admission clauses", "DESC_CLAUSES INIT_WORLD",
  "Original descriptor/world predicate specifications and approved all-compatible punctured-context domain, including direct and whole carrier holes.",
  "Specify exhaustive Init/Response/Resume/FutureUse clause operands: same raw handle/current store, typed response, actually returned provider, original receiver, and other bindings/import validity. Define no domain by successful Q or current-source reachability. This is clause formation, separate from history preservation/coverage.", "inlet source adequacy")
n("SEM_JOINT", "OPEN-PROOF", "Joint independent interpretation of descriptor/world/admission clauses", "DESC_CLAUSES ADMISSION_CLAUSES INIT_WORLD",
  "Complete original clause specifications and their original scopes/quantifiers; mutually referencing predicates remain one semantic family.",
  "Construct a common independently justified interpretation of descriptor, carrier, world, local constructor and admission predicates satisfying every clause, with any required guarded/step-indexed or other realization proof. Independently supply CalRet, including current-world and latent/future returned-provider facts; DelayIntro for the whole inert carrier; Phase_r for every actual receipt, entry, body/native, designated-consumer and return phase, with exhaustive finite/zero-step prefixes and future developments; and BindTyped for the complete ordered pending suffix at every admitted response/current state and returned-provider future use. Construct CI-Operands joint captured-environment/provider/current-world and both operand typing facts; CI-Bind every original ordered interface; CI-ArgFrame for every retained CalRet witness, preserving its evidence while jointly extending argument typing at the actual returned C1 and ArgCompatible with that actual provider (C0 typing alone is insufficient); CI-Receipt the complete first independent receipt/authority inputs; and CI-StepFrame complete next-phase inputs and their incident Bind interfaces jointly at the actual current returned world. Keep one coherent original-scope evidence family, not separately selected existential worlds or witnesses; no bridge assumes whole invocation/Call membership. Their actual source/world instances remain unproved. Do not pick per-node predicates, define membership as source image, or assume a greatest fixed point. This interprets definitions and constructs law inputs; it does not establish source-world inhabitance, attachment, licensing or profile assembly. The open-import clauses must justify their actual original-incidence action, fixed-interpretation identification and joint importer root extension. Transporting only the image of a generic relation is not preservation of that independently fixed semantic family.", "source compat newrec newglobal call3 round3review operandcandidate importaction1")
n("REC_DESC", "OPEN-PROOF", "Independent recursive descriptor introduction", "REC_K FH SEM_JOINT",
  "Fix the actual provider, original descriptor, and original scoped (xi,w); independently define DescMem and the query-independent admission domain. Establish semantic adequacy of each captured Name lookup at that same scope/assignment as a static/root premise or a complete local check; Gamma identity alone is insufficient. Keep actual latent Return handles, current resumed state, pending suffix, and compatible event-local assignments. Never define DescMem as source-image membership or use it to admit its own failure witness.",
  "For the listed FH route, prove exact finite-failure reflection at the original scoped (xi,w), including static/zero-step checks, captured lookup, actual returned handles and all independent future admissions. If FH is forall h exists e. L(h,e), failure must yield exists h forall e. not L(h,e); one failing extension is insufficient. Alternatively derive the ordinary two-closure introduction for the actual K certificate, with all inlet/world/static checks and original shared witnesses, without assuming opposite member validity. Unfolding D=F(D) and postfixedness do not prove absorption, even for F(Z)_f=Z_g,F(Z)_g=Z_f. This alternative replaces the descriptor proof method only; neither route supplies M_E, carrier/world or CompleteMem discharge. The reviewed own-member dependency cut requires auditing every actual world/lookup premise: K lookup identity supplies no ordinary readout, and a world implying d_f/d_g cannot be assumed to introduce them. The restricted simultaneous alternative must expose the independent external/current base, actual K/provisional interfaces, exhaustive ordinary local clause instances, all nonrecursive guards and original CompleteMem conjuncts, and a proved ordinary cyclic Return acceptance theorem for only the exposed latent occurrences. Operational Return/lookup progress supplies no such theorem; its source-root/world conclusions remain unproved, and the independent inlet/world domains and original witness scopes are retained.", "newrec k source recdreflection recbridge reclookup coind2 round2review world3 round3review attack4")
n("REC_LOCAL", "OPEN-PROOF", "Actual pointwise simultaneous local member certificates", "SEM_JOINT INTRO GUARD_COVER",
  "Same actual provider knot and original scoped (xi,w); the predicates are fixed by SEM_JOINT; this local theorem quantifies over every independently valid initial world without assuming such a world is inhabited.",
  "Construct actual receipt/entry/rebind/body/returned-handle local preservation checks and compatible event extensions pointwise for every member in the fixed independent admission domain. This is not initial-world existence or complete KV satisfaction; INIT_VALID and MEMBER_DISCHARGE are separate.", "newrec k core")
n("INIT_VALID", "OPEN-PROOF", "Actual initial world and environment realization", "SEM_JOINT INLET_CARRIER REC_LOCAL",
  "Original independent world/admission interpretation, actual source environment/imports and actual recursive knot, with local preservation laws rather than already validated member contracts.",
  "Construct the actual initial punctured-world/alias/environment witnesses at original scope and show Init/EnvStore/JointWF, including recursive captures where present. Derive this base without assuming completed member membership or defining admission by source-solution existence; returned-only/empty-world fixtures do not suffice. The exact source-root/import extension inputs must be constructed, including scalar cross-world installation and any hole-dependent open-import action. If an ordinary world premise entails own-member facts d_f/d_g, assuming that completed world merely relocates the recursive obligation: installed own-root validity is a simultaneous conclusion with ordinary member typing, not an already completed premise. Do not invent an EnvStore predicate by deleting unspecified conjuncts.", "init compat k world3 round3review")
n("MEMBER_DISCHARGE", "OPEN-PROOF", "Actual simultaneous recursive member/environment discharge", "REC_KV FH REC_DESC REC_LOCAL INIT_VALID",
  "Fixed common predicate interpretation, actual valid initial source world, all pointwise member/transition checks and compatible extensions at the original assignment.",
  "Combine independently proved ordinary descriptor introduction (the listed FH/reflection route or a sound actual two-closure rule) with every original KV/CompleteMem conjunct and simultaneous environment judgment on the same providers. Initial validity and compatible local/history witnesses must be actual, not separately chosen member worlds. The direct certificate changes no non-descriptor obligation. The reviewed minimum simultaneous source-root/world rule, if independently proved and instantiated, would conclude the selected pair's d_f/d_g, actual installed root-world validity, every original CompleteMem/KV conjunct and pointwise transition/lookup preservation jointly. Its external/current base excludes hidden own-member target assumptions; all ordinary local instances and nonrecursive guards plus latent cyclic Return acceptance remain open. The interface does not redefine EnvStore or infer broader all-world/history/Generalize coverage.", "newrec k core coind2 round2review world3 round3review")
n("REC_INIT_SELF", "CLOSED", "Approved exact singleton self-initialization executable boundary", "",
  "Validated q1/d1 approval at a814bc76aa107f2ffb7aae9cb2e2887c5b078792: exactly singleton original source my f = f, one simple binder, no parameters/annotation, entire RHS a direct Name resolving to that binder. No descriptor/world/member premise is assumed.",
  "The reviewed EXEC-SELF-Q1 rule and SELF-ENVELOPE/SELF-NOSTART/SELF-INFER/SELF-ADEQUACY proofs give deterministic rejection at executable acceptance before initialization or RHS self-read, preserve the existing F4 Never inference, and discharge this exact source-envelope inversion/no-start/source-adequacy subcase. Actual compiler enforcement remains an implementation obligation pending; this is no implementation claim or authority, no rule for other recursive initializers or general Never, and no production cutover.", "selfinit selfproof3 selfanswer selfreceipt round3review")
n("REC_INIT", "OPEN-SEMANTIC", "Recursive source initialization beyond guarded immutable closures", "REC_K REC_INIT_SELF",
  "Included recursive source forms and their initializer order/world access, distinct from lexical preallocation. The exact approved q1 singleton is excluded from execution with its F4 inference preserved; other forms are not thereby excluded.",
  "Specify source evaluation/admissibility for remaining non-constructor-guarded initializer classes, with concrete availability, read-before-initialization, re-entry, publication/order and incoming-world obligations. For another-member direct Name, independently establish inclusion/start before deciding its original InitRead outcome at the actual target/activation/availability/world; q1 supplies neither premise nor unavailable-target disposition. No allocator freshness or final scheme shape substitutes. Actual q1 compiler enforcement remains pending separately.", "k charter core selfinit selfproof3 round3review")
n("GENERALIZE", "OPEN-PROOF", "Semantic eligible view, binders and anchors", "PG1 RS_LX INTRO MEMBER_DISCHARGE",
  "Complete simultaneous source relation, fixed captured/import/non-generic/world coordinates, source-selected endpoints and original quantifier tree.",
  "Construct the generalized view and eligible binder placement satisfying complete admission/reflection and all authorized future instances; prove scope hiding/anchors and distinguish semantic eligibility from lexical locality.", "pg rs fview")
n("CALL_TYPE", "CONDITIONAL-CLOSED", "Independent complete Call constructor typing", "CALL_REL SEM_JOINT",
  "One fixed SEM_JOINT ordinary descriptor/carrier/provider-entry/consumer interpretation and original X/xi, universally over every independently admitted operand/world assignment. Independently supply CalRet, including current-world and latent/future returned-provider facts; DelayIntro for the whole inert carrier; Phase_r for every actual receipt, entry, body/native, designated-consumer and return phase, with exhaustive finite/zero-step prefixes and future developments; and BindTyped for the complete ordered pending suffix at every admitted response/current state and returned-provider future use. Construct CI-Operands joint captured-environment/provider/current-world and both operand typing facts; CI-Bind every original ordered interface; CI-ArgFrame for every retained CalRet witness, preserving its evidence while jointly extending argument typing at the actual returned C1 and ArgCompatible with that actual provider (C0 typing alone is insufficient); CI-Receipt the complete first independent receipt/authority inputs; and CI-StepFrame complete next-phase inputs and their incident Bind interfaces jointly at the actual current returned world. Keep one coherent original-scope evidence family, not separately selected existential worlds or witnesses; no bridge assumes whole invocation/Call membership.",
  "The repaired full conditional composition derives existing target typing of every complete output/pending Call observation from precisely these independent local laws and constructed-input bridge instances. Build the actual whole receiver suffix backwards through the original ordered Binds; callee Requests retain Delay/invocation before receipt, receiver Requests retain the remaining suffix without replaying receipt. All finite prefixes, current-state raw resumptions and future returned-provider uses retain the same scoped evidence family. No actual local law/input is instantiated, no assignment inhabitance or whole-source coverage is proved, and no original association, attachment, licensing, assembly or profile is inferred. On the fixed Name/Name cut, CI-Operands still needs independent joint Env/Name/Return introduction at C0; CI-ArgFrame then needs evidence-preserving joint argument typing and actual-provider carrier compatibility at returned C1. The bounded constructor audit derives only Gamma(x)=Value(Ax), Result(Value(Ax))=Comp(empty,Ax), and inert Return(lookup x). Its exact missing source head is the original argument-to-actual-provider whole-carrier checking certificate plus independently justified Name/Return typing, soundly and jointly realized at C1 for every retained CalRet witness; it yields neither Typed nor ArgCompatible from syntax, generated constraints, C1=C0, provider view or Q. The trace-local Name/Name cut further isolates `CapturedEnvFrame_x`: initial captured-binding adequacy and callee typing share one original CI-Operands witness, and the actual binding/reference/latent dependencies must remain adequate at each retained CalRet C1. Current-world adequacy and actual-provider whole-carrier compatibility are separate required inputs. Neither is derived by lexical identity or the emitted skeleton. This refines the premise without changing its semantics or status.", "source core newassoc call3 round3review operandcandidate attack4 argframeconstruct frameleaf")
n("SIG_RULES", "OPEN-SEMANTIC", "Exhaustive original signature licensing judgment", "SEED_SOURCE INTRO",
  "Original beta=(formal,root), typed positions, scope/binder/own-upper/inherited-provider arms; current direction fixed.",
  "Give comparison-independent original owner/contribution/incidence introductions and exhaustive licensing last-rule elimination, including own-upper, provider, annotation, mixed-use, certified transport, conservative-contract and reference origins. The reviewed candidate calculus reduces assembly to explicit K-Leaf/K-Image/K-Owner/K-Incidence and original licensing sequents; their original-domain validity and exhaustivity remain unproved. Slots and I_orig are not new labels or a chosen assembly image.", "sig profile lic fview kernel2 round2review")
n("ORIGINAL_ASSOC", "OPEN-SEMANTIC", "OriginalAssocType_X inhabited original source-owned fiber", "CALL_TYPE SIG_RULES",
  "Original I_orig(X), beta/p0/upper/exposure and complete F_C(X); same xi, original scopes/providers and contribution dependencies.",
  "Derive one original slot/contribution/incidence before the universal over the complete family: exists a in I_orig(X). forall z in F_C(X). Cover(a,z). The explicit OC-Call-Intro cut requires original contribution-domain closure under the full typed invocation image, static source-owner introduction and joint incidence coherence at the same beta,p0,upper,xi and scope. Complete whole-carrier inlet R_U_all is independent of the selected source diagonal Delay(Name_x). All original license witnesses survive; H_gen, H_typed, IDs and assembly-image replacement supply none of these introductions. P2 is the original OC-Owned-Image head: construct an original typed full-denotation preimage jointly incident at its original static owner/slot/path, retaining every local evidence arm; global contribution representability and an inhabited owner fiber separately are insufficient. At the approved captured Call, keep O0 original typed output/source-root correspondence, O1 original static owner introduction with actual seed-at-exposure, C0 complete independent typing over the full admitted inlet, C1 original contribution-domain preimage with witness-preserving embedding, and J0 joint source incidence/one uniform complete-family witness separate. An owner-first traversal imposes no global order on these independent branches. Even complete pairwise projections and disconnected retained license IDs cannot recover joint incidence: use an actual joint certificate or a proved witness-linked lossless decomposition. The bounded K-Owner pair audit establishes neither uniqueness nor two complete competing Authority-consistent semantics. P3 requires one actual original complete-family witness before observation choice and preservation of all licensed witnesses, including those outside any constructor image. All finite-observation assemblies, even with full evidence retention, do not imply it. A conditional alternative is finite-family coverage plus a finite quotient of semantic complete-coverage profiles on the fixed owned/typed fiber; finite Slots, a finite source graph or finite descriptor graph do not establish that quotient. Under a proved OC-Owned-Image with its original coverage elimination, separate arbitrary assembly becomes redundant only for that exact route. ATTACH and licensing remain independent open rule correspondences; provenance projection supplies no Attach_C/Lic_C derivation. Preserve the active original ordered source-to-contribution map, including pending suffix and raw-resumption interpretation at the same original occurrence/provider/scope dependencies; retained witness tokens, static operand order and unordered effect summaries alone do not certify it. C-realization specialization still consumes the original local owner/view member and cannot construct an inhabitant.", "assoc newassoc assocctor assockernel kernel2 round2review call3 round3review fiber4 incidence4 ownerpair assocconstruct5 assocorder5 producerchronology attack4")
n("ATTACH", "OPEN-PROOF", "Attach_C source constructor correspondence", "ORIGINAL_ASSOC",
  "The inhabited original fiber and exact source constructor/transport derivation, at the same X.",
  "Construct Attach_C using the original incidence witness and invert its source constructor, preserving all original arms/scopes and independently typed contribution; structural call/declaration labels are only locators.", "assoc newassoc")
n("LIC_FORWARD", "OPEN-PROOF", "Attachment implies original licensing", "ATTACH SIG_RULES",
  "Original licensing introduction clauses, rather than a fresh licensing predicate defined to mean Attach.",
  "For each actual Attach constructor derive Lic_C at identical original s,c,beta,p,X and retain every original dependency. No successful Q or endpoint shape premise.", "lic assoc")
n("LIC_INVERT", "OPEN-PROOF", "Exhaustive original licensing inversion", "SIG_RULES ATTACH",
  "All original licensing last rules, including own upper/inherited transport/generalized/annotated arms and conservative licensed contributions.",
  "Invert every original Lic_C witness to its licensed attachment/source-origin arm. Last-rule accounting must reach inside the independently interpreted owner/view kernel instead of stopping at its supplied primitive witness. Do not require a source execution for each Option 2 extra observation, erase static exposure because no event/return occurred, or assert Slots singleton from one exposure. The latest bounded attack found no original licensed-unattached witness.", "lic newassoc attachattack associnvert assockernel option2")
n("PROFILE", "OPEN-PROOF", "Complete original beta/Slots/profile construction and inversion", "LIC_FORWARD LIC_INVERT",
  "One jointly constrained original profile coordinate; all licensed incidences, policies and inherited tags on that same source relation.",
  "Assemble exactly the original licensed slot domain with well-typed positions/contributions and prove forward/backward coverage, preserving all dependencies and allowed slot sharing. Local mandatory p0 alone is insufficient.", "profile sig newglobal")
n("ROWS", "OPEN-PROOF", "Complete original typed-row nonemptiness", "PROFILE CALL_TYPE SEM_JOINT INIT_VALID MEMBER_DISCHARGE GENERALIZE ALL_WORLD",
  "Independently admitted source and all independent endpoint/role/entry/profile/continuation/import/world predicates at original scope; admission is not defined by J_S satisfiability.",
  "Construct one joint witness of J_S satisfying every original constraint. Separately nonempty fragments or quiet identity execution do not suffice; original universal world/history clauses stay universal.", "profile init newglobal")
n("MIXED_ROLE", "OPEN-SEMANTIC", "Whole-source mixed-use role refinement/aggregation", "SC_ROLE SEED_SOURCE",
  "Same source formal and original relation across Handler/internal/NonHandler uses; actual callable role/entry separately fixed.",
  "Specify independently justified complete-source role predicate and aggregate all use demands without erasing upper seeds/provider-owned protection or recombining incompatible marginal witnesses.", "mixedrole fview rs")
n("DREL2", "OPEN-PROOF", "Seed-to-refined primitive relation correspondence", "MIXED_ROLE PROFILE WHOLE_REL",
  "Independently interpreted seed and refined active kernels on the same whole X, original binder tree and recursive operators.",
  "For every changed primitive prove same-scope extension/erasure with one joint witness and preserved admissions/typed incidences; entailed substitution into an unchanged kernel only closes SC_ROLE.", "drel rs mixedrole")
n("INIT_WORLD", "OPEN-SEMANTIC", "Independent initial punctured world/import relation", "PCINIT",
  "Original xi, semantic imports, source alias/activation identities, other environment/world state, checked hole kept open.",
  "Specify filling-independent EnvStore/JointWF clauses for initial context and all imported roots including hole-dependent aliases; exclude circular checked-membership admission. SEM_JOINT interprets them jointly, INIT_VALID realizes actual initial worlds, and HISTORY/ALL_WORLD prove preservation/coverage. Retain the reviewed restricted source-root interface: one independently typed external base, actual open-import substitution action where needed, original source constructor data/provisional roots, joint cross-boundary incidence/current-world compatibility and an independent root-extension last rule. Scalar exporter validity still needs actual cross-world installation at the importer; closed filled roots supply no hole-dependent open action. Preserve B_orig/xi and witness dependencies without requiring one new witness across fillings or restricting to source-reachable clients. For each independently legal open-import substitution, act on original hole/rigid incidences and all licensed dependent witnesses together; prove clause-by-clause identification with the fixed independent import/world interpretation and joint importer root extension preserving old external incidences at the same original X/xi and binder positions. Generic relation-image transport or independently valid closed fillings supplies neither that rule nor its witness transport. The new bounded W0 audit distinguishes source-owned root construction from an independent semantic import: the latter needs its independently specified open descriptor/provider clause at its original importing incidence and a zero-step joint root extension over the external base, punctured callable/argument interfaces, shared provider/reference/state identities, activation and live owner evidence at one (C0,xi). The rule leaves holes open, preserves prior incidences and assumes neither checked membership nor validity of the extended world; no inspected context, source-contract or inert-introduction clause supplies it. The step-index candidate grants a hole premise only after a concrete source transition; inert Name/capture/Delay needs an independently justified zero-step open-root introduction at the importing incidence. Treating installation as a transition adds an event not selected by the current source rules. This is a restricted guard-placement obstruction, not a source counterexample or a decision that rejects step indexing.", "compat init inlet world3 round3review importaction1 attack4 initworldw0")
n("INLET_CARRIER", "OPEN-PROOF", "Pointwise whole inlet/carrier/descriptor compatibility", "SEM_JOINT PROFILE CALL_TYPE",
  "Direct callable and entire inert-computation-carrier holes, original inlet descriptor/actual role/entry and response port, at every independently valid original world.",
  "Prove the local carrier/descriptor plugging law at each inlet, including the apparently pure identity carrier, preserving all other bindings/imports. This is pointwise in the fixed semantics; INIT_VALID separately proves actual initial world/environment realization.", "inlet init core")
n("HISTORY", "OPEN-PROOF", "Independent response, raw re-entry and future-use admission", "ADMISSION_CLAUSES SEM_JOINT INLET_CARRIER INIT_VALID MEMBER_DISCHARGE",
  "Every independently valid original world and admissible response/argument; fixed raw continuation and original receiver; arbitrary finite prefixes.",
  "Prove initial, response, same-handle resume/current-state and actually returned-provider future-input rules are exhaustive and preserve all original validity/permissions and one compatible scoped assignment.", "adequacy source newrec")
n("ALL_WORLD", "OPEN-PROOF", "All-world independent admission completeness", "ADMISSION_CLAUSES SEM_JOINT INIT_VALID INLET_CARRIER HISTORY",
  "All independently compatible punctured contexts at the original tuple, including other-program/future contexts, not only current-source reachability.",
  "Prove generated challenge relation equals the independent domain in both directions for empty histories and all finite extensions; no finite sampled worlds or chosen filling defines the domain.", "inlet adequacy source")
n("TYPED_SOURCE_INCIDENCE", "OPEN-PROOF", "Source-owned complete typed boundary/Flow/receipt generation", "PROFILE ORIGINAL_ASSOC SV",
  "Actual raw source constructor, boundary and owner derivation; same source arms, original receiver and typed view path.",
  "Emit/invert every typed boundary introduction and indexed image for argument/result/environment/store/adapter flow, matching receipts and actual result timing. General cases extend SV without promoting positional equality.", "boundary core sv")
n("EVENT_OUTPUT", "OPEN-PROOF", "Actual event-to-complete-output contribution correspondence", "TYPED_SOURCE_INCIDENCE CALL_TYPE HISTORY",
  "Reached request and current complete executing view with original pending suffix; formal invocation distinct from callee-evaluation prefix.",
  "Derive exact Observe(q,V,p_exec) and typed p0-to-p_exec incidence through complete invocation/result consumption for every emitted event; preserve independent q/origin/K,D and no blanket Call attribution.", "event boundary newassoc")
n("CAPTURE_LIVE", "OPEN-PROOF", "General typed capture/read/receiver/liveness coverage", "TYPED_SOURCE_INCIDENCE EVENT_OUTPUT HISTORY TRANSPORT",
  "Actual capture/write/read/receipt and original receiver/owner/handler activations, including returned latent values and raw resumed state.",
  "Prove all source transitions produce the typed incidence used by Path and the exact current activity sets, with future view-specific Observe and no revival of expired receivers. SV exact case is already closed conditionally.", "boundary sv adequacy")
n("ADAPTERS", "OPEN-PROOF", "Complete source adapter generation and correspondence", "CALL_TYPE TYPED_SOURCE_INCIDENCE",
  "Actual provider-owned role/entry, complete argument and designated result consumer, independently typed unknown-shape conversion alternatives.",
  "Generate and realize all admitted source adapters and invert resolver alternatives, preserving whole observations and source incidence; an internal inferred Function view does not change actual entry.", "core boundary")
n("MIXED_EFFECT", "OPEN-SEMANTIC", "Mixed abstract/concrete effect membership and annotation bridge", "SIG_RULES",
  "Original nonempty joint component, polarized ports, event occurrences and symbolic K,D; no endpoint-marginal recombination.",
  "Specify exhaustive comparison-independent mixed-row membership and source annotation-to-port/event incidence, extending the reviewed limited EROW cases while retaining hidden dependencies.", "compat mixed")
n("SUBTRACTION", "OPEN-PROOF", "Complete shallow/deep handler contribution image", "MIXED_EFFECT EVENT_OUTPUT",
  "Actually targeted typed events, original handler/resumption/consumer semantics and symbolic invariant dependencies.",
  "Prove exactly which complete observations are removed/transformed; retain independent same-family events, raw suffixes, re-emission and live K,D. Support cancellation alone cannot justify the image.", "ordinary mixed boundary")
n("RELEASE", "OPEN-PROOF", "Source attribution and actual protection-release crossing", "TYPED_SOURCE_INCIDENCE EVENT_OUTPUT CAPTURE_LIVE SUBTRACTION",
  "Approved outward crossing after intervening computation/handler processing; same selected target view and original live receiver.",
  "Generate comparison-independent e-attribution and prove actual crossing/persistence at the same transported target; receipt or Observe alone is not crossing, and a new receiver cannot inherit expired release.", "release boundary")
n("DISPATCH", "OPEN-PROOF", "Complete ordinary dispatch/OpCompat/generic arm theorem", "GUARD_COVER MIXED_EFFECT CAPTURE_LIVE",
  "Actual ordered active-boundary search, independently opened request/arm binders and declared assumptions, ordinary raw resumptions.",
  "Derive complete source ordered search and candidate eligibility, selected-arm compatibility, outside-arm/deep expansion and same-witness generic checks under rigid-hole permissions.", "ordinary charter boundary")
n("RAW_SOURCE", "OPEN-PROOF", "Complete source relation generation and inversion", "SEED_SOURCE DREL2 GUARD_COVER MEMBER_DISCHARGE REC_INIT GENERALIZE ADAPTERS DISPATCH",
  "Precisely declared supported source syntax and independent source judgments; generated relation retains every alternative at original scopes.",
  "Induct on every included literal/Name/Lambda/Call/Bind/annotation/pattern/conversion/global/operation/handler constructor to emit exact atoms and lift every independent typed derivation back. No supplied decorated typing premise for raw formation.", "core source fview")

# Shared world, finite solving, all-view, production and lifecycle cuts.
n("STATE_ID", "OPEN-SEMANTIC", "Source State location and activation identity", "INTRO",
  "Source declarations and distinct invocation/event identities; static StateSlotId is only an origin.",
  "Give source introduction of dynamic storage locations/activations and capture alias identity across same/different invocations, without deriving it from an Oracle fixture.", "state")
n("STATE_RW", "OPEN-SEMANTIC", "State read, replacement and restart source equations", "STATE_ID",
  "Actual source location and incoming live store.",
  "Specify exact Read/update/replacement/restart equations, including the store passed to saved suffix and later captured reads; ordinary Bind's threading is not a replacement rule. Frozen Oracle archaeology found an explicit historical local-State lowering and snapshot/frame runtime route, useful only to locate operational responsibilities: it supplies neither current xi/typed EnvStore preservation nor the successor equations.", "state oraclestate")
n("STATE_RESUME", "OPEN-SEMANTIC", "Raw resumption store and multi-shot branch equations", "STATE_ID",
  "Original raw handle, current resumed state and repeated branch identities.",
  "Specify which store each resume receives and how repeated/re-entered branches relate; sampled candidate branch equations are not source authority.", "multishot ordinary")
n("REF_WORLD", "OPEN-PROOF", "Reference/import alias plugging and world transition closure", "INIT_WORLD STATE_RW STATE_RESUME",
  "Original typed open source identity graph, semantic imports, same world/xi and hole-dependent aliases.",
  "Prove plugging and every source transition preserve EnvStore/JointWF for references and imports; static reachability alone supplies neither typing nor arbitrary-world closure. The recovered historical State frame mechanism separates static operation identity, dynamic frame identity and live payload, but does not provide the current typed preservation theorem.", "compat state oraclestate importaction1")
n("CTX_FINITE", "OPEN-PROOF", "Finite source guard-context canonicalization", "GUARD_COVER RAW_SOURCE",
  "Actual source child-comparison law j_child=Ctx_r(j,u,v,witnesses), original origins/opening identities and invalidation dependencies.",
  "The reviewed finite static-port relational algebra constructs J_inc=product_i Powerset(I^k_i), its exact context encoding and finite state/hyperedge carrier. A reviewed restricted trace represents unsealed outward permission restriction; it does not cover a sealed result/store packet. That trace needs a source-justified scoped target interface and bound-capture/pack/open correspondence preserving every original witness, provider, scope, K,D dependency and suffix. This is only the next uncovered operation in that trace, not a global ordering or the sole leaf. Remaining: enumerate every actual source child-context operation and identity observer in the syntax (or prove its separate finite representation), and establish semantic rule/guard preservation plus monotone fact/permission/alias updates. Finite carrier alone cannot exclude a toggling invalidation loop or bound worlds.", "contexts newglobal projection2 ctxpacket round2review")
n("PRIMITIVES", "OPEN-SEMANTIC", "Complete independent Guard/Phi/K,D operand semantics", "SIG_RULES MIXED_EFFECT INTRO",
  "All primitive original operand tuples and original binder placements, including projected/grafted endpoint variation.",
  "Give exhaustive comparison-independent primitive relations and any varied-endpoint transport law; retaining an old operand does not prove substituting a different endpoint preserves admission.", "phi residual newglobal")
n("JOINT_DEC", "OPEN-PROOF", "Effective complete joint solver/residual decision", "PURE_DEC CTX_FINITE PRIMITIVES ALL_WORLD",
  "Every original structural/effect/guard/profile/admission predicate jointly interpreted; exact admitted source envelope.",
  "Construct finite effective candidates/quotient with preservation AND reflection for every actual active primitive and simultaneous original-witness completeness, or an exact effective residual decision route. The reviewed Record-chain halting extension proves that finite syntax, finite nominal support and decidable individual candidate checks do not supply a computable joint bound from pure FMP. This is not Yulang undecidability; the missing actual primitive reflection/decision law is still required.", "puredec contexts residual newglobal projection2 round2review")
n("PROJECTION", "OPEN-PROOF", "Effective principal public projection", "JOINT_DEC GENERALIZE EQ_RES",
  "Original quantifier alternation, fixed imports, structural/effect correlation and all evidence alternatives.",
  "Compute a legal exported constrained scheme with exact original-fiber projection and ordinary-use factorization. Equality-only eligible atom coordinates now have a reviewed exact orbit-elimination and witness-strategy theorem at the original binders; the bounded shadow evaluator implements only pointwise truth. Remaining: prove every actual eliminated-name observer's exact expansion, preserve non-name/recursive predicates and their original quantifiers, construct the residual/exported scheme and actual ordinary-use evidence. Neither equivariance nor separate root marginals supplies these laws.", "residual scoped pg projection2 orbitimpl round2review")
n("COMMON_DESC", "OPEN-PROOF", "Legal common descriptor and all-path realization", "PROFILE ALL_WORLD ALLOC_COMMON",
  "One original source solution, every typed Function path and independent compatible carriers/contexts.",
  "Construct one legal descriptor realizing common output allowance while admitting every required original challenge, not merely a pointwise union over incompatible descriptors.", "common source")
n("COMMON_TOTAL", "OPEN-PROOF", "Total common allowance at original solutions", "COMMON_DESC ROWS WHOLE_REL",
  "Same original source witness and legal descriptor with retained graft/query operands.",
  "For every original s, construct a jointly compatible a with Q_common(s,a), preserving the complete source/admission relation; Q success may not generate source facts.", "common source newglobal")
n("ALL_VIEW", "OPEN-PROOF", "All-valid-view lifting through actual common export", "COMMON_TOTAL USE_GRAPH GENERALIZE",
  "Independently valid public V, fixed original scopes and actual exported B_common with its resolver/evidence alternatives.",
  "Prove Valid_V(v) implies exists original-scope x,p,w,a: J_S and K_G and Q_common and Direct(B_common,R_V(v)) for every V. Exact rewriting or a retained unexported root cannot supply this Direct. In source-contracts §5.3's displayed certificate calculus, the Function Direct rule requires a matching non-coverage interface; a nonidentity widened result does not follow from a leaf VIncl or paired Option 2 extras alone. The separate decorated value-membership leaf and other actual resolver cases remain open, so this is not a universal resolver counterexample. A reviewed bounded actual-result-check trace finds no successful decorated inclusion product in the inspected F5 route: `apply_typed_task` decomposes endpoint pairs and retains diagnostic/incompatibility data, ordinary Lambda synthesis supplies its body result directly, and final export rebuilds an F5 predicate. The exact remaining construction is an original-scoped decorated result-check certificate from independently established nonidentity VIncl(A,B), consumed by an applicable whole-Function resolver at actual B_common. The independent semantic inclusion and actual resolver/export evidence remain open; this refines the construction locator only and does not prove F5 absence of every alternate resolver.", "use coverage newglobal attack4 resultbridge")
n("SAT_A", "OPEN-SEMANTIC", "Exhaustive Option A/2 production member clauses", "SIG_RULES PRIMITIVES SEM_JOINT",
  "Approved complete original Rel_C and xi, endpoints/role/entry/path/origin/continuation/scope/authority/dependencies; Option 2 extras allowed.",
  "Specify exhaustive independent Sat_A for all licensed members, including observations without source-reference constructors. Do not define production as the candidate source image.", "optiona option2 source")
n("ADM_A", "OPEN-SEMANTIC", "Exhaustive production punctured-context admission", "ADMISSION_CLAUSES SEM_JOINT",
  "Approved direct callable and whole inert carrier holes at same xi; other environment/world validity independent of checked membership.",
  "Give exhaustive Adm_A initial/response/resume/future clauses ranging over every independently compatible context, including empty histories, hole-dependent imports and actual provider roles.", "optiona inlet init")
n("DOMAIN_INCLUSION", "OPEN-PROOF", "Complete checked-to-actual production admission inclusion", "ADM_A ALL_WORLD",
  "Independent D_C and D_A at exactly the same original tuple.",
  "Prove forall xi: D_C(xi) subset D_A(xi), with every carrier/context/world/history witness preserved. Empty output sets cannot prove this domain statement.", "optiona core newglobal")
n("OBS_INCLUSION", "OPEN-PROOF", "All production observations contained in checked contract", "SAT_A DOMAIN_INCLUSION",
  "Every c in D_C and every production member at original xi, including independently licensed extra members.",
  "Prove P_A(c;xi) subset P_C(c;xi) for complete observations and future histories. Reference source-constructor simulation closes only its subfamily.", "option2 core newglobal")
n("SELECT", "OPEN-SEMANTIC", "Visible implementation and method candidate judgments", "",
  "Current source scope/world, receiver, method name and declared role/impl forms; no parser-implied finite complete candidate assumption.",
  "Specify independent visibility/candidate formation and selection/ambiguity alternatives with exact evidence; actual source observations/outcomes must be stated before fixed-point proofs.", "charter newglobal")
n("ROLE_ASSOC", "OPEN-SEMANTIC", "Role conformance and associated-type witness coupling", "SELECT",
  "One receiver/type assignment and original chosen implementation witness with its dependencies.",
  "Give source role-conformance/associated-type equations and recursive dependency judgments; associated types cannot choose a separate impl witness after method selection.", "charter newglobal")
n("RESOLVE_FP", "OPEN-PROOF", "Joint method/role/associated-type/visibility fixed point", "ROLE_ASSOC PRIMITIVES JOINT_DEC",
  "Complete independent candidate/role/associated judgments, retained alternatives and original shared nu.",
  "Construct sound complete principal resolution and prove termination/canonical finite carrier or admitted effective residual; positivity, uniqueness and finiteness must be proved, not assumed from syntax.", "charter newglobal")
n("IFACE_FORM", "OPEN-PROOF", "Complete finite simultaneous generalized interface producer", "GENERALIZE PROJECTION RAW_SOURCE",
  "All downstream inference observations, source origins/scopes, exports/imports/evidence/admission and recursive member roots.",
  "Generate a finite complete interface preserving/reflecting the whole source relation and every consumer observation; printed schemes/arena IDs or separate member projections are insufficient. CI_ALPHA only compares already supplied complete presentations. The reviewed next local head is emit_iface_r(original constructor data, child records)=E_r, with decode_atoms(E_r) equal to RAW_SOURCE's exact original r-atoms and Observe_r(original constructor/child data;xi)=Eval_accessor_r(E_r;xi) for every actual downstream read. Retain finite typed sort/scope/binder and rigid-input references, ordered primitive/kernel operands, recursive back references, original origin/receipt/owner/continuation/path incidence, evidence/admission dependencies and every actually read field. Full PROJECTION/GENERALIZE, if established, cover whole ordinary-use/evidence observations; they do not themselves enumerate all actual interface accessors. Identify an actual required evidence accessor before proving its emitted-reference equation; no new observer, opaque AllFuture predicate or semantic choice is invented.", "rebuild lifecycle newrec round3review")
n("IFACE_EQUIV", "OPEN-PROOF", "Actual interface-kernel equivariance and rigid identity coverage", "IFACE_FORM",
  "Every actual primitive/constructor/evidence/recursive/query operation in interface and consumer.",
  "Prove all required covariance/reflection laws and enumerate identity observers to fix rigid coordinates; supply CI_USE premises for the actual compiler rather than by convention.", "newrec lifecycle")
n("FRESH_LIFE", "OPEN-PROOF", "Internal/fresh use and SCC lifecycle correspondence", "IFACE_EQUIV CI_USE REUSE",
  "Actual intra-SCC live roots, independent incoming use instances, rigid imports/captures and consumer references.",
  "Prove fresh-use maps and all internal sharing; handle SCC split/merge, rebuild, cache/reference validity, dependency completeness and atomic publication without old numeric-ID reuse. Closed sublemma QR_CAPTURE_MAP_CURRENT_SOLVER: for production-produced schemes in one successfully returned immutable SolvedModule, a complete captured incoming-use Q/R map is total and injective, repeated occurrences and both R bounds share its substitution, distinct committed incoming-use images are disjoint, and capture denotes historical row identity rather than a live solver-row capability. Do not generalize this sublemma to arbitrary generic boxed finalizer inputs: its validator can admit an unregistered-Q ordinal collision; production finalization registers all Q and indexed validation enforces dense disjoint R ordinals. Independent compiler-referee review passed this restricted scope. This supplies no source/successor use correspondence, activation liveness, split/merge/rebuild correctness, dependency completeness, or atomic publication.", "rebuild lifecycle qrmap", closed=("QR_CAPTURE_MAP_CURRENT_SOLVER",))
n("RESOURCE", "OPEN-SEMANTIC", "Exact practical resource/admission and failure boundary", "JOINT_DEC IFACE_FORM",
  "Deterministic measurable source/solver support dimension and exact admitted results; no finite-world truncation.",
  "Choose justified support/resource limits and early rejection/failure ownership with no partial publication, then prove termination and behavior inside that envelope. The reviewed multiplicity-aware bound for one current constrain_live drain retains fixed closed endpoint inventories containing the initial task, finite bounds, stable memo/inventory, a constructor DAG and diagnostic boundary. It bounds neither source-size expansion, complete generalization/freshening, successor contexts nor total work. Shadow alpha/orbit exhaustion is not a production limit or UNSAT.", "charter newglobal livedrain alphaimpl orbitimpl")
n("HIR_WIRING", "IMPLEMENTATION-ONLY", "Settled source-to-HIR and complete production pipeline wiring", "RAW_SOURCE PROJECTION FRESH_LIFE RESOURCE",
  "Reviewed semantic contract and explicit implementation authority for its exact supported forms; user has authorized only settled shadow slices here.",
  "Implement the complete source coverage and lower/emitter/solver/generalizer/instantiator/publisher correspondence. Reviewed shadow plumbing retains solved Apply operands, nested/grouped topology, annotation/header joins, SCC endpoints/outgoing uses and pending instantiation. The exact local-Bind sidecar now retains captured apply/step identities and one unresolved inner Call through solve and the existing Core projection; ordinary refusal and outer bookkeeping remain. The captured Apply now joins its enclosing root to the exact current finalized scheme/component under the existing SCC observer, while successor generalization remains unresolved and neither operand has an SCC-use route in that fixture. The opt-in HIR pending inventory now names the conditional CALL_TYPE CI-ArgFrame joint argument-typing/actual-returned-provider-carrier-compatibility obligation at each Apply; it carries no provider/world/evidence, emits no constraint and leaves solver typing unresolved. Alpha comparison and equality-orbit evaluation have separate supplied-input implementations. The later opt-in current Q/R capture retains successful original use/target/binder/opaque-row identity, with missing/incomplete/internal/zero-binder states distinguished and successor correspondence still pending. A focused structural observer now joins two resolved source occurrence positions to distinct incoming uses and complete current Q/R captures for their shared current scheme; it keeps current-to-successor correspondence and shared-contract transport unresolved. The Frozen Oracle captured-Call crosswalk joins historical source spans to the same HIR/Core/collected/solved pending row; it proves no inferred-type parity or source acceptance. The exact approved q1 recursive self-init source envelope now yields cold default-off Reject evidence retaining original binder/RHS identities; other shapes remain Unresolved, and production pre-execution enforcement remains pending. None supplies complete semantic dependencies, Generalize, profiles, contribution formation or ordinary Call inference.", "hir solver shadowcore owner retention bindergroups sourceuses solveduse applycross headerjoin sccendpoints sccoutgoing pendinguse localbind callscheme alphaimpl orbitimpl round2review shadowinit3 shadowexecq1 freshcapture legacycrosswalk producerchronology argframe sourceuseqr")
n("ORACLE_COMPAT", "OPEN-PROOF", "Successor capability and observation compatibility", "RAW_SOURCE RESOLVE_FP OBS_INCLUSION",
  "Declared final well-typed source envelope and current Authority; Frozen Oracle is historical evidence only.",
  "Prove required final acceptance/observations and justify each intended delta; use differential fixtures as evidence. Oracle algorithms/projections/IDs do not define successor typing or licensing.", "charter oracle newglobal")

# Aggregate endpoints have one explicit remaining theorem, not an implicit closure
# merely because their prerequisites have been enumerated.
n("SOURCE_ADEQUACY", "OPEN-PROOF", "General source adequacy and independent complete admission", "RAW_SOURCE ROWS ALL_WORLD CAPTURE_LIVE ADAPTERS SUBTRACTION RELEASE REF_WORLD RESOLVE_FP REF_SIM",
  "One original scoped source relation, independent judgments for every included form and all histories; actual operational source machine.",
  "Construct a single complete source/typed-core/observation correspondence with forward and backward derivation transport, world admission and compatible witnesses, covering the full declared source envelope. The reviewed constructor-local target is Emit_r plus independent local/world/history/descriptor certificates and child OpCorr implies OpCorr for the actual included r-constructor, on the same original scoped witness family. OpCorr transports actual SourceExec and the emitted decorated computation in both directions over corresponding finite prefixes/admitted histories, actual provider roots, entry/body/consumer/result ports, raw handles, complete pending suffix and re-entry delimiters, preserving nu/K/D. For the actual Lambda/source-function case, inert creation and invocation-head reduction retain lexical references; the remaining first body square is actual raw Run versus the emitted decorated body at the same original environment/current world and complete consumer/return suffix. RAW_SOURCE's typing emission/inversion and supplied decorated REF_SIM do not alone establish that operational square. This is an existing local correspondence obligation, not a new source-image definition, unlisted-constructor counterexample or status promotion.", "adequacy core source ordinary newglobal round3review attack4")
n("PROD_CONFORMANCE", "OPEN-PROOF", "Complete production semantic conformance", "SOURCE_ADEQUACY DOMAIN_INCLUSION OBS_INCLUSION",
  "Independent actual production relation/domain and declared checked source contract; no restriction to source-constructible production extras.",
  "Prove the complete source and production squares commute on original xi, while retaining both nonredundant containment quantifiers. The reviewed nonempty fixed-original-fiber separation makes the existing lower source-to-actual leg explicit: each generated source observation under independent admission must inhabit the independently interpreted actual descriptor/Sat_A at that same source object, with one original scope-preserving witness correspondence for roles/entries, endpoints, origins, continuations, typed paths, authority and K/D. Derive this actual constructor/member head from child membership and the original constructor witness, including the descriptor conjunct; neither D_C subset D_A nor P_A subset P_C proves it. Retain all original valuations/contexts/future histories and permit Option 2 extras without requiring their source construction. This refines the existing commuting target, not a new gate reduction.", "optiona option2 core newglobal aggregate3 round3review")
n("SOUND", "CONDITIONAL-CLOSED", "Sound successor inference", "SOURCE_ADEQUACY JOINT_DEC PROD_CONFORMANCE HIR_WIRING",
  "Full existing SOURCE_ADEQUACY, JOINT_DEC, PROD_CONFORMANCE and HIR_WIRING contracts, including HIR's existing PROJECTION/FRESH_LIFE/RESOURCE cone and complete actual semantic-stage input/result correspondence. Exact admitted source/resource envelope; original binder strategies and joint residual/query evidence; actual independent incoming-use maps, aliases/internal sharing, fixed rigid coordinates, references and atomic publication. A residual result strategy must satisfy every retained obligation; acceptance of syntax alone supplies no successful query.",
  "The reviewed conditional synthesis reflects every actual accepted finite joint use/result to its complete actual solver graph or satisfied residual strategy, undoes actual fresh maps with the use-indexed inverse iota_u(x) -> (u,x) preserving independent copies, aliases and rigid/shared identities, reflects the whole ordinary-use/evidence strategy through original-scoped PROJECTION, and applies same-original source/production correspondences. Option 2 extras use upper containment, not source inversion. No ALL_VIEW or universal Q success is needed. Establish a fresh complete snapshot's SOUND first from full stage correspondence and actual FRESH_LIFE maps/sharing/reference/barrier/resource exactness; REUSE's sound/principal-valid rebuild hypothesis is not a premise proving that snapshot sound. Reuse applies only afterward to an already covered complete snapshot, with any required principality proved separately. The narrower aggregate countermodel remains valid without HIR_WIRING; it is excluded by this existing full route. Actual semantics and complete pipeline correspondence remain unattained; HIR_WIRING is not strengthened or closed and no current compiler conformance, operational totality or cutover is claimed.", "charter adequacy aggregate3 sound3 round3review")
n("PRINCIPAL", "CONDITIONAL-CLOSED", "All-view principal successor inference", "SOURCE_ADEQUACY ALL_VIEW PROJECTION",
  "The full existing SOURCE_ADEQUACY, ALL_VIEW and PROJECTION contracts; every independently valid finite public scheme in the declared conservative abstraction; actual designated B_common export; original scopes, correlations, witness strategies and query evidence. PROJECTION includes ordinary-use/evidence factorization, not only marginal projection equality.",
  "The reviewed conditional synthesis computes one finite legal P_S before choosing V, constructs one whole ordinary-use copy/query graph for each V before assignments/challenges/histories, transports ALL_VIEW's one coherent original-scope joined strategy with actual B_common Direct evidence through full PROJECTION, and derives exact public factorization by certified-use Theorem 3. This proves universal ordinary-use factorization across all valid finite public schemes IF the three unchanged upstream contracts hold; none is actually closed. It supplies no production containment, SOUND or cutover claim.", "charter use newglobal principal3 round3review")
n("CUTOVER", "OPEN-PROOF", "Final reviewed implementation and production inference cutover", "SOUND PRINCIPAL PROD_CONFORMANCE FRESH_LIFE RESOURCE HIR_WIRING ORACLE_COMPAT",
  "Frozen complete successor design, implementation correspondence, required independent reviews and concrete explicitly approved routing/rollout.",
  "Validate whole pipeline and capability envelope, then obtain/consume concrete production implementation and rollout authority. Current user explicitly forbids cutover; this procedural gate is not a semantic user-decision blocker.", "charter rebuild review")

FAMILIES = {
    "directional source generation/provenance": "DIR_LOCAL RS_LX SEED_SOURCE",
    "recursive/generalized-use supplier": "REC_K REC_KV RS_LX MEMBER_DISCHARGE GENERALIZE",
    "simultaneous member validation/discharge": "FH DESC_CLAUSES SEM_JOINT REC_DESC REC_LOCAL INIT_VALID MEMBER_DISCHARGE REC_INIT REC_INIT_SELF",
    "Generalize eligible binder/anchor/view": "PG1 GENERALIZE",
    "section22 introduction/guard/permission": "INTRO S22_DIRECT GUARD_INSERT GUARD_TERMINAL GUARD_COVER",
    "complete source relation generation": "CALL_REL RAW_SOURCE",
    "seed/refined DREL-2": "WHOLE_REL SC_ROLE DREL2",
    "mixed-use role refinement/aggregation": "MIXED_ROLE DREL2",
    "original signature formation": "SIG_RULES PROFILE",
    "OriginalAssocType_X": "ORIGINAL_ASSOC CALL_TYPE",
    "Attach_C": "ATTACH LIC_FORWARD",
    "Lic_C": "SIG_RULES LIC_FORWARD LIC_INVERT",
    "complete beta/Slots profile and inversion": "PROFILE LIC_INVERT",
    "contribution ownership/typed source incidence": "ORIGINAL_ASSOC TYPED_SOURCE_INCIDENCE",
    "complete typed-row nonemptiness": "ROWS SEM_JOINT INIT_VALID",
    "initial/re-entry/all-world admission": "PCINIT INIT_WORLD ADMISSION_CLAUSES SEM_JOINT INIT_VALID HISTORY ALL_WORLD",
    "inlet/carrier/descriptor/import/world": "DESC_CLAUSES INLET_CARRIER INIT_WORLD SEM_JOINT REF_WORLD",
    "event/output correspondence": "EVENT_OUTPUT CALL_TYPE",
    "general capture/read/receipt/receiver/liveness": "SV CAPTURE_LIVE TRANSPORT PATH_QUERY",
    "general source adequacy": "SOURCE_ADEQUACY",
    "common allowance/all-view extension": "ALLOC_COMMON COMMON_DESC COMMON_TOTAL ALL_VIEW",
    "all-view principality": "PRINCIPAL",
    "SCC interface equality/fresh use/lifecycle": "CI_ALPHA CI_USE IFACE_FORM IFACE_EQUIV FRESH_LIFE",
    "residual/guarded joint solving/projection": "EQ_RES CTX_FINITE PRIMITIVES JOINT_DEC PROJECTION",
    "State/reference/world": "STATE_ID STATE_RW STATE_RESUME REF_WORLD",
    "method/role/associated/visible-impl fixed point": "SELECT ROLE_ASSOC RESOLVE_FP",
    "Option A/Option 2 containment": "SAT_A ADM_A DOMAIN_INCLUSION OBS_INCLUSION PROD_CONFORMANCE",
    "finite presentation/termination/resources": "FMP PURE_DEC CTX_FINITE JOINT_DEC IFACE_FORM RESOURCE",
    "production HIR/source coverage": "HIR_WIRING RAW_SOURCE",
    "successor/production/Oracle compatibility": "ORACLE_COMPAT PROD_CONFORMANCE",
    "final production inference cutover": "CUTOVER",
    "additional adapter/mixed-effect/subtraction/release/dispatch": "ADAPTERS MIXED_EFFECT SUBTRACTION RELEASE DISPATCH",
}
RETIRED = [
    ("Generic SOUND wrapper still lacks an actual publication leg", "SOUND HIR_WIRING SOURCE_ADEQUACY JOINT_DEC PROD_CONFORMANCE", "Reviewed full conditional reflection uses the existing complete HIR stage correspondence and PROJECTION/FRESH_LIFE/RESOURCE cone. Actual semantic and wiring proofs remain pending; no circular REUSE sound/principal premise certifies a fresh snapshot."),
    ("Generic final principality composition still unproved", "PRINCIPAL SOURCE_ADEQUACY ALL_VIEW PROJECTION", "Full conditional composition is proved; actual source adequacy, universal actual-export Direct lifting and whole ordinary-use/evidence projection remain open."),
    ("Generic complete Call composition still unproved", "CALL_TYPE DESC_CLAUSES SEM_JOINT", "Repaired full conditional composition is proved only with every independent CalRet/DelayIntro/Phase/BindTyped law and joint CI-Operands/CI-Bind/CI-ArgFrame/CI-Receipt/CI-StepFrame instance; their clause construction and actual source/world realization remain open."),
    ("Executable disposition and first self-read ambiguity for exact q1 my f = f", "REC_INIT_SELF REC_INIT", "Approved exact singleton is rejected before execution with F4 Never unchanged; actual compiler enforcement and all other initializer classes remain pending."),
    ("Pure FMP, selector/one-anchor existence as future gates", "FMP PURE_DEC", "Closed pure fragment only; arbitrary active predicates remain outside."),
    ("Opaque selected receipt/capture supplier", "SV", "Selected actual transitions and Pending histories proved with original typing/profile premises."),
    ("Opaque actual recursive provider graph or all lexical imports", "REC_K REC_KV RS_LX", "Actual graph and lexical ownership proved; KP argument/context pairing and KV predicate interpretation are conditional; semantic discharge/eligibility remain."),
    ("Arbitrary new complete Call index or new slot-label allocation", "CALL_REL ORIGINAL_ASSOC", "Complete relational family already constructible; original-kernel inhabited association is the real cut."),
    ("One separately completed P per local lemma/use", "PROFILE ROWS", "Use one jointly constrained original p at original scope; retain universal world/history predicates."),
    ("Separate original attachment/licensing claims with no original-coordinate distinction", "ORIGINAL_ASSOC ATTACH LIC_FORWARD LIC_INVERT", "Normalize to source-owned fiber introduction and forward/exhaustive inverse laws; no fresh-ID substitution."),
    ("General DREL-2 still opaque for the exact completed singleton", "SC_ROLE DREL2", "Entailed unchanged-kernel substitution closed there; changed primitives/mixed source remain."),
    ("Blanket no-existential classification O required for every row", "INTRO GUARD_INSERT GUARD_TERMINAL", "O is only a sufficient specialization; origin-relative local preservation M is the weaker actual target."),
    ("New m_V calculus as a prerequisite", "USE_GRAPH ALL_VIEW", "Ordinary copy/graft/query exists; actual-export all-view success remains."),
    ("Rollback/inverse intrusive mutation across edits", "REUSE FRESH_LIFE", "Authoritative rebuild route replaces inverse mutation; atomic lifecycle remains."),
    ("No effective interface equality whatsoever", "CI_ALPHA IFACE_FORM IFACE_EQUIV", "Finite supplied complete alpha presentation has a decision procedure; complete actual producer/equivariance remain."),
    ("Reachability/liveness helper as a source or production semantics gate", "PATH_QUERY TYPED_SOURCE_INCIDENCE CAPTURE_LIVE", "Finite supplied query is separable implementation; source evidence cannot be supplied by it."),
    ("E/R choice or blanket normalized Function effect protection", "DIR_LOCAL SEED_SOURCE", "Superseded by current directional user decision; no question reopened."),
    ("Production members must all have source constructors", "SAT_A OBS_INCLUSION", "Incompatible with approved Option 2; extra licensed members require full containment."),
    ("Finite-context theorem selects finite semantic worlds", "CTX_FINITE JOINT_DEC", "Draft conditional finite state-key theorem supplies no all-world quotient."),
    ("Repaired finite typed query still awaits compiler/spec review", "PATH_QUERY", "The previous full-attack record already closes both repaired independent reviews; only supplied-input conditions remain."),
    ("No constructive context/name-projection procedure in any fragment", "CTX_FINITE PROJECTION", "Reviewed finite relational context syntax and equality-only original-binder orbits are constructive; actual source observers and full projection remain open."),
    ("No current live-drain work bound", "RESOURCE", "The reviewed conditional multiplicity-aware single-drain bound exists; it is not a source-size or complete successor bound."),
    ("Approved captured local Bind cannot retain its inner pending Call through solve", "HIR_WIRING", "The exact opt-in local-binding sidecar and Core differential now retain it; ordinary HIR refusal and all semantic premises remain."),
]


def validate(check_refs=True):
    ids = [node["id"] for node in NODES]
    assert len(ids) == len(set(ids)), "duplicate obligation"
    by_id = {node["id"]: node for node in NODES}
    children = {key: [] for key in ids}
    degree = {}
    for node in NODES:
        key = node["id"]
        assert node["status"] in STATUSES, key
        assert node["premises"] and node["minimal_lemma_or_closed_scope"], key
        assert len(node["requires"]) == len(set(node["requires"])), key
        assert node["references"], key
        for ref in node["references"]:
            assert ref in REFS, (key, ref)
            if check_refs:
                assert (ROOT / REFS[ref]).is_file(), (key, REFS[ref])
        for parent in node["requires"]:
            assert parent in by_id and parent != key, (key, parent)
            children[parent].append(key)
            if node["status"] == "CLOSED":
                assert by_id[parent]["status"] in {"CLOSED", "CONDITIONAL-CLOSED"}, (key, parent)
        assert node["status"] != "BLOCKED-BY-USER-DECISION", "no qualifying two-semantics witness supplied"
        degree[key] = len(node["requires"])
    queue = collections.deque(key for key in ids if degree[key] == 0)
    order = []
    while queue:
        key = queue.popleft()
        order.append(key)
        for child in children[key]:
            degree[child] -= 1
            if degree[child] == 0:
                queue.append(child)
    assert len(order) == len(ids), "cyclic proof-route ledger"
    assert len(FAMILIES) == 32, "audit family coverage changed; review request mapping"
    for title, names in FAMILIES.items():
        assert names and all(key in by_id for key in names.split()), title
    reachable = set()
    todo = ["CUTOVER"]
    while todo:
        key = todo.pop()
        if key not in reachable:
            reachable.add(key)
            todo.extend(by_id[key]["requires"])
    # PATH_QUERY is optional shadow implementation, not a logical cutover premise.
    assert set(ids) - reachable <= {"PATH_QUERY"}, set(ids) - reachable
    return by_id, children, order


def data(by_id, children, order):
    return dict(
        schema_version=1, date="2026-10-07", baseline=BASELINE,
        revalidated_remote_head=REVALIDATED,
        status="Research navigation; exact scopes and cited independent reviews govern; no production authority",
        edge_meaning="Direct prerequisite for the named sufficient route; conditional nodes retain their explicit premises",
        universal_scope="All-world/admission/future quantifiers remain inside original predicates; existential notation never prenexes the original binder tree",
        topological_order=order,
        nodes=[dict(by_id[key], unblocks=children[key],
                    closed_lemmas=list(dict.fromkeys(
                        [dep for dep in by_id[key]["requires"]
                         if by_id[dep]["status"] in {"CLOSED", "CONDITIONAL-CLOSED"}]
                        + MANUAL_CLOSED_LEMMAS.get(key, []))))
               for key in order],
        request_coverage={family: names.split() for family, names in FAMILIES.items()},
        retired=[dict(old=old, replaced_by=keys.split(), reason=why) for old, keys, why in RETIRED],
        references=REFS,
    )


def render(doc):
    nodes = doc["nodes"]
    counts = collections.Counter(node["status"] for node in nodes)
    out = [
        "# Successor proof-obligation DAG", "",
        "Date: 2026-10-07", "",
        f"Audit baseline: `{BASELINE}`; read-only dependency revalidation through `{REVALIDATED}`.", "",
        "Status: canonical **research navigation**, not an Authoritative semantic design.", "",
        "Generated from `tools/research_successor_obligation_dag.py`; machine form: [successor-proof-obligations.json](successor-proof-obligations.json).",
        "", "## Interpretation and authority", "",
        "Current explicit user decisions govern, followed by approved designs, exact reviewed theorem scopes, confirmed code, historical Oracle and general practice. Upper source exposure protects its output occurrence; it does not backflow into an existing lower/provider and does not delete that provider's independent protection. Internal inference views and actual callable roles/entries remain separate.",
        "",
        "Edges are direct prerequisites of the named sufficient proof route. They do not say that enumerating prerequisites proves the remaining theorem. CLOSED is only the stated scope; CONDITIONAL-CLOSED records a proved implication with the displayed premises. IMPLEMENTATION-ONLY means a settled structural responsibility still needing implementation/verification, never permission to adopt unresolved semantics. OPEN-SEMANTIC marks a missing independent clause, not a user decision. There is no qualifying same-source pair of complete competing semantics, so no BLOCKED-BY-USER-DECISION node.",
        "",
        "The full original `(X,xi=(nu,K,D))`, source scopes, binder identity and contribution provenance stay shared. A complete profile is one original coordinate inside `J_S`; all-world/admission/future-history quantifiers remain in its predicates. No existential choice of a convenient history replaces them. Scoped quantifiers are never prenexed by this notation.",
        "",
        "Each gate below lists its direct premises, directly reused closed lemmas, smallest remaining claim, downstream gates and production relevance. Transitive requirements follow the machine-checkable DAG. The checker validates structure, coverage and navigation only; it does not verify the mathematics or source semantics.",
        "", "## Status counts", "", "| Status | Nodes |", "| --- | ---: |",
    ]
    out += [f"| {status} | {counts[status]} |" for status in sorted(STATUSES)]
    out += ["", "## Full topological inventory", ""]
    for node in nodes:
        key = node["id"]
        links = lambda keys: ", ".join(f"[{k}](#{k.lower().replace('_', '-')})" for k in keys) or "None"
        out += [f"### {key.replace('_', '-')}", "",
                f"**{node['gate']} — {node['status']}**. Production relevance: {node['production_authority']}.", "",
                f"- Direct prerequisite gates: {links(node['requires'])}.",
                f"- Premises retained: {node['premises']}",
                f"- Already closed lemmas reused directly: {links(node['closed_lemmas'])}.",
                f"- Minimal remaining lemma / exact closed scope: {node['minimal_lemma_or_closed_scope']}",
                f"- Unblocks: {links(node['unblocks'])}.",
                "- Sources: " + "; ".join(f"[{r}](../../{REFS[r]})" for r in node["references"]) + ".", ""]
    out += ["## Required audit coverage", "", "| User-requested family | Normalized gates |", "| --- | --- |"]
    out += [f"| {family} | {', '.join(keys)} |" for family, keys in doc["request_coverage"].items()]
    out += ["", "## Explicit retirement and replacement", "", "| Historical/pseudo gate | Current gates | Reason |", "| --- | --- | --- |"]
    out += [f"| {row['old']} | {', '.join(row['replaced_by'])} | {row['reason']} |" for row in doc["retired"]]
    out += ["", "## Direct next proof cuts", "",
            "1. On the original Call chain, construct every independent local law and joint Call-input instance retained by conditional CALL_TYPE, then introduce the owned full typed-image incidence and complete-family original fiber; then invert the actual original licensing rules, assemble the complete profile and construct one complete joint row. No new ID or source position supplies that fiber.",
            "2. First specify the independent descriptor, world and admission clauses and construct their joint interpretation; distinguish this from actual initial-world existence. For the listed recursive FH route derive exact finite-failure reflection, or prove the alternative ordinary two-closure introduction with all independent guards. Unfolding and a postfixed graph alone do not prove absorption. Audit own-member facts hidden in world premises; construct source-root/import-world extension and prove latent ordinary cyclic Return acceptance together with the required simultaneous root validity and every non-descriptor member conjunct. The exact q1 self-init rejection is closed; remaining initializer classes and actual compiler enforcement are open.",
            "3. Supply semantic eligible Generalize views and origin-relative insertion/terminal laws; use the closed provenance machinery and finite alpha equality only after their actual premises hold.",
            "4. Extend actual typed source incidence and history/world admission beyond SV; the finite Path query computes consequences of supplied evidence and cannot create it.",
            "5. Complete the shared primitive/world/source predicates, source-derived finite context presentation, effective joint solving/projection, legal common descriptor and universal actual-export Direct lifting. Prove both production inclusions, including Option 2 extra observations, before cutover.",
            "", "The [full-attack review](../progress/2026-10-07-successor-full-attack-review.md), historical [round-2 review](../progress/2026-10-07-successor-round2-review.md) and current [round-3 review/integration record](../progress/2026-10-07-successor-round3-review.md) identify actual proofs, implementations and checks. Round 2 retained 89 nodes / 194 edges and unchanged statuses. The first round-3 checkpoint promoted PRINCIPAL and CALL_TYPE with unchanged prerequisites and added CLOSED exact REC_INIT_SELF as one REC_INIT prerequisite: historically 90 nodes / 195 edges, CLOSED 7, CONDITIONAL-CLOSED 19, OPEN-PROOF 44. The later reviewed full SOUND composition adds only HIR_WIRING to its existing sufficient route and promotes SOUND conditionally: final 90 nodes / 196 edges, CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1, BLOCKED 0. Existing OPEN nodes decrease from 65 to 62 by those three conditional implications; the new closed self-init subcase is not an old-node reduction. HIR_WIRING retains its full existing definition and actual implementation/verification remains pending; the concurrent C1-C7 Call operand note is an unadopted research candidate only. No actual upstream semantic input is closed. The preserved pre-correction ledger is unchanged; old map snapshots are navigation history, not additional live gates.", ""]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    by_id, children, order = validate()
    doc = data(by_id, children, order)
    outputs = {
        ROOT / "notes/theory/successor-proof-obligations.json": json.dumps(doc, ensure_ascii=False, indent=2) + "\n",
        ROOT / "notes/theory/successor-proof-obligations.md": render(doc),
    }
    for path, content in outputs.items():
        if args.write:
            path.write_text(content)
        else:
            assert path.read_text() == content, f"stale generated ledger: {path}"
    counts = dict(sorted(collections.Counter(node["status"] for node in NODES).items()))
    print(json.dumps(dict(status="PASS", nodes=len(NODES), edges=sum(len(n["requires"]) for n in NODES),
                          covered_families=len(FAMILIES), counts=counts,
                          semantic_proof_checked=False), sort_keys=True))


if __name__ == "__main__":
    main()
