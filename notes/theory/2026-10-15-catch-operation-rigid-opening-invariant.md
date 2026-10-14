# CatchOperation rigid opening: native owner invariant and missing premise

Date: 2026-10-15
Status: frozen bounded research checkpoint; non-authoritative; independent review pending
Claim class: static source/operational characterization and minimized missing premise
Baseline: `research/simple-sub-intrusion`, `427d1ff5daab866fa7d89cb513a077063cc6454d`
Exclusive output lease: this file only
Method: constructive bridge attempt through actual generation, bound insertion,
opposite-bound replay and polarity-indexed extrusion; no execution

## 1. Frozen statement and authority

Fix a well-formed declaration
`Delta |- p : forall rho_family,beta_local. Sigma(rho,beta)`, its admitted,
known family instance `rho`, one source arm body `h` with its original
annotations and captured environment `Gamma`, and one assignment `nu` to
shared/captured endpoints. `Delta` fixes rigid imports and already-shared
endpoints. `beta_local` is the declaration-owned tuple outside the family
parameters, including local binders in callback effects. Ownership does not
change when two assigned endpoints happen to coincide.

For every actual selected request `q`, retain its original declaration map
`theta_q`, fixing `Delta` and `rho`, and its single witness
`s_q = theta_q(beta_local)`. The dependent tuple is
`P_q = (A, B, J_q, profiles/evidence, K,D, latent dependencies)`; dependent
`J_q` is inside the package. All actual requests remain quantified; a failed
consumer cannot remove a reached request. Aliasing, another dynamic event
and raw resumption do not independently instantiate an already typed use.

The required native bridge constructs and checks one finite source derivation
under one joint fresh rigid tuple `kappa`, with scopes

```text
exists Z_shared.
  forall kappa_local.
    DeclBounds(rho,kappa) implies
      exists Z_body. BodyConstraints(Gamma,rho,kappa,Z_shared,Z_body).
```

`Z_shared` remains outside the universal; body-local witnesses and nested
declaration binders retain their original scopes. Caller-private `s_q=Int`
remains in the joint ledger and supplies no arm assumption `kappa=Int`.
Successful checking must specialize at each retained `theta_q` using the
same captured assignment and the same joint dependent tuple through actual
propagation/extrusion consumers. Separate pointwise body elaborations do not
satisfy this statement. Neither vacuous success over an empty admitted generic
domain nor success on only concrete signatures discharges its A/B obligation.

The existing hypotheses are declaration well-formedness and bounds,
substitution-preserving primitive rules, actual typed Flow, and well-formed
store/raw-suffix interfaces at the resumed state. A substitution-stable
checked body derivation is the evidence the bridge must supply; it is not
assumed to follow from the formula or a successful constraint store.

Authority: charter §§19–20, operation-instance package §§2–4,7–9, and
top-level inference principles §§1–4, including §1.1. Charter §19's
`sink::put` arm containing `my checked:int=x` stays rejected even for
Int-only callers. `echo` with `k x` is the uniform-positive payload/response
discriminator only. Package §7's conditional cut theorem is reused under its
actual hypotheses; it proves no missing source/native constructor. Package
§8's equality kernel and staged-extrusion scope lemma retain their limited
and conditional status. No solver representation is selected here.

Exclusions: no theorem promotion, compiler implementation authority, new
source restriction, value restriction, escape ban, caller enumeration or
per-constraint eager solving. Complete checking, lifecycle, full Call, effect
hygiene, soundness, required principality and F5 gates retain their scope and
OPEN status. This packet supplies no independent review of its own output.

## 2. Actual construction and live consumers

Locators below refer exclusively to committed baseline bytes.

1. `shadow_apply.rs:191–228` preflights each LocalSource before collection and
   candidate-session creation. `candidate_source.rs:133–142,191–198` admits
   operation arms only with `monomorphic_signature`: value variables and
   symbolic effect variables recursively fail this predicate. Thus a generic
   signature does not reach the normal arm action/body execution route.
2. For the admitted concrete domain, `Action::CatchOperation`
   (`candidate_source.rs:42`) carries declaration, arm occurrence, binder
   components, original scrutinee endpoint/effect and numeric level.
   Collection (`:429–459`) places this action before visiting body consumers;
   execution (`:901`) calls `candidate_catch_operation`. The action supplies
   no original request-local map or rigid-opening correspondence.
3. `candidate_catch_operation` (`candidate_effect.rs:806–870`) materializes
   paired payload A and response B through one values/effects/views map.
   Slots 60–61 link the payload; slots 62–63 link Functions for the raw
   continuation. The returned value is the original scrutinee value; the
   effect uses provisional conservative full-S, not an exact dependent J
   construction. Slots 64–65 are stored and sent to the live typed drain.
4. Value links call `candidate_scheme.rs:1369–1376`, which both records a
   constraint and calls `constrain_live_value`. The real chain is
   `lib.rs:11956–12009 -> run_candidate_typed_drain:12210 ->
   step_typed_drain:12264 -> dispatch_live_item:12380`. Context transport and
   execution precede dispatch; ordinary Function children and rewritten
   extrusion comparisons become typed work items. This is actual activation
   evidence, not an inference from stored constraints alone.
5. Nonstructural value processing reaches `candidate_apply_value`
   (`candidate_extrusion.rs:811–840` via `lib.rs:13804–13810`). It selects
   a bound side using row levels, calls `candidate_insert_bound`, and then
   separately calls `candidate_replay_bound`. Replay (`:767–808`) reads
   opposite bounds, constructs real Value/Effect tasks, and drives contextual
   replay. The same insertion/replay distinction holds for effects (:843–869).
6. The signature variable branch (`candidate_effect.rs:1453–1466`) allocates
   ordinary `fresh_value_at_level`; local effect names similarly use
   `fresh_effect_at_level` (:1588–1602). Allocation (`lib.rs:10177–10229`)
   gives default bounds, a numeric level, Fresh origin and `non_generic:false`.
   No operation-opening identity or checking-access restriction is emitted
   on these inspected branches. The private route below also reaches this
   allocation; bypassing preflight does not make that variable rigid.

### 2.1 Normal solve admission versus private collection

The normal `CandidateInference::solve` route in step 1 is distinct from direct
internal collection. At the pinned baseline,
`ConstraintBatch::collect_candidate_mode(hir,true,true)` (`lib.rs:910–915`)
has no source-preflight call. With LocalSource available it calls
`emit_candidate_source` (`lib.rs:1130–1144`), whose entry
(`candidate_source.rs:246–252`) likewise does not call preflight. The resolved
operation-pattern branch (:429–456) queues `CatchOperation` without invoking
`monomorphic_signature`. Driving the private candidate session's source
schedule (:817–825,901) therefore has a constructor path to
`candidate_catch_operation` and its ordinary flexible signature rows even
for a generic signature, subject to collection's other actual requirements.
This source inspection does not establish success for every generic HIR.

Direct collection is a real private function, not itself compiled only in
tests. Concrete callers also occur inside test modules: the helper
`lib.rs:18334–18336` in the cfg-gated module beginning at :18297, and the
session helper :33226–33240, call collection/session construction directly.
Those callers bypass the solve preflight by construction. No test was run
in this delta; neither the private route nor its flexible-row allocation
establishes generic source acceptance, uniform checking, or production
admission. The complete pinned collector and emitter were searched for
preflight references, and the cited constructor branches were read directly;
these claims do not rely on another producer's conclusions.

**First missing constructor premise:** before ordinary arm-body consumers,
the authentic CatchOperation route must construct one declaration-local rigid
checking opening for the complete dependent packet and its correspondence to
each retained request map, granting only declared bounds and the fixed
captured environment as checking assumptions. Normal solve excludes generic
signatures; the private path can reach ordinary flexible construction, but
provides no joint request witness or rigid-opening identity. The first missing
rigid constructor premise is therefore unchanged across these two inspected
routes. This is unavailable constructor evidence, not a source-qualified
counterexample or proof of proper generic rejection.

## 3. Direct extrusion: the concrete additional coverage seam

The prior note's reference-extrusion warning has a corresponding native
owner seam. `candidate_extrude` (`candidate_extrusion.rs:21–375`) memoizes
rows by `(endpoint,polarity,target)`. An endpoint already at/below the target
is reused (:97–100). A younger row allocates a copy, retains its parent/copy
occurrence, and directly inserts the one-sided source link (:119–125).
Selected source bounds are queued as `Work::Bound` (:126–165); that work
directly inserts the copied bound (:310–325). Incoming allowance copying
has another direct insertion (:305). These operations are not calls to
`constrain_live_value` or an equivalent typed comparison for each edge.

The physical emitter `candidate_insert_bound_with_evidence` (:409–570)
canonicalizes endpoints, validates row/sort, retains admission evidence,
pushes the selected bound side, registers capture incidence when requested,
marks intrusion dirty and emits a physical-slot receipt. It does not perform
the generic opened-binder check or separately replay every inserted edge.
`Work::Bound` subsequently transports origins. An emission/transport receipt
does not by itself establish a rigid comparison or exhaustive replay.

Here is an unexecuted owner-step calculation using native Function structure,
not the reference Record constructor. Let `alpha_l` and `X_(l+1)` be ordinary
rows with `alpha` in `X.lower`. Positively extrude a Function whose result
coordinate is X to target l, with other coordinates unchanged. The Visit
branch allocates `R_l`, inserts `X.upper += R`, recursively reuses alpha
because its level is at/below l, and `Work::Bound` inserts
`R.lower += alpha`. In the negative dual, start with alpha in `X.upper` and
negatively extrude a Function's result coordinate X: insertion gives
`X.lower += R`, then `R.upper += alpha`. Both calculations follow the actual
selected-side native transitions and memoization, without assuming an opening
constructor or final successful publication.

**Conditional use of that calculation:** if a future authentic opening denotes
an opened `kappa_l` by alpha while preserving its identity, these direct
mutations create same-boundary nonidentity comparisons `kappa_l <: R_l` or
`R_l <: kappa_l`. Package §8's selected checking discipline requires their
scope justification before forbidden specialization/publication. Wrapping
only the ordinary typed comparison entry misses these insertion sites.
The calculation proves a routing omission for that proposed wrapper; it is
not an admitted generic-source counterexample, an executed probe, a proof
that final native publication is unsound, or a principality refutation.
No rigidity is attributed to today's ordinary alpha row.

The exact downstream premise is complete opening-aware coverage of source
links, copied bounds, structural children, alias normalization and replay,
with current evidence after dependency changes and no successful publication
of a forbidden or stale checking relation. Package §8 already states the
conditional closure lemma. This pass identifies its actual missing native
owner evidence; it does not prove that adding a guard preserves native
solution relations, termination or required principality. Those obligations
cannot be discharged by the routing observation or by making all extrusion
rigid/blocked. Declaration-authorized comparisons remain part of the original
uniform source judgment, not blanket rejection cases invented by this note.

## 4. Same-request witness and qualifying intrusion

Within one signature materialization, repeated binder occurrences share row
identity. Dropping a temporary map does not erase this graph sharing.
However, operation use (:786–804) and CatchOperation (:806–870) allocate
distinct maps, and neither constructor establishes a generic request-pack /
arm-opening relation over A/B/J/profiles/K,D. The original scrutinee endpoint
is insufficient evidence of each selected request's declaration-local map.
`OperationOrigin` (:146–151) retains declaration/occurrence provenance;
it is not a completed joint witness correspondence.

Extrusion preserves actual parent/copy identities and source qualification:
`candidate_intrusion.rs:229–288` records parent, copy, polarity, target,
source events, comparison and occurrence. Qualification uses Value-reference
SCCs, not type-bound endpoint SCCs (`candidate_value_graph.rs:204–206`).
`settle_candidate_intrusion` (:480–508) equates the qualifying actual pairs.
These existing identities must be retained by any opening bridge. They
establish neither a request-local tuple nor checking access to private K,D.
An empty typed worklist cannot supply the missing opening correspondence.

`candidate_transfer_bound_origins` (`candidate_effect.rs:563–607`) transports
retained contextual witnesses and origin evidence. Its legacy origin-table
branch explicitly records `MissingOriginAssociation`. That gap is evidence
about that transport branch, not proof that the entire request witness was
lost. Neither retained origins nor absence of a generic witness constructor
licenses choosing payload/response/latent witnesses separately. General
alias/generalization and every relevant mutation/replay/intrusion route need
the original joint correspondence; this pass does not certify them.

## 5. Economy audit, evidence boundary and next action

Uniform rigid checking is A; admitting intended generic source arms is B.
Reconstructing the lost local tuple from family identity would be D, since
package §2 already proves that projection noninjective. This packet does not
reclassify or weaken those obligations. The earlier source characterization
stopped before generic construction. This different owner-level pass reduces
the downstream coverage question to direct insertion at :125/:305/:316 and
its physical emitter; it still cannot discharge the absent source opening.
Another cut proof or guarded-closure lemma assuming that opening would leave
the same premise untouched. Stop here under the economy rule.

One next action for the primary: obtain the smallest explicitly provisional
construction artifact at CatchOperation that emits the original joint
request/opening correspondence before body consumers and exposes obligations
for the direct native insertion sites identified here. This changes the
missing constructor input rather than assuming it in another preservation
lemma. Any executable source-evidence slice needs the primary's explicit
authorization and verification owner; keep generic production/cutover OPEN.
The concrete falsifier is an
authentic admitted generic arm using caller-private Int facts to justify the
charter's rejected payload consumer, or independently choosing one of the
tuple's marginal witnesses. Unsupported admission cannot satisfy it.

Static coverage is limited to the listed candidate owners/intervals. Omitted:
legacy and production inference, executable parsing/lowering, parameterized
family constructors, declared-bound carriers, generic callback checking,
complete J and selection image, complete effect hygiene, recursive scoped
checking, lifecycle/generalization, abnormal diagnostic publication and
all-path replay invalidation. Source constraints and qualifying intrusion
remain required; these omitted cases are not excluded from the parent theorem.

## 6. Checks, dependencies and commit packet

Scope delta: §2.1 independently traces private collection and test callers from
the same pinned source; no test execution or production-admission claim.

Read-only checks: pinned `git rev-parse`/branch/status, `git show
427d1ff5d:<path>` with bounded line reads, owner `rg` searches, committed-byte
SHA-256/live equality comparison. No builds, tests, probes, measurements,
Git mutations, delegation or shared-file writes. One leaf static pass within
20 minutes; zero experiment processes/samples; CPU/RAM not measured.

Configured prover model/effort pins are absent. Per primary launch provenance,
requested settings are inherited `gpt-6.1-sol/high`; effective runtime
model/effort is **unknown**. Role/default inspection is not runtime metadata.
No Astra assignment or override occurred.

The two earlier notes are the reviewed bounded inputs identified by the
primary; their committed headers still say unreviewed. This packet does not
adjudicate that status. Their concurrent record/header edits are excluded:
all substantive correspondence uses the pinned committed bytes. Record-only
HEAD movement during the pass does not replace this baseline.

Dependency hashes and final integrity results follow. Output is frozen before
submission; independent review and shared-record synchronization belong to
the primary.

SHA-256 of pinned committed dependencies:

```text
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9  notes/design/2026-10-02-operation-instance-binding-package.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
55d4e68cb9f144c42c07a33cb7d9ea3c9278a674bb8ae1c47c39864ec1745967  notes/theory/2026-10-15-generic-operation-rigid-opening-construction.md
a261db48f0986ed2f03a26a6506e5179793bc992708f8e26c90a2aa383c6e492  notes/progress/2026-10-15-generic-opening-source-audit.md
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  crates/yu-solver/src/candidate_intrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
64b94da599dc10aef6fd06003fc6c1ab909bdce2a07c722fdb11eb1c8b690ec4  crates/yu-solver/src/candidate_value_graph.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
```

Final observed HEAD: `7e076a6d22e4d34395a899f95b1ab9109a589fa0`; pinned source baseline remains unchanged.
All listed semantic authority/native code working bytes equal the pinned baseline.
Changed working dependency bytes, excluded from this bridge:

```text
dcf9b7d6d75fea8527683cbb6f7fae3aa922d9fca99167491099c02bd17762f0  notes/theory/2026-10-15-generic-operation-rigid-opening-construction.md
773e4166f202e38e8f131201425257202db363548b98cac8be704c8594546e1d  notes/progress/2026-10-15-generic-opening-source-audit.md
```

Commit packet:

- Exact changed lease: `notes/theory/2026-10-15-catch-operation-rigid-opening-invariant.md`.
- Baseline SHA: `427d1ff5daab866fa7d89cb513a077063cc6454d`.
- Dependency changes by this leaf: none. The two preceding input notes changed
  outside this lease; excluded current hashes are above, for primary delta review.
- Review: producer-only bounded characterization; fresh independent review pending.
  Parent rigid-opening and implementation gates remain OPEN.
- Checks already run: pinned owner/consumer inspection, fourteen SHA-256 dependency
  comparisons and note fence/whitespace/newline integrity; zero builds/tests/probes.
- Proposed checkpoint message: `research: locate native rigid-opening extrusion premise`.
- Proposed shared-record delta, left to primary/curator: retain the original generic
  A/B gate OPEN; link the first missing CatchOperation joint-opening constructor and
  the native direct-insertion coverage seam at candidate_extrusion.rs:125/305/316;
  keep checked-template, request/lifecycle transport, full Call, hygiene, soundness,
  principality and implementation gates separate. No shared record was edited.
