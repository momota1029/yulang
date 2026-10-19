# R84 finite classifier and role-call preservation

Assignment: `R84-ROLE-CALL-PROOF`, handoff revision 1. Author and sole writer:
`/root/r84_role_call_proof`. Status: **candidate mathematical proof under a
Draft judgment**, with a **conditional** ordinary-Apply specialization. This
artifact is a frozen review target, not independent certification, semantic
adoption, source/native closure, or production authority.

## Authority, parent and dependencies

R84 contract revision 1:
`tasks/agent-loop/sprints/effect-hygiene-runnable-role-slice-20261019-r84.md`,
SHA-256 `fd6de85efe1926696f3a45894aa1e3a8a612b31d257bb71b339cc7c79d7c2f48`.
The sole normative classifier is the frozen Draft
`notes/design/2026-10-19-r84-role-call-judgment.md`, SHA-256
`f3c604dd7a131bbba606d38ff5b19f37c01ef1b26386a5f90ae39e8de60478c1`,
authored by Luna. Baseline supplied by Luna:
`af3ccf2d63ba7f87e0359e183568db548ea53307` (no Git verification in
this assignment). Direct reusable proof is R81
`notes/theory/2026-10-19-r81-role-call-request-prefix.md`, SHA-256
`d3b3d52e19332506c6fab8eea7878a5ff1c81f90cf96dff548b30ab5f88c767f`,
author `/root/r81_prefix_proof`. R83 closeout is
`notes/progress/2026-10-19-r83-closeout.md`, SHA-256
`fb85fa14d8c5da7ce3bbc234d619d17b5c77902c4e1bd982df5322eb7667b00b`,
Luna; its mixed-failure conflict is rejected, not carried into this judgment.
Charter §21 (`notes/design/2026-09-29-scc-intrusion-redesign-charter.md`,
R81-pinned SHA-256 `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`)
is the source-role authority. The Authoritative top-level inference principles
remain in force (R81-pinned SHA-256
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`).

The original Simple-sub/evaluator theorem and class A/B obligations retain
their accepted source domain, universal quantifiers, source/native
correspondence and independent F1/FK1 foreign-continuation obligations. They
remain **OPEN 0→0**; R50 remains **NOT_ADOPTED**. This packet proves only a
finite property of the proposed role-call classifier and applies an existing
conditional ordinary-runtime lemma. It adds no bypass around constraint
generation, accumulation, propagation, levels, extrusion, qualifying
intrusion or generalization. Ordinary endpoint evidence is an input to the
classifier, never manufactured by it. Provider, annotation, receiver, request,
residual and witness lineages remain distinct.

## 1. Totality and disjointness of the ordered classifier

Fix a finite pair `(s,i)` of source declarations. Write `E` for
`SigEligible(s) ∧ ImplEligible(i)`, where each predicate is exactly §1 of the
R84 judgment. In particular, `ImplEligible` examines implementation source
form independently: it neither compares arities nor infers endpoint types.
When `E` holds, let `T` be the two *complete* finite endpoint inventories from
ordinary evidence, including the receiver and every explicit slot of each
declaration, whether or not a slot has a peer. Each item has exactly one tag
`Supported(t)`, `Outside(t)`, or `Unknown`; `t ∈ {int, ()}` for Supported,
with exact `[_] int` form additionally required for Computation entry. Put
`G = ∃ x∈T. tag(x) ∈ {Outside,Unknown}`. If `E ∧ ¬G`, let `V` be equality of
the complete supported parameter count, receiver/slot endpoint types and §21
entry-role vectors. The signature result is already `int` under `E`; the
implementation body result is checked by ordinary typing outside this
classifier.

The four mutually exclusive decision regions are:

| Region | Predicate | Outcome |
| --- | --- | --- |
| A | `¬E` | Unsupported |
| B | `E ∧ G` | Unsupported |
| C | `E ∧ ¬G ∧ ¬V` | Incompatible |
| D | `E ∧ ¬G ∧ V` | Compatible |

Proof of totality: source-form eligibility is decidable on the finite syntax.
If `E` holds, scan every element of the finite, tagged inventories to decide
`G`. If `G` is false, all compared entries are known supported values and the
finite vector comparison decides `V`. Classical binary case splitting on
these three terminating decisions reaches A, B, C or D. Proof of
disjointness: A contradicts the `E` conjunct of B–D; B contradicts the `¬G`
conjunct of C–D; C contradicts D on `V`. A and B deliberately share the
*outcome* Unsupported, but no declaration pair enters both regions. The
ordered procedure thus returns one outcome, even for simultaneous failures.
This argument assumes the judgment's exact-one-tag evidence contract; it does
not establish that the current compiler constructs such inventories.

The decisive applications follow from the guard before vector comparison:

| Pair against eligible `int -> int -> int` unless stated | Guard and mismatch | Result |
| --- | --- | --- |
| `self, selected:int, extra:bool` | extra endpoint Outside; arity also differs | **Unsupported** (B) |
| `self, selected:int, extra:int` | every endpoint Supported; arity differs | **Incompatible** (C) |
| `self, action:[_] int` | every endpoint Supported; Value/Computation roles differ | **Incompatible** (C) |
| `int -> [_] int -> int` versus `self, action:bool` | action endpoint Outside; Value/Computation roles also differ | **Unsupported** (B) |
| `int -> [_] int -> int` versus `self, action:int` | every endpoint Supported; roles differ | **Incompatible** (C) |
| `int -> int -> int` versus `self, selected:int` | all endpoints Supported and vectors equal | **Compatible** (D) |

The fourth row discharges the mixed `bool` plus role-mismatch case using an
ordinary `bool` Value annotation, which satisfies the independent source-form
predicate. `[_] bool` is also Outside, but does not itself exhibit a role
mismatch against the Computation signature. A missing supported binder follows
C by the same count comparison; an unknown or outside endpoint follows B even
if other positions differ. Neither `Incompatible` nor `Unsupported` means
ordinary language inference rejects the source.

## 2. Finite §21 executable-binder role preservation

For an eligible implementation with actual source binders
`b₀,…,bₙ`, define `ρ(b)` directly from charter §21: absent or ordinary value
annotation yields `Value`; an explicit outer `[_]` annotation yields
`Computation`. The pilot excludes every other executable annotation form.
Define the signature's role vector from its supported slots. The classifier
only *reads* the binder annotations and role vector. It inserts no adapter,
annotation, binder or execution step.

If the result is Compatible, region D gives `V`. Its count equality provides
one paired signature slot for every actual executable binder; role-vector
equality gives `ρ(bⱼ) = signatureRole(j)` for each `j`, including receiver and
every explicit slot. Since no binder is rewritten, ordinary entry under §21
retains `ρ(bⱼ)`. Thus the proposed finite judgment preserves the executable
roles of every paired binder **without inheriting roles from the signature**.
If `selected` is unannotated, its Value role follows its own source boundary;
ordinary inference must establish the `int` endpoint before compatibility.
An explicit `action:[_] int` has Computation role and matches only the pilot's
Computation slot. An unannotated action cannot acquire that role from a
signature. This proves the classifier-level implication, conditional on
actual binder retention and ordinary runtime role consumption when applied
to emitted code; it proves neither an actual role-member source constructor
nor general runtime correspondence.

## 3. R81 ordinary-Apply specialization and exact stop boundary

R81's conditional prefix theorem fixes one occurrence, original binder IDs,
source sites and lineages, and compares the selected-member output to the
*same* emitted ordinary `Apply(Apply(C_member,E₀),E₁)` graph. Apply it here
only under R81 P1–P5 and successful ordinary transitions. R84's Compatible
result discharges the finite role-agreement check for the Value/int pilot;
it does **not** supply P1–P4 or endpoint evidence. P5 comes from §21 only if
P2 retains the actual executable source binders and annotations.

For `SecondInt::second 1 2`, assume P1–P4 actually produce and admit the
ordinary graph with implementation body `second self selected = selected`;
assume ordinary evidence establishes all `int` endpoints, successful literal,
Name and Call construction, and ordinary completion. Both executable binders
are Value. The inner Apply forces receiver `1` before entering its body and
returns the closure for `selected`; the outer Apply forces `2`, then `selected`
returns `2`. The **conditional** outcome is `Completed(Integer(2))`. No
actual role-qualified source execution or current compiler acceptance follows.

For the exact Value call
`SecondInt::second (io::observe 1) (io::observe 2)` in R81's no-handler
source, retain the same P1–P4 and ordinary-operation hypotheses. Value entry
for `self` forces the whole first argument. Its `io::observe` payload `1`
creates the first unanswered event `q`; ordinary outward propagation stops at
`UnhandledRequest` with the resolved operation, first observe source,
payload `1`, event `q` and saved suffix. The suffix retains pending
`ValueEntry(self, member-body, member-env)` and the outer
`Frame::Callee(argument=io::observe 2, caller-env)` among crossed frames.
It need not contain every root frame. The first Value entry has not returned,
the next closure has not returned, and the second Value entry has not begun.
The observed prefix is exactly `[observe(1)]`; neither `observe(2)` nor a
completed `2` is derivable. A hypothetical handler response cannot be used
to extend this no-handler trace. The fixed source/event/continuation identities
are retained rather than equated with an unrelated residual or witness.

## 4. Parent application, source/native boundary and TODOs

The new finite lemma removes R83's mixed-failure ambiguity for the **R84 Draft**
and blocks signature-to-binder role inheritance. Combined with R81 it gives
an exact conditional Value-call behavior for the pilot. Original A/B, F1/FK1,
foreign continuations and all six effect-hygiene frontiers remain open at
their prior scopes. R81's `program.rs:414–433,488–566` and
`machine.rs:629–657,879–1105,1706–1775,1929–1960` are pinned ordinary
consumer evidence for binder roles, Apply and the stopped request. They are
not evidence that a role-qualified producer emits the needed graph. No new
source, native, test or runtime inspection occurred here.

| Stable TODO / owner | First missing evidence and falsifier |
| --- | --- |
| `R84-P1` / future validation and role-resolution source owner under Luna | Resolve unique `(ImplId,MemberId)` and receiver type without evaluating arguments; falsifier: `Role::member` still resolves only an Operation, selects eagerly or publishes an ambiguous target. |
| `R84-P2` / future member-materialization source owner under Luna | Retain actual binder IDs, source annotations, body and lexical environment; falsifier: synthetic/signature-inherited binder role or wrong member environment. |
| `R84-P3` / future LocalSource Call/Apply graph owner under Luna | Emit exactly the two ordinary Apply edges with whole arguments, caller environments and source sites; falsifier: eager argument, missing edge or lost provenance. |
| `R84-P4` / future candidate/runtime admission owners under Luna | Validate complete metadata/root and target before publication; falsifier: unsupported/incomplete role target admitted through an unrelated exemption. |
| `R84-ENDPOINT` / ordinary inference and source/constraint owner under Luna | Establish all complete-inventory endpoint tags through existing generation, accumulation and propagation, then validate body/result independently; falsifier: a tag inferred from the signature without ordinary constraints, extra binder skipped, or incompatible body accepted. |

R81's forward producer and backward consumer investigations already left
P1–P4 open; another assumed-transition trace cannot establish them. R83's
algorithm/prose conflict is resolved in the new Draft by the complete-inventory
guard, not by retroactively calling its proof complete. A future implementation
packet requires explicit semantic adoption and new exact leases. The narrow
source action is to materialize and validate the selected member through the
named owners, then compare emitted HIR/constraints/admission against this
conditional proof. An assumed LocalSource shape or passing test is not emitted
source evidence. No reviewer or production decision is made by this author.

## 5. Checks, resources and STOP

Checks: bounded read of the frozen contract, judgment, R81 proof, R83 closeout,
charter §21 and governing rules; symbolic finite case split and manual
case-table reconciliation. No tests, build, source probes, compiler CLI, Git,
source edit, external contact, delegation or scratch output. Resource charge:
R84 proof grant **150 seconds charged in full**; no carryover. Actual runtime
duration before the first clock observation is UNKNOWN. Requested model/effort
`gpt-6-sol`/high; observed effective model/effort **UNKNOWN/UNKNOWN** (no
effective-routing metadata supplied). Worker ID `/root/r84_role_call_proof`,
session `current-conversation-2026-10-19-r84-stage1`; no descendants.

Exactly two new paths in this assignment: this note and
`tasks/agent-loop/inbox/20261019-r84-proof.md`. There is no further in-envelope
stage after freezing the handoff. **STOP**: this author ceases writes after
the handoff hash receipt; review, adoption and integration belong to Luna.
