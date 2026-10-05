# Fresh Int Initial attempt: conditional map available, slot/view still open

Date: 2026-10-06 (assigned artifact date)
Status: frozen unreviewed partial conditional source proof and proposed precision repair
Baseline: `d2837d34026c262280e19e66085992bf480f7cf2`
Exclusive lease: this file only
Implementation authority: none
Method: constructive premise enumeration using the existing typed-structure correspondence clauses

## 1. Result and correction

Typed-boundary §6 already supplies the conditional rule for `M_Int`:
same-type binding uses identity and Force/return removes the computation's
result prefix. No new semantic map rule is required. The earlier fresh-Int
record needs a precision repair where it treats this correspondence itself
as the first missing source rule.

The corrected construction generates the literal/result/delay and derives
the path-map form **conditional on the independently typed source port and
binding**. It still does not complete `chi_Int` or Initial. The unresolved
field is the independent known slot/executing view and its source
profile/receiver context, including evidence that the contemplated port and
binding occur in that valid punctured context. The map law does not supply
this decorated certificate.

An empty profile is justified for the scalar literal's value view, which
has no effect-observation positions. It cannot be extended to the complete
callable/CallView profile just from empty argument effects, no handlers or
an empty environment. The construction stops before assuming that extension.

## 2. Exact inputs and authority boundary

Only committed objects at the full assigned baseline were consumed. The
previous note is inspected solely to propose a repair, not to certify this
attempt. The selected domain, Option A and Option 2 remain unchanged.

| Input | Exact governing/comparison scope | Git blob |
| --- | --- | --- |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §6, especially lines 763–789: typed-structure identity/prefix removal; profile introduction at 684–700; receipt at 792–807; realization boundary at 1020–1027 | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §§2–3 supplied source evidence and whole delay; §6 literal/result/parameter/call clauses | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | §2.1 decorated inputs; §3 independent hole/Initial premises; known-slot nonempty example | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | §21 syntax-selected Value entry, whole inert argument | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §3 actual fresh invocation/frame and receipt-before-entry | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | §10 Invoke, Receive and RebindResultPath under the typed correspondence | `10775573537d8b56423f796db3c7ac6bb427e252` |
| `notes/progress/2026-10-06-function-int-context-fresh-certificate.md` | §1 first-premise wording; §4 map/profile rows; §§5/7 interpretation and next obligation | `dd6b2715095a2797fd9f49cb50470ec371395959` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | d1 decisions 1–5: original independent context, direct whole carrier/callable, no Q premise | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | d1 decisions 1–5: complete original fiber, independent predicates, concrete clauses open | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | d1 decisions 1–4: Option 2 extras and source-reference/production distinction | `fb4a169a2d748422490cc74c026338587290e90c` |

The type/view packages retain their conditional/Draft source-realization
scope. The typed transport clause is used as given within that scope; this
note does not propose replacing it. No implementation authority or new
source admission rule is introduced. Previously read research/design-authority/
Git-concurrency rules govern this new disjoint lease.

## 3. Fresh independent declarations and local construction

Start from fresh proof labels and ground source endpoint choices, without
transporting the earlier Unit witness. The callable hole `H` has a declared
`Value(Int)` parameter. To make the terminal consumer concrete, take a
declared Int result skeleton as well. These declared interfaces describe
the context's uses; they are not a proof that any actual filling meets a
complete Function bound. The typed source skeleton is

```text
hole declaration: H : Value(Fun(Value(Int), Comp(empty,Int)))
other environment: empty
source argument:   c_1 = result(literal(1))
source context:    call(result(H), c_1).
```

The Function display here is the typed-core parameter/result skeleton, not
an exhaustive four-port descriptor interpretation or an invented meaning
for an effect sentinel. The source context has one callable hole and an
independently derived argument. At the call boundary the challenge has
direct callable and carrier ports, filled by the callable and the entire
carrier `t_1`. `H` is not entered into the semantic environment of other
values, and `Q` is not a premise of its declaration.

Typed-core §6 and §3 generate the local steps:

```text
d_1 = literal(1) : Value(Int)
I_1 = Value(Int)
c_1 = Normalize(I_1,d_1) = result(d_1) : Comp(empty,Int)
t_1 = Delay(X[c_1], empty lexical references).
```

No argument construction prefix executes. The eventual scalar is not
substituted for `t_1` in the receipt or admission record. No actual `id`
filling is used for these steps; no actual body behavior or successful
Function comparison licenses the context.

For this fresh ground **local fragment**, no operation-family binder,
symbolic family formula, import or other dependent value is introduced.
Thus local `K_1=D_1=empty` is permissible. This does not delete a preexisting
ledger: the fragment is newly chosen. If completion of the independent
slot/view introduces retained predicates, their incidences must be joined
under the same original assignment; the whole certificate's `K,D` cannot
be declared empty by ignoring those predicates. Before that completion,
the original ground endpoint choices fix `a=c=Int`, but do not certify a
complete original decorated fiber.

## 4. Derive the correspondence conditionally

Let `p` range over paths of the scalar Int result; its value-root path is
`epsilon`, and it has no latent effect-observation descendant. Keep source
and target **view occurrences** distinct even when their path suffixes are
equal. The following is the existing typed-structure rule instantiated at
this signature:

```text
M_force : (carrier, computation.result.p) -> (forced-result, p)
M_bind  : (forced-result, p)              -> (parameter-binding, p)
M_Int   = M_bind composed with M_force.
```

`M_force` removes the designated computation-result prefix; `M_bind` is
identity on the Int path suffix because the typed binding changes no type.
Consequently

```text
M_Int(carrier.computation.result.epsilon,
      parameter-binding.epsilon).
```

This is a conditional derivation from typed-boundary §6, lines 763–789,
not a new solver atom, carrier or semantic rule. Its premises are the
source-designated computation port and the independently typed Int result
binding. It does not relate arbitrary paths solely because they have equal
endpoint types. The whole-carrier parameter receipt and the result-value
rebind remain separate events/ports; prefix removal describes the result
transport, not erasure of the argument before entry.

The transport equations then preserve the original packet:

```text
chi' = M_*chi; D' = M_*D; K' = K; lineage' = lineage.
```

For empty local `chi,K,D`, these images remain empty. The identity/prefix
rule therefore handles this ground map form once source typing supplies its
ports; it does not depend on proving `Q`, or on an actual `id` filling.

## 5. Enumerate Initial premises and stop at the decorated slot/view

| Initial premise | Evidence reached in this fresh attempt | Status and exact limit |
| --- | --- | --- |
| Typed literal | §6 literal rule gives `literal(1):Value(Int)`, using its Int source primitive relation. | Derived local source form. No operation/request contract is involved. |
| Whole carrier/result port | §6 result normalization gives `Comp(empty,Int)`; §3 introduces its inert whole Delay. | Derived local provider and result interface. |
| Local empty profile | The literal's scalar `Value(Int)` view has no effect-observation positions, and boundary profiles are defined only at such positions. | Its local scalar profile is empty. This is not a complete callable/CallView profile. |
| Complete carrier/slot profile | Theorem C requires the carrier `d` profile and compatible known slot/view; typed-boundary §6 treats signature profiles as source-contract data. | **Open:** the independent source slot/signature/view certificate and its applicable profile positions are not generated from the displayed hole skeleton. Choosing its entire profile to be empty would be an assumed decoration. Stop here. |
| Receiver and receipt | Source-role §10 enters a fresh invocation and records `Receive` for typed parameter bindings; ordinary-computation §3 fixes receipt before entry. | Derived operational/typed schema, conditional on a valid typed invocation/view. An actual compatible receiver-context instance cannot be extracted from the literal alone; none is supplied using a filling. |
| Known slot/view `beta_Int` | A fresh proof label can be reserved for the declared callable position. | Reservation is not a proof that it is Theorem C's independently instantiated compatible slot/view. Its original profile/receiver relation remains unproved. |
| `M_Int` | Force result-prefix removal composed with same-type Int binding identity (§6). | Conditionally derived from the independent source port/binding. Its rule is available; its valid placement in the required complete slot/view certificate is still conditional. |
| Scope | Literal has no free-value bindings; callable hole is outside the other-value environment; all fresh source labels belong to this context. | Syntactic scope is determined. Original scope of an eventual boundary/profile/receiver witness must be supplied with that witness, not copied from a future filling or another context. |
| Original fiber/`K,D` | Ground `a=c=Int`; empty local ledger/incidence is consistent with this newly chosen scalar fragment. | No arbitrary old predicate is dropped. A complete admissible `xi_Int` is not proved until all slot/view contract predicates and incidences are accounted for. |
| Empty history, no handlers | No request response, handle or latent-provider extension appears in this literal-prefix case. | These extension checks are absent; the independent Initial context/view check is not discharged by their absence. |

This table separates available rules from independently certified input
data. The first unresolved **complete decoration** is the compatible known
slot/executing view and its profile/receiver relation. Downstream receiver,
scope and fiber conditions are recorded without pretending to finish them
after that stop.

Theorem C Initial requires the profile/path-bearing typed carrier in that
context. Its premise tree is therefore still incomplete:

```text
typed literal/result/delay                             available
same-type/prefix-removal map rule                      available conditionally
independent compatible slot/view/profile/receiver      OPEN
original complete scopes and joint predicates         depend on that completion
---------------------------------------------------------------- Initial
no conclusion is claimed.
```

## 6. Why no handlers and empty effects do not close the profile field

Typed-boundary §6 makes the relevant distinctions explicit:

- An omitted/wildcard callback capture annotation supplies protection at
  applicable callback positions, even though it supplies no concrete grant.
- A signature profile is source-contract data, not a projection reconstructed
  from inferred effect support.
- Merely using `H` as callee does not make `H`'s own invocation a recipient
  of its public callee view. A receipt for the argument does not produce
  the missing callable slot/view profile.
- Receiving a typed binding records ownership of that use; it creates no
  boundary or concrete contract.

The literal's lack of events and the absence of handlers thus do not prove
that all callback/view profile fields are empty. An independent declaration
with no applicable boundary positions could make a corresponding profile
empty, but proving that declaration/view formation is the unresolved datum;
it cannot be inserted as an unexplained assumption and called a generated
`chi_Int`. Neither the source call rule nor map algebra alone constructs it.

This is a bounded failure to complete the certificate from the supplied
rules, not a semantic impossibility or a source rejection. No actual `id`
body, receipt or behavior is inspected to certify admission. No request
trace, Unit transport or new profile rule is added.

## 7. Precision repair proposed for the earlier note

Leave `2026-10-06-function-int-context-fresh-certificate.md` untouched in
this worker lease. Return the following repair to the primary:

1. Replace the claim that the typed map itself is the first missing source
   rule with: the map's **form is conditionally generated** by the existing
   typed-structure clauses; independently typed call/port/binding and
   compatible decorated slot/view data remain unproved.
2. In the `M_Int`/receipt rows, cite typed-boundary §6 lines 763–789 for
   identity and result-prefix removal. Distinguish that conditional map from
   an independently formed full receiver/profile certificate.
3. Retain the earlier stop-before-Initial conclusion, local constructor
   facts, no-`Q` requirement and production/Option 2 boundaries. Refocus its
   next obligation on independent decorated source slot/view formation,
   rather than adoption of a new correspondence rule.

This is a proposed precision repair for primary adjudication/review. It
does not undo a selected language meaning or certify the repaired previous
artifact; this producer cannot independently review its own record.

Recommended next action: resolve an independent source declaration/formation
certificate for the known Int callable slot and complete executing view,
including its original applicable profile and receiver scope. Once that
datum is supplied, use the existing conditional map/receipt rules and
Initial; do not invent another map rule or assume Function comparison
success. Option 2 extras, exhaustive admission and production conformance
remain separate open obligations.

## 8. Checks, omissions, resources and frozen review handoff

Checks: committed source/authority reads at §2's exact sections; targeted
line searches verifying the previously omitted typed-structure paragraph;
ten dependency blob identities checked read-only; output lease absence and
final dependency/scope/hash recheck at handoff. No semantic worktree
replacement or previous review verdict was used as a proof premise.

No executable oracle/model, seeds/ranges, mutation, test, build, formatter,
benchmark, production edit or Git mutation ran. The correspondence proof
shares the selected conditional typed-source premises with its governing
transport package; it does not independently validate source typing or
profile formation. The local scalar/profile reasoning is not an oracle
for whole Function admission. Independent review of this note is pending.

Coverage: fresh scalar/result/delay, conditional typed map, all Initial
premises, local-versus-complete empty profile, and exact repair proposal.
Omitted: the stopped decorated slot/view formation, full admissible context
fiber, raw syntax-to-decoration generation, actual filling behavior,
arbitrary histories/adapters/state, production-only extras, complete
production observation containment and principality.

Resources: one producer, no children/heavy process; captured lightweight
commands each below one second. Aggregate CPU/memory/reasoning wall time
uninstrumented; no incomplete enumeration or timeout. Writes stop before
submission for frozen review. Prior files and shared records remain intact.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-function-int-source-initial-certificate.md` only.
- Baseline SHA: `d2837d34026c262280e19e66085992bf480f7cf2`.
- Changed dependency hashes: none at baseline verification; all ten direct Git blobs are pinned in §2 and rechecked at handoff.
- Claim/review status: frozen unreviewed research-only partial conditional source proof; `M_Int` rule instantiated conditionally, no complete `chi_Int` or Initial admission claimed.
- Checks already run: committed governing/authority/previous-record reads, ten blob identities, lease absence and final scope/hash/dependency recheck; zero tests/builds/models.
- Proposed one-line checkpoint commit message: `research: derive conditional Int path map and isolate Initial view premise`.
- Shared-record deltas intentionally deferred to primary/curator: the exact prior-note precision repair in §7 and corresponding task/theory premise wording; retain decorated certificate, Option 2, exhaustive admission and production gates. No shared or prior artifact was modified.
