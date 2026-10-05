# Fresh Int context: partial construction stops before Initial

Date: 2026-10-06 (assigned artifact date)
Status: frozen unreviewed partial conditional source derivation; decorated context open
Baseline: `7cdc4e47f162ed6afe7d41a26e5ebbeea5e4f2ac`
Exclusive lease: this file only
Implementation authority: none
Method: construct fresh source operands, then audit generation of each required decorated field

## 1. Outcome and exact first missing premise

A fresh Int literal/result/delay construction is available without any Unit
transport. The supplied rules do not complete a fresh `chi_Int`: the first
unproved decorated incidence is the typed correspondence joining the whole
carrier's designated result port to the receiver's parameter/rebind path.
That correspondence is an input to `Receive` and `RebindResultPath`, not an
output established merely by naming the two Int endpoints.

The kernel follow-up makes this boundary explicit. Source-role §10 writes
`Receive(u,parameter,t,typed correspondence)`. Typed-boundary §6 says a
typed-value-flow derivation **supplies** path correspondences and source
elaboration **supplies** signature profiles. Neither clause constructs that
derivation/profile for this new punctured source call. Typed-core §6 also
retains admitted annotation/typed-flow premises at receipt paths. Theorem C
§2.1 takes these decorations as input; §3 Initial needs their profile/path.

The construction therefore stops before Initial. No `chi_Int`, valid
complete fresh fiber, or admitted challenge is claimed. There is no assumed
cross-form check, borrowed Unit witness, or assumption that the pending
Function comparison succeeds.

## 2. Fixed baseline and source identities

The full assigned commit was resolved read-only before the pinned reads:
`git rev-parse 7cdc4e47f162ed6afe7d41a26e5ebbeea5e4f2ac` returned that exact
SHA. All semantic/kernel inputs below were read from that committed object,
not a worktree replacement. The previous artifacts were not edited or used
to certify this construction.

| Input | Exact scope used | Git blob |
| --- | --- | --- |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §2 supplied typed paths/Flow/receipt/constraints; §3 call delay; §6 literal, result, parameter and retained path premises | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | §2.1 decorated source inputs; §3 punctured certificate and Initial premises | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | §21 unannotated Value parameter and whole inert argument | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §3, lines 91–179: delay, invocation frame, receipt before entry, result rebinding | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | §1 supplied positions/profiles; §4 incomplete profile elaboration; §10, lines 573–613: Invoke/Receive/Rebind | `10775573537d8b56423f796db3c7ac6bb427e252` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §6, lines 665–754, 792–832, 1020–1027: profile introduction, supplied maps, ledger transport and receipt | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | d1 decisions 1–5: independent contexts, direct whole-carrier/callable inputs, retained original evidence | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | d1 decisions 1–5: original complete `Rel_C`, independent predicates, concrete clauses open | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | d1 decisions 1–4: Option 2 extras; source certificates not exhaustive production membership | `fb4a169a2d748422490cc74c026338587290e90c` |

The ordinary source-machine, source-role and typed-boundary packages retain
their Draft/conditional scope and stated realization gaps. The charter's
selected entry/reification principles and the approved domain decisions are
preserved. This partial proof does not promote a candidate kernel rule to
production authority. Previously read research/design-authority/Git-concurrency
rules govern the disjoint lease.

## 3. Fresh declaration and generated local operands

Use new proof labels for this construction only. No original Unit slot,
assignment, profile, binder, path or primitive is reused.

The source context has a callable hole `H`. Declare its parameter source
interface `Value(a)`, choose `a=Int`, and for the terminal identity-shaped
context declare a result skeleton `Comp(empty,c)` with `c=Int`. These are
independent **hole-interface declarations**, permitted by Theorem C §3;
they do not assert that a filling meets them, or complete a four-port
Function descriptor interpretation. `H` is not another environment value
whose semantic validity assumes the filling's Function membership.

The independent other-value environment is empty. The source argument is

```text
d_1 = literal(1)                   : Value(Int)
c_1 = result(d_1)                  : Comp(empty,Int)
t_1 = Delay(X[c_1], lexical refs)  : the whole inert received carrier.
```

The first two lines follow typed-core §6's literal and result-normalization
rules, using the literal's local Int source relation. The third is §3's
call translation. With no other free values the argument's lexical reference
list is empty; no computation prefix runs to construct it.

At the source-expression level the punctured skeleton is
`call(result(H),c_1)`. This displays derivation constructors, not new user
syntax or an already completed source typing judgment. At its invocation
boundary, the challenge supplies the callable and **whole** `t_1` directly
to their callable/carrier ports. The source argument computation is `c_1`;
its received carrier is `t_1`. Putting an already delayed `t_1` in place of
`c_1` and delaying again would confuse these roles. This construction does
not assert a separate context-abstraction theorem for arbitrary replacement
of the literal argument.

The complete future fiber would be `xi_Int=(nu_Int,K_Int,D_Int)` at its
original scopes. At this stage only the independent endpoint choices
`nu_Int(a)=Int` and `nu_Int(c)=Int` are fixed. Reserving this notation does
not prove an admissible complete `nu_Int`, a complete `K_Int`, or the needed
`D_Int` incidence. Those remain incomplete rather than being set to an
empty ledger to conceal the missing path.

## 4. Required fields and their source-generation status

The symbols for paths and activations in this table are proof labels.
Where a field is open, giving it a name does not generate its witness.

| Required field | Fresh value/shape | What supplied rules generate | Exact open part |
| --- | --- | --- | --- |
| Callable hole | `H`, independently declared parameter `Value(Int)` and terminal Int result skeleton | Theorem C §3 permits the declared hole interface without proving filling satisfaction. | It does not derive a complete compatible known-slot profile/view from that skeleton. |
| Argument provider/result port | Local source node `c_1`, result type Int, source result path `p_1` at that node | Typed-core §6 literal/result rules generate the local provider and its result interface; §3 retains its code under Delay. | No receiver correspondence is generated just by the local port. |
| Whole argument | The inert carrier `t_1` of the entire `c_1` | Typed-core §3 and ordinary-computation §3 prescribe Delay without execution prefix or state snapshot. | Its complete typed receipt/view packet at the receiver is not derived by allocating the delay. |
| Parameter/rebind path | A receiver parameter-result/value path `p_H`, typed Int, to be related to `p_1` | Value entry requires a designated Force followed by typed result rebinding (charter §21; typed-core §6). | **First non-derivable incidence:** the actual typed correspondence `M_Int(p_1,p_H)` and its relation to the carrier's designated Force port have not been generated. Equal Int endpoints alone do not supply it. |
| Receiver and invocation | A fresh invocation occurrence `u_H` when the hole filling is actually invoked; receiver role remains the filling's actual role | Ordinary-computation §3 and source-role §10 prescribe entering one invocation under the current configuration. | This operational allocation schema is not an independently valid punctured-context/typed-receiver certificate before filling. It does not supply `M_Int`. |
| Argument receipt | Required `Receive(u_H,parameter,t_1,M_Int)` | Typed-boundary §6 records receipt when a invocation obtains a view at a typed binding; it creates ownership of that use and no contract. | The rule requires the typed correspondence. Recording the receipt with an unknown map would assume the missing field. |
| Known slot/view | Reserve a fresh slot label `beta_Int` belonging to this context only | Source certificates require an independently known instantiated slot/view. A proof label may be fresh. | No rule here turns the reserved label and scalar declarations into that compatible typed slot/view. |
| Signature profile | Required `Gamma_beta` and its original protected/concrete-contract computation positions | Typed-boundary §6 defines boundary introduction using the source profile and distinguishes protection from concrete grants. | It explicitly says source elaboration supplies profiles. Empty effects/environment do not justify choosing an empty profile or defining its positions by row support. |
| Profile incidence/authority | Required boundary `b=(receiver,slot,Gamma_beta,endpoints)` and carried profile incidence | Typed-boundary §6 transports a supplied profile along supplied path maps; receipt itself grants no capture contract. | Profile introduction/compatibility for this fresh source context is open. No grant or protection is fabricated to fill the field. |
| Lexical scopes | Context root scope; separate identity-parameter scope only on the later actual side; no other free-value binders | Theorem C preallocates source labels/binders; typed-core §6 produces the unannotated parameter scope and body binding on lambda synthesis. | The complete scope-incidence link among slot, receiver, carrier/result paths and local witnesses is not generated by empty environment alone. No binder is hidden per segment. |
| `K_Int` | Shared original predicates and endpoint constraints before any `Q` | Typed-boundary transport keeps the same `K` under one assignment; it does not reconstruct or freshen its truth conditions. | The full source-call contract predicates are not emitted by the local literal rules. Known endpoint assignments are only part of the required constraints. |
| `D_Int` | Incidences of those same predicates at callable, carrier, result/rebind and view paths | With a typed map `M`, typed-boundary §6 gives `D' = M_*D`, retaining original predicate identities. | The relevant source incidences and `M_Int` must already exist. The transport equation cannot create an input incidence or prove its semantic validity. |
| Configuration/history | Empty other environment; no ambient operation handler/request; initial history empty | The literal/identity source shapes need no Response/Resume witness. | These empty extension cases do not validate the initial receiver/view/profile configuration. Initial still needs its complete premises. |

The first stop is therefore not a Unit/Int type mismatch. Both local scalar
endpoints are deliberately Int in this fresh attempt. It is a missing typed
**incidence derivation**. The table identifies downstream unresolved fields
without pretending to continue their construction after that stop.

## 5. Why the kernel does not discharge the missing incidence

The additional kernel sources were inspected specifically to avoid assuming
that Theorem C's imported decorations must remain unexplained forever:

- Ordinary-computation §3 states that source boundary instances and the
  typed receipt precede entry. It says `RebindResultPath` abbreviates the
  existing typed-path transport/receipt relation. This fixes execution order
  and the relation to preserve; it does not derive this context's path map.
- Source-role §10 makes the parameter explicit:
  `Receive(u,parameter,t,typed correspondence)`. Result rebinding transports
  matching result/value paths under the same assignment and `K,D`. It does
  not create a contract or supply a previously missing correspondence.
- Typed-boundary §6 takes monomorphic source descriptors/positions as input,
  says typed-flow derivations supply maps, and says source elaboration supplies
  profiles. Its relational-image theorem proves preservation **given** those
  maps/profiles. Lines 1020–1027 keep deriving profiles, correspondences and
  source typing/acceptance as a realization obligation.
- Typed-core §6 derives the unannotated role/entry skeleton while retaining
  admitted annotation/typed-flow premises at receipt paths. Its application
  clause states the whole-argument/path/contract obligation, not a concrete
  inference rule closing it in this fresh context.
- Theorem C §2.1 takes decorated kernel witnesses before the tested query;
  §3 Initial requires the independently typed carrier's declared result port,
  profile and path in the compatible punctured context.

Consequently no inspected rule supplies the missing `M_Int` and associated
profile/context certificate from just the declared hole and local literal.
This is a bounded missing-premise finding in these named sources, not a proof
that no such source derivation can exist or that a richer carrier is needed.

## 6. Actual identity side and independence of `Q`

Only when describing a possible actual filling, independently synthesize
`id x=x`: unannotated `x` produces a fresh value endpoint `A_f`, body binding
`Value(A_f)`, name body and `Comp(empty,A_f)` result, with actual Pure
introduction and Value entry. The fresh intended Int instance can choose
`nu_Int(A_f)=Int` consistently with that local synthesis. The actual body is
not regenerated from the hole's expected endpoints.

This does not supply the hole's missing path/profile certificate. Actual
invocation would require its receipt before Force/rebind/body; assuming that
the filling satisfies the hole contract in order to certify this receiver
context would reintroduce the forbidden comparison premise. No actual
behavior claim is used to admit the challenge here.

All generated/declaration steps above are independent of `Q`. The unresolved
fields must also be generated or independently licensed before `Q`; using
success of `Q`, `D_checked subseteq D_actual`, or eventual output compliance
to fill them is not allowed. The correct report is **Initial not yet
derivable**, not “admitted because Int matches,” and not a rejection of the
source program.

If an independent source construction supplies `M_Int`, original profile,
receipt/context compatibility, scope and joint constraint incidences, the
existing Theorem C Initial rule can be applied under those explicit premises.
This conditional continuation is not a completed `chi_Int` or an exhaustive
production definition. Option 2 extra observations, complete production
membership and source/production conformance remain separate open gates.

## 7. Exact next obligation, checks and omissions

Recommended next action: require a source-generation lemma for the fresh
typed correspondence from the Int literal carrier's designated computation/
result port to the declared Value(Int) receiver/result-binding path, including
its original profile and joint `K,D` incidence. Its input must be the
independent source declarations/derivations, not a preexisting compatible
`chi_Int` or Function comparison success. If those rules require a new
durable interpretation, return the exact missing clause for the primary's
authority gate.

Checks: exact baseline resolution; committed section reads listed in §2;
kernel searches for Invoke/Receive/Flow/profile premises; nine direct
dependency identities checked by read-only `git rev-parse BASE:path`; lease
absence and final output/dependency scope/hash rechecks at handoff. No live
semantic replacement or previous producer verdict was consumed as authority.

There is no executable oracle. The partial proof uses the selected source
role/reification decisions and explicitly bounded conditional kernel rules;
it does not validate them with a checker assuming their transitions.
No models, seeds/ranges, mutations, tests, builds, benchmarks, formatters,
code edits or Git mutations ran. Independent review remains pending.

Coverage: fresh scalar/literal construction, declared callable context,
whole-argument delay, generation status of every Initial decoration, and the
named kernel's typed-flow/profile realization boundary. Omitted: the stopped
incidence/profile construction, complete fiber/context formation, source
acceptance, arbitrary request/resumption/future histories, adaptations,
mutable state, exhaustive production-only extras, production correspondence
and principality. No source counterexample or general impossibility claim
is made.

Resources: one producer, no children or heavyweight process; lightweight
captured commands each below one second. Aggregate CPU/memory/reasoning wall
time uninstrumented; no unfinished enumeration or timeout. The file is frozen
before submission. Previous artifacts and all shared records remain untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-function-int-context-fresh-certificate.md` only.
- Baseline SHA: `7cdc4e47f162ed6afe7d41a26e5ebbeea5e4f2ac`.
- Changed dependency hashes: none at baseline verification; all nine direct Git blobs are pinned in §2 and rechecked at handoff.
- Claim/review status: frozen research-only unreviewed partial conditional source derivation and bounded field-generation audit; no `chi_Int` or Initial admission established.
- Checks already run: baseline resolution, committed source/authority/kernel reads, nine dependency identities, output lease absence and final scope/hash/dependency recheck; zero tests/builds/models.
- Proposed one-line checkpoint commit message: `research: stop fresh Int inlet certificate at typed receipt correspondence`.
- Shared-record deltas intentionally deferred to primary/curator: record generated fresh literal/result/delay operands and the first open receipt/rebind path-map/profile formation premise; preserve exhaustive admission, Option 2 and production-conformance gates. No task/index/theory/authority/question file changed.
