# Int-literal callback admission: adversarial premise audit

Date: 2026-10-05
Status: Unreviewed conditional research; frozen on handoff
Baseline: `b35803eb6bc8c028510c61aa05d7e95a865ad664`
Gate/method: Int-literal admission bridge; minimized missing-premise reasoning
Implementation authority: none

## Objective and bounded result

Test whether an Int literal can supply a complete admitted callback challenge,
or whether a proposed bridge silently creates its receiver/profile/incidence
decorations. No source counterexample to the fully decorated conditional
bridge was found. The smallest incomplete certificate is already the
punctured call `H 0`: literal synthesis supplies its value/result interface,
but the admission rule requires independently supplied context evidence.
This is a blocked derivation, not an asserted rejected Yulang program or an
unsoundness witness for the selected source semantics.

Only the pinned revision was used for substantive claims. The initial live
reads were replaced by pinned reads. Governing sections are callback-context
delivery §§2–4 and 8; source-generated callback theorem §§2–3; source contracts
§§2–3 and 5–7; and their direct typed-core dependency §§2–3, 6, 8–9.
`tasks/current.md` supplies accepted decisions and the current production gap.
The inspected source-contract clauses are conditional; their language is not
silently promoted to selected production formation/admission rules.

## Smallest route and its first missing premise

Let `H` be the declared callable hole at the supplied callback slot, without
assuming anything about the actual callable later inserted there. The
one-call, one-literal source shape is

```text
call(result(name H), result(literal 0))
```

It is proof-core notation. The independently justified local route is

```text
literal 0 : Value(Int)
Result(Value(Int)) = Comp(empty,Int)
Normalize(Value(Int), literal 0) = result(literal 0)
X[result(literal 0)] = Return(0)
whole call argument = Delay(Return(0))
```

The first four steps follow from typed-core §§3 and 6 for an admitted literal
typing premise. The final step is the inert argument construction of typed-core
§3, conditional on the call derivation. It does not execute the argument.
For an actual Value-entry callable, §9 then requires receiver activation,
its original source boundaries and receipt, the designated argument Force,
typed result rebind, body, consumer and return. The scalar leaf supplies none
of those context references. In particular `Comp(empty,Int)` does not identify
a static slot, its profile, or its typed argument/return incidence.

Theorem C §3's Initial rule explicitly takes a carrier's declared result
port, profile and path. Its enclosing certificate additionally takes the
known slot, compatible decorated owner/view context and one `nu,K,D`.
Therefore the candidate inference

```text
result(literal 0) : Comp(empty,Int)
----------------------------------  [unsupported]
Initial(H 0) is an admitted complete callback challenge
```

has a missing context premise even before any request or future interaction.
Adding more literal values or execution steps does not repair that inference.
This witness is minimal in the inspected first-order call fragment: removing
the literal removes the Int actual, while removing the call removes the
callback-invocation admission obligation.

## Exact hypotheses under which the missing step follows

The same route is admitted conditionally if the proof packet independently
provides all of the following at their original scopes:

1. A lexical declaration for `H`, its instantiated complete callback contract,
   static slot `beta`, original `Slots(beta)`, and the source-typed punctured
   context that uses that hole. The hole's declaration can be used; the pending
   comparison with the eventual filling cannot be used.
2. The actual receiver/entry and source-owned argument receipt and Force/rebind
   paths, with distinct callback-value receipt and invocation-argument receipt
   where the enclosing construction includes both.
3. The original typed correspondence of carrier/result/complete-call ports,
   with `d-`, `d+`, `b+` retained as distinct incidences where present. Empty
   request support does not delete these identities or routing-profile presence.
4. One jointly consistent, well-formed complete fiber `xi=(nu,K,D)` satisfying
   the local literal endpoint constraint and every retained context/contract
   predicate. Separate endpoint or row witnesses do not establish this.
5. An independently interpreted admission inventory and local descriptor typing
   evidence; the source membership graph alone does not provide them.

Under these hypotheses, the Initial rule admits the empty interaction prefix;
the actual Value inlet can force `Return(0)` and rebind its Int result by the
supplied path. No Function-query success is needed for this admission step.
No request/response/resumption case is needed for this smallest witness.
This is a conditional rule instantiation, not a derivation of those five
hypotheses from bare source text or current production endpoints.

## Why the other cited bridges do not fill the hole

Callback-context delivery §2 starts with an already resolved and instantiated
formal, slot and profile. Step 6 leaves complete Function formation as an
obligation. Its literal rule selects Handler introduction, while an existing
Pure callable preserves its actual role and entry under §4. Neither path can
replace the missing context certificate by the expected value endpoint.

Source-contract §2.2 makes retained predicates active as an additional
interpretation hypothesis. §§3.1–3.3 require the source decorations and separate
admission inventory. §3.5 assumes local descriptor typing lemmas. Thus active
source incidences cannot be inferred merely because a literal or a retained
reference exists. Theorem C §2.6 explicitly refuses an absent path, revived
owner or newly manufactured capture grant; total logical projection cannot
construct those missing premises.

Sections 5.1 and 6.3 require matching whole providers, typed paths, original
constraints and scope legality. Section 7 reconstructs endpoints from an
already independently checked allocation view. Its `forall v satisfying C_V`
statement does not prove that `C_V` has a witness or that an arbitrary literal
call belongs to that view class. Section 3.7's Option 2 extras preserve the
separate admission requirement; membership extensivity cannot imply admission.
This respects the accepted production denotation basis and conservative extras
without selecting their open concrete clauses.

## Method, coverage and failure conditions

This was a textual dependency and inference-premise audit, with no execution
oracle. Its grounding is independent of the proposed bridge: the cited rules
explicitly name their inputs and omitted formation premises. It is not an
independent review of a constructive lane's artifact, which was not consumed.
The audit shares the source/core contracts and accepted decisions with that
lane; it cannot validate those contracts from an external semantics.

The symbolic premise-deletion mutation removes the decorated context from
the Initial rule and leaves the literal/result typing intact. The mutation
fails the displayed rule's premises; it supplies no semantic countermodel.
No numeric ranges, random seeds, executable searches, tests, builds, Oracle
runs, or differential experiments were used. Coverage is one minimal Int
actual, one callable hole, Value entry and empty initial history. Handler
effects, resumed histories, latent outputs, arbitrary annotations, production
descriptor satisfaction and source-wide acceptance remain unverified.

This non-finding would change if a supplied decoration yields incompatible
retained predicates on the same fiber, or if an existing governing source
rule actually generates the omitted context evidence. Neither was established
in the inspected scope. Stop here: selecting a default receiver/profile,
inventing typed paths or guessing a `nu,K,D` model would choose new source rules.

Commands were bounded `git show <baseline>:<path>` reads, narrow `sed`/`rg`
selection, `git ls-tree` dependency identity capture and scoped `git diff
--numstat` for dependency drift. No concurrent heavyweight process was started;
at most one lightweight shell process ran at a time. CPU, peak memory and
wall-time were not instrumented. The primary owns final whitespace/hash checks.

## Frozen dependencies and handoff

Pinned semantic dependency Git blob IDs:

| Path | Blob |
| --- | --- |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
| `tasks/current.md` | `8b3e7363d7f15e3fbe791457e1acc833dd10f538` |

The semantic dependencies showed no drift from the baseline in the scoped
working-tree comparison. `tasks/current.md` had concurrent changes (11 added,
10 removed lines); only its pinned version was used. No dependency was edited
by this worker. Primary revalidation remains necessary before integration.

Recommended next action: require the constructive Int bridge to expose one
complete independent context certificate and joint fiber, with literal
synthesis and supplied decoration hypotheses separately identified.

Commit packet: exact lease
`notes/progress/2026-10-05-int-literal-view-falsification.md`; baseline
`b35803eb6bc8c028510c61aa05d7e95a865ad664`; dependency identities above;
unreviewed conditional non-finding, research-only, frozen at handoff; checks
already run are the scoped source/dependency reads and drift comparison, with
no executable validation. Proposed message:
`research: isolate Int-literal callback admission context premises`.
Shared-record deltas intentionally left for primary/curator: optionally link
this audit from the active Int bridge status; keep source-admission and production
formation gates open; no authority/index/task/question-board change is proposed.
