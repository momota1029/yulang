# Identity Function: independent admission and same-fiber derivation

Date: 2026-10-06 (assigned artifact date)
Status: frozen unreviewed research; candidate predicates and conditional derivation
Implementation authority: none
Baseline: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`
Exclusive lease: this file only
Method: constructive semantic derivation, with premise isolation; no executable probe

## 1. Objective and result

Try to interpret retained identity-Function evidence independently of a pending
Function comparison, first for an Int-returning carrier and then for a carrier
that requests before returning an Int. The approved answers determine the
quantifier domain and observation basis, but do not determine an exhaustive
production admission or satisfaction predicate. The formulas below separate
that missing interpretation from a constructive reduction already present in
the typed core. They are candidates, not adopted rules.

The first missing premise is already encountered at the empty-history call:
an independently interpreted, complete inlet/path judgment relating the
**whole** carrier to `Value(Int)` and its retained contract. A result-path type
of Int alone does not supply that judgment. Typed-core §6 gives its intended
source shape, while leaving the endpoint/path realization open. Retained F5
rows, insertion receipts and parameter sharing supply neither its definition
nor its completeness proof.

Once this inlet premise and the existing decorated entry premises are supplied,
the identity reduction preserves an entry request and attaches the identity
suffix to its original continuation. Theorem C then supplies a sufficient
source-generated linked-lift subcase. It cannot establish containment of all
Option 2 production observations or exhaustiveness of the approved domain.

## 2. Fixed authority and dependencies

All semantic inputs were read from committed objects at the baseline, including
where worktree replacements exist. The primary's accepted decisions are:

- `production-function-inlet-context-domain/q1/d1`, exact embedded decisions
  1–5: all independently well-typed compatible punctured caller contexts at
  fixed original `(nu,K,D)`; direct callable and whole-carrier holes; other
  environment values independently valid with joint evidence; admission
  independent of the tested comparison; no exhaustive rule approval.
- `production-function-denotation/q1/d1`, exact embedded decisions 1–5:
  Option A uses complete original `Rel_C` fibers with independently interpreted
  endpoint, role/entry, path, origin, continuation, scope, authority and
  dependency constraints; complete concrete clauses remain open.
- `production-function-bound-membership/q1/d1`, exact embedded decisions 1–4:
  Option 2 permits independently licensed conservative observations without
  mandatory source-constructor witnesses; Theorem C and `P_ref` remain a
  source-generated result; matching four ports is insufficient.

Exact governing sections and object identities:

| Input | Governing location | Git blob |
| --- | --- | --- |
| Approved inlet answer | embedded decisions 1–5 | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| Approved denotation answer | embedded decisions 1–5 | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| Approved membership answer | embedded decisions 1–4 | `fb4a169a2d748422490cc74c026338587290e90c` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | §§2.1–2.2, 3.1–3.7, 10 | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §6 parameter/body/application rules, lines 303–425; §9 entry and joint containment, lines 904–1137 | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | §§2.1–2.6, 3; linked-lift Theorem C | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | “One semantic carrier”; “Candidate Function contract over the same relation,” lines 930–1004 | `841325b72ab797729b9f26d4569007ec6694c99b` |
| `notes/progress/2026-10-06-function-f5-endpoint-inventory.md` | §§3–5, identity facts and missing interpretation | `9a12c7bc58096fb0340ee9da6d7fb4a0a6d60a55` |
| `notes/progress/2026-10-05-production-function-inlet-admission-audit.md` | “Conditional source-call derivation”; “Required production gate” | `b87fb96ded029deaa6efdc419e323a4c31191bb9` |

The two core documents retain their Draft/candidate scope; source-contracts
and Theorem C retain conditional theorem status. The answers supersede a
source-tight interpretation of production membership. No status is promoted
by this note. `notes/design/INDEX.md` and `tasks/current.md` were used only as
committed routing context. Research, design-authority and Git-concurrency
rules were read; no shared record was edited.

## 3. Candidate predicates: explicit dependency boundary

Let `A` denote the actual description, `C` the checked description, and
`xi=(nu,K,D)` one original fiber with its original binder tree. Here `C` is
not a caller-context symbol. A challenge `h` records the punctured context,
other environment values, actual callable, inert carrier, initial decorated
configuration and a finite input/history development. A witness `w` records
the existing typed paths, provider identities, operation instances, raw
handles, current states and logical witnesses. This is metatheoretic notation
over retained evidence, not a proposed solver carrier.

An explicit candidate admission schema is:

```text
Adm_A^cand(h;xi) iff there exist pi,eta,w at their original scopes such that
  HoleCtx_A(pi; h.context, xi)
  and OtherEnv(pi,eta;xi)
  and Inlet_A(pi; h.callable,h.carrier,h.initial,w,xi)
  and LegalHistory(pi; h.history,w,xi)
  and Joint(K,D; h,eta,w,xi).
```

The intended independent premises are precise:

1. `HoleCtx_A` checks the punctured context against a *declared* interface
   assumption for its holes. It contains no proof that the callable filling
   satisfies that interface. The holes receive the callable and the whole
   carrier directly; the tested callable is absent from `OtherEnv`.
2. `OtherEnv` independently validates all other supplied values and their
   shared provider dependencies. It cannot obtain their validity from the
   pending query or assume the filling's output contract. Recursive semantic
   environments need an independently grounded interpretation; this schema
   does not solve that additional issue.
3. `Inlet_A` relates the whole carrier and its designated demand/result path
   to the parameter contract and actual role/entry, under the original
   configuration, scopes and authority. It must preserve carrier effects
   and future-use dependencies even when the designated result is Int.
4. `LegalHistory` extends a prefix only by a response at its exposed request,
   reentry of its retained raw handle, or use of an actually returned provider
   at its retained typed port. Witnesses remain those of that history and
   current resumed configuration. This is an independent rule schema,
   not a proof that the rules are exhaustive for production.
5. `Joint` evaluates original formulas and all their incidences on one
   shared tuple; it does not independently existentially hide each segment.

The corresponding candidate satisfaction schema is:

```text
Sat_A^cand(h,O,w;xi) iff
  (nu,O) belongs to the original complete Rel_C fiber
  and Endpoints_A(h,O,w;xi)
  and RoleEntry_A(h,O,w;xi)
  and Paths_A(h,O,w;xi)
  and OriginContinuation_A(h,O,w;xi)
  and ScopeAuthority_A(h,O,w;xi)
  and Joint(K,D;h,O,w,xi).
```

`Endpoints_A` must say which retained endpoint constrains each complete
observation, including genuine guarantee bounds and latent interfaces;
`RoleEntry_A` uses actual source introduction and entry; `Paths_A` checks
designated typed incidences; origin/continuation uses original operation
witnesses and raw suffixes; scope/authority validates the original binder
positions, receiver lineage and current grants. No conjunct tests Function
comparison success, the desired inclusion, or membership in `P_ref`.
Neither success of four port comparisons nor an insertion receipt is a
substitute for these predicates.

These are **explicit candidate signatures and dependency separation**, not
completed definitions: `HoleCtx_A`, `Inlet_A` and exhaustive `Endpoints_A`
are not supplied by the pinned production contract. In particular, calling
them “independent” in a formula does not prove independence or completeness.
The finite ground interpretation below fills a source-generated sufficient
subcase only. Turning either schema into a total production predicate
requires the missing independently interpreted clauses and conformance map.

Once those clauses exist, write

```text
D_A(xi) = { h | Adm_A(h;xi) }
P_A(h;xi) = { Pi_xi(O) | Sat_A(h,O,w;xi), with w at original scopes }.
```

The same construction applies to `C`. Admission is not defined by whether
`P_A(h)` is empty, has only successful returns, or satisfies `P_C(h)`.
An admitted divergent carrier can have no return and still have prefixes.

## 4. Smallest constructive subcase

Use the production-admitted source `my id x = x`, with actual Value entry,
and instantiate its shared value coordinate at Int. The pinned F5 inventory
gives one parameter/body coordinate `p` and the five facts

```text
EffectBottom+ <: e_b       e_b <: EmptyEffect-
EffectBottom+ <: e_l       e_l <: EmptyEffect-
Function(p-,EmptyEffect-,e_b+,p+) <: root.
```

These facts retain structural correlations and the pure body link. They do
not define a whole-argument endpoint, context admission, or complete-call
effect denotation. This derivation uses the inventory as a committed bounded
source characterization; it does not independently re-audit its code paths.

Supply a decorated, independently typed direct-call context with callable
and carrier holes, no other free values and no eligible handler. Let `B`
be the initial configuration and let `r_id` be its actual receiver receipt.
Use two inert carriers:

```text
t_0 : designated execution Return(0,B), result path Int
t_q : designated execution Request(q,Unit,B,k), result path Int
k(z,B') = Return(z,B') for a response z : Int.
```

`q` is one declared operation instance with Unit payload and Int response;
its original type-instance map, origin and continuation are retained. These
are descriptions of existing carriers/relations, not additional surface
syntax. The construction of either carrier is inert.

The explicit source-subcase hypotheses are:

- the supplied context and carrier have independent decorated source
  certificates with the original `xi`, typed ports and sharing;
- its local whole-carrier inlet/path certificate relates `t_0` or `t_q` to
  `Value(Int)` without invoking the pending whole-Function comparison;
- all original `K` formulas hold jointly, scopes are valid and the context
  has the required receiver/argument paths without manufacturing a grant;
- the source primitive certificates, actual receipt and typed-core §9 entry
  equations apply; the context exposes rather than handles `q`;
- legal response/resumption extensions retain the same request witness,
  handle and current state. No one-shot/linearity restriction is assumed.

For these certificates, `Adm_A^src` is just their conjunction and the
independently certified finite history rules above. It checks no execution
output against a checked bound. Its empty prefix is admitted before any
return or request is observed. `Sat_A^src` conjoins the original relation,
those same scoped certificates, actual receipt/entry, the designated return
type Int, and the original request/response/continuation relations. This
provides source witnesses sufficient for the corresponding candidate
conjuncts **if** their independent production interpretation validates them.
It is not a definition of complete production membership as source images.

Write the identity suffix, at the current state, as

```text
S(z,B') = RebindResultPath(t,z,B'); result(x=z); ReturnFromInvocation.
```

The two reductions under the supplied premises are:

```text
Invoke(id,t_0,B)
  = establish r_id; Force_argument(t_0) >>= S
  = establish r_id; S(0,B).

Invoke(id,t_q,B)
  = establish r_id; Force_argument(t_q) >>= S
  = establish r_id; Request(q,Unit,B, lambda(z,B'). k(z,B') >>= S).
```

The second follows directly from typed-core §9 and Theorem C §2.3's bind
equation. At an admitted response `z:Int`, the raw suffix returns that same
`z` through typed rebind and the identity body at `B'`. Receipt and argument
entry are not replayed. Reusing a retained raw handle follows that same
suffix with the same operation-local witness; a finite multi-resumption
development does not create independent copies of the original shared
type assignment. Current-state dependence is retained throughout.

The request prefix is an observation even if no response is ever supplied.
Thus `J_body=Comp(empty,Int)` does not imply that complete `J_call` is pure.
Likewise the argument's eventual Int does not replace its `J_arg`: replacing
`t_q` by the returned `z` removes the request and its suspended suffix.
No exact row-union meaning or interpretation of printed `never` is needed
for this reduction. An arbitrary surrounding context might handle the
request, but its handler image must then be derived in that context.

The smallest discriminating witness for the *carrier-as-value shortcut* is
one Value-entry identity, one Unit-to-Int request and its Int-returning raw
continuation, with no ambient handler. Removing the request removes the
distinction; removing Value entry removes this entry demand. This is a
conditional semantic witness against that shortcut, not a new compiler
acceptance counterexample or a minimized witness over the full language.

## 5. Exact containment obligation and available sufficient theorem

At every fixed original `xi`, the required law is

```text
D_C(xi) subseteq D_A(xi)
forall h in D_C(xi). P_A(h;xi) subseteq P_C(h;xi).
```

Both inclusions retain complete joint tuples and histories. No witness can
be selected independently per effect row, result value, resumption segment
or future call. Only legal local witnesses are hidden at original scopes,
and one whole-observation `Pi_xi` is applied afterwards. In particular,
`forall h exists w` cannot be replaced by an unrelated choice for every
projected coordinate, and changing `nu` between the two sides is invalid.

The conditional soundness argument is immediate once these premises hold:
every checked challenge is an actual challenge; satisfaction of the actual
contract places its execution observations in `P_A(h)`; the joint inclusion
places them in `P_C(h)`. This argument proves the implication from the two
inclusions, not either inclusion or production execution coverage.

For the identity's decorated source-generated linked Pure-value lift,
Theorem C §3 supplies an independent source challenge framework. Its actual
Value inlet imposes no support-purity test from Pure introduction or `never`;
the checked source challenge has the same typed result path and whole
carrier. Section 2.6 retains the old whole witness and adds total derived
coordinates without strengthening old segment predicates. Induction over
the two displayed reductions and every finite legal response/resumption
development then preserves the old observations; the source theorem covers
finite latent-provider uses when such providers are present. This is the
existing source-generated `P_ref` sufficient subcase, subject to its exact
source/primitive/decoration and checked-template hypotheses.

It proves neither `D_C^prod subseteq D_A^prod` nor
`P_A^prod subseteq P_C^prod`: production may admit contexts outside its
source-certificate envelope and complete observations without constructor
witnesses. Merely proving `P_ref subseteq P_A^prod` would give the wrong
direction for the latter obligation. Source-contracts §3.7 offers a
conditional paired `H_G` route with independent `W,Z`, matching whole
parameters, exhaustive grammars, compatible admission and hard-envelope
inclusion. Those additional premises are not consequences of the three
approved answers; neither `W/Z` nor their grammar is selected here.

## 6. Precise blocker and stopping point

The shortest missing admission premise is a total independently interpreted
`Inlet_A`/typed-hole rule at the original retained incidence:

```text
whole carrier J_arg + original result/demand path + parameter Value(Int)
  + receiver/context/contracts + original xi
    -> admissibility judgment with evidence and an exhaustive meaning.
```

Typed-core §6 says to relate the whole `Result(I_a)` to the parameter
interface; it does not define the endpoint/path translation that would
justify treating this as a specific `Result(I_a) <: P` query. Even adopting
that query shape would not prove that local success exhausts source context
typing or production admission. The existing inlet audit records this same
boundary; this note adds the explicit comparison-independent predicate
dependency and identity reduction rather than another supplied-rule checker.

The parallel satisfaction premise is a total interpretation mapping retained
Function/body/effect evidence into every Option A endpoint constraint at its
actual observation incidence, with exhaustive production-only alternatives.
An F5 pure body row is not already a complete-call observation predicate.
Source-contracts §2.2 explicitly hypothesizes active admission/membership
clauses; it does not show that current F5 emits or interprets them.

The missing rule is a semantic/adoption or source-correspondence boundary,
not evidence that a new carrier is needed. Work stops here before choosing
it. No broader probe or additional request count could establish its meaning
while leaving that premise assumed.

## 7. Independence, checks, omissions and resources

There is no executable oracle in this lane. The entry reduction is grounded
in committed source equations; the approved answers independently fix what
the production gate must quantify over. The source certificates and local
primitive relations are shared premises of the derivation and Theorem C.
Consequently the derivation is not independent validation of those source
rules, raw-syntax decoration generation, or their implementation. No checker
assuming these transitions was used to claim they were proved.

Reads used `git show BLOB`, `git show BASE:path | sed -n 'START,ENDp'`,
and targeted `rg -n` searches. A read-only Python `git rev-parse BASE:path`
pass checked all nine direct dependency blob identities in §2. All matched
the primary's six explicitly pinned objects and the three additional
committed inputs. Final output-lease scope and dependency identity rechecks
are recorded in the handoff. Git reads performed no index/ref mutation.

Coverage is a symbolic derivation for one identity source and two carrier
shapes, with arbitrary independently admitted finite response/resumption
extensions in the stated source subcase. It is not bounded executable
enumeration: seeds/ranges and sample counts do not apply. No tests, builds,
formatters, benchmarks, mutations or executable probes ran. The shortcut
witness in §4 is derived, not an executed mutation result.

Omitted: exact all-context typing and environment interpretation; concrete
production endpoint/admission semantics; production-only extras; imports,
mutable state and arbitrary handler images; annotation/adaptation cases;
raw syntax-to-decoration generation; unknown recursive higher-order
interfaces; all-source soundness, principality, effective solving and
implementation. Int results have no latent callable/computation interface
to develop in the displayed witness; general future-provider obligations
remain explicit in §3 and in the conditional source theorem, not erased.

Resources: one producer; only lightweight source/hash/file commands, each
captured command under one second; no heavyweight process, child, or search.
The assigned wall-time ceiling is 15 minutes. CPU and peak memory were not
instrumented. No partial enumeration or timeout result is presented as
complete. Invalidations include changed direct dependencies, a proved
existing total inlet rule omitted by the bounded reads, failure of the
independent source certificates, or a changed endpoint-incidence map.
Independent review remains pending.

Recommended next action: have the primary isolate and adjudicate the total
whole-carrier inlet/path clause for this Int identity, together with its
retained-evidence interpretation and completeness scope. Until that clause
is fixed, preserve this result as an unreviewed conditional source subcase.

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-function-independent-admission-derivation.md` only.
- Baseline SHA: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`.
- Dependency hashes changed: none; nine direct input Git blobs are pinned in §2. The primary must recheck them before integration.
- Claim/review status: frozen, research-only, unreviewed candidate predicate decomposition and conditional identity reduction; no production gate closure or implementation authority.
- Checks already run: committed source/authority reads, nine baseline dependency-identity checks, final leased-note scope and dependency recheck at handoff; zero tests/builds/probes.
- Proposed one-line research-checkpoint commit message: `research: derive identity carrier admission premises on fixed Function fibers`.
- Shared-record deltas intentionally left for primary/curator: link this note from the production Function inlet/admission task and theory dependency entry; record the total inlet/path interpretation as the first unresolved premise and Theorem C as a sufficient source subcase. No task/index/authority/question or theory-map file was edited; no theorem status promotion is proposed.
