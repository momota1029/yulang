# First projection Lambda: transformed export and use construction

Date: 2026-10-08
Status: Draft
Scope: constructive research for the isolated nonrecursive `my id x = x`
Baseline: `9ddcc69a30f2be2039ce05c7abe50c9722dc8559`
Decision: integrated `successor-generalize-root-policy/q1`, answer `a1`,
bundle `ec5e36c91`, receipt at the baseline
Authority / implementation / production cutover: none
Review: producer-authored; independent review pending
Write lease: this file only

## 1. Result and claim classes

An explicit candidate export is

```text
Σ_id = forall q. q -> q
α_id = (ordinary Pure introduction, Value entry,
        default Value result consumer,
        received-result/provider -> returned-result/provider incidence,
        binder/port schema, empty capture inventory).
```

The arrow displays the accepted **body/result** presentation. It does not
assert that invoking the function on an effectful argument is pure. The
incidence entry is one interface wire, instantiated at the receiving use;
it is not a stored Lambda, source relation, execution trace, or relation root
whose unfolding recovers the definition. All source paths used to justify
the wire are compile-time proof inputs and can be discarded after validation.
Whether every listed field is necessary for type checking remains open;
ordinary arrow conventions could make some tags implicit. The provider wire
is a proposed retained interface certificate for observation/capture transport,
not a new public value refinement or a singleton type.

The allocation of information is explicit: `Σ` carries the single binder and
its two shared value-type occurrences; `α` carries the proposed provider/path
incidence and its schema, together with any entry/role/consumer tag not already
fixed by the canonical interpretation of that arrow. If an independently
selected canonical `Σ` decoder fixes ordinary Pure/Value entry and the Value
result consumer, those tags are omitted from `α`. The entry witness below
requires the decoded export to retain demand; it does **not** prove demand
must be stored separately in `α`. If the canonical decoder also supplies the
needed provider incidence, that wire may likewise be omitted. Establishing
such decoder laws is P2/P4; this note assumes no decision on that placement.
The smallest candidate therefore adds only what that decoder cannot recover,
without copying the shared type binder out of `Σ`.

Three different results follow below:

1. **Derivation under the selected source core:** the ordinary parameter and
   body lookup derive Value entry followed by Return of the rebound value.
   Entry requests, raw resumptions, divergence and returned latent providers
   survive this derivation. This uses the existing source/core laws.
2. **Conditional theorem for a finite interface transformation:** replacing
   that source path by the stated port wire preserves the source-base complete
   relation and independent admission if the typed wire and descriptor laws
   P1–P5 below hold. Binder renaming is explicit. No all-inference claim follows.
3. **Candidate abstraction, with open premises:** this wire has not been
   installed as an active legal inferred descriptor or complete query rule.
   Exhaustive Option 2 membership and factorization of every independently
   valid view remain open. The note does not establish the full principal
   scheme acceptance criterion even for `id`.

No `pick y = z` case is included: capture eligibility, environment linkage and
provider transport would introduce additional dependencies into this first case.

## 2. Governing sections and dependencies

The following sources are read at the baseline, rather than from concurrent
shared-record edits:

| Source | Exact sections / use |
| --- | --- |
| Approved q1/a1 and receipt | Decision items 1–5: transformed public export; extra information remains undetermined; no renamed complete source relation; proof/implementation gates retained. |
| FVIEW, `2026-10-05-inferred-function-call-views.md` | §§1.1, 2, 5: annotation/display/internal evidence separation, one joint scoped assignment, stable source identities, independent admission, completed-contract principality and Option 2 conformance. §3 is the `apply f x` formal-use case and is not a rule for `id`. |
| Principal acceptance criteria, `2026-10-04-principal-scheme-acceptance-criteria.md` | Accepted `id : 'a -> 'a`; Existing production value-skeleton evidence; Proof boundary; Common-allowance factorization gate. A presentation must preserve solution families, not merely print correctly. |
| Source contracts, `2026-10-05-source-contracts-and-common-allowance.md` | §§2.1–2.2 active descriptor/membership/admission; §§3.1–3.4 emission, complete histories and whole transport; §3.7 exhaustive Option 2; §5.3 actual-root complete-query certificates. These are conditional contracts, not adopted new primitives. |
| Redesign charter, `2026-09-29-scc-intrusion-redesign-charter.md` | Gates D–E and §§18, 21, 24: result synthesis, source-selected Value entry, ordinary Pure introduction; no production representation approval. |
| Typed core, `2026-10-02-typed-computation-core-elaboration.md` | §6 parameter/name/result synthesis; §9 entry/rebind/pending suffix and complete call image. |
| Context preimage, `2026-10-04-common-allowance-context-preimage.md` | §§1, 6: `forall valid V exists m_V`, scope discipline and actual admissible maps; exact complete-domain conditions in §3. |
| F5 value skeleton, `2026-10-04-production-f5-value-skeleton-selector.md` | Source-generated package and Boundary: same parameter value ordinal in both Function children, effects projected away. |
| Current compiler files | `emit_lambda`, `admit_lambda_fact`, `instantiate_and_route_closed_inner`; `ClosedValueScheme`, `ClosedValueSchemeView`, polarized Function/effect views; shadow `ClosedSchemeRef` and qualified quantifier identities. |

The upstream-only `2ea53e3dd` Generalize document is not an input and supplies
no rule or target here. The live modified theory/index/task records are only
navigation context; they supply no premise of this derivation.

## 3. Source derivation and exact observation target

Consider a definition outside callback context, with no explicit Function
annotation, recursion, free names, adapters or explicit computation parameter.
Let `A` be its fresh value endpoint. Charter §21 and typed core §6 give

```text
P = Value(A)
Gamma_body(x) = Value(A) after entry rebind
lookup x : Value(A)
Result(Value(A)) = Comp(empty,A)
body = result(name x).
```

Charter §24 gives ordinary Pure introduction in this stated context. It does
not derive that role from empty effects, infer a role for a supplied callable,
or discharge the distinct FVIEW provisional-Handler formal rule.

Write `t` for the whole inert argument carrier and `C` for the original
executing configuration. Typed core §9 expands the actual invocation as

```text
EnterReceipt(t,C) ;
Force_argument(t) >>= (a,C').
    RebindResultPath(t,a,C') ;
    result(a) >>= ReturnFromInvocation.
```

`EnterReceipt`, `RebindResultPath` and `ReturnFromInvocation` are the existing
typed boundary/consumer actions, not newly erased identities. The wire
interpretation below retains those actions and their dependencies. Only the
body's resolved parameter lookup is replaced by using the just rebound result.

The observable target is this **whole** operation before one final typed
projection `Pi_xi`, for one original `xi=(nu,K,D)`. For an admitted argument:

- A Return carries the same returned value/provider and current configuration
  into the rebind/body/return suffix. No latent part of `a` is forced there.
- A Request carries its original operation witness, origin, typed response
  endpoint and raw resumption. Its continuation is the original argument
  continuation followed by that same suffix. Resuming does not repeat receipt.
- Every finite prefix and divergence is retained. An admitted divergent
  argument need not return; an empty observed return set proves no admission.
- Later use of a Function, computation datum, record provider or existentially
  packaged provider returned as `a` uses that same original provider/witness
  package. Its arguments, raw suffixes and joint dependencies are unchanged.

This is a source/core derivation conditional on the admitted typed argument,
receipt and primitive laws. It is not derivation of those complete admission
and typing premises from raw source, nor an assertion that `J_call=J_body`.

## 4. Finite export construction and maps

The producer can recognize the general constructor shape: a Value-entry
Lambda whose independently resolved result is its rebound formal, with no
additional body computation. It validates the actual resolution and scope
while it has the source definition. It then emits the displayed shared-binder
arrow and a port incidence certificate. Recognizing this shape does not add a
special typing rule for the identifier `id`.

The candidate use-time schema has these typed ports:

```text
i       whole argument carrier port, supplied by the use
v       result of the designated Value-entry demand on i
o       returned value/provider port, wired to v
q       the single value-type binder used at v and o
b       formal/result position schema under the export's binder scope
```

Its invariant operations are the ordinary Value-entry, typed rebind and
Value-result consumer contracts. Its one additional fact is incidence
`o.provider = v.provider` under the typed result-path transport; it does not
equate arbitrary events with matching type shape. No arbitrary predicate,
whole source relation, body root, source AST, per-history table, or per-port
independently chosen witness belongs to `α_id`. No pending query is a producer
input. The finite schema is constant-sized for this case; referenced generic
primitive contracts and their verification costs are not thereby proved
constant-sized or free.

`b` denotes the validated position schema, with enough original identity to
transport its incidences. It is not a newly inferred `Slots(beta)` inventory
for higher-order formal invocation. This source contains no invocation of
`x`; substituting a Function for `q` does not create a static source call slot.

For independent use `u`, construct one simultaneous action

```text
rho_u(q) = q_u                       fresh and eligible at use scope
rho_u(b) = b_u                       fresh instance of position schema
rho_u(i,v,o) = (i_u,v_u,o_u)         one ordered incidence tuple
rho_u(v.type) = rho_u(o.type) = q_u
rho_u(o.provider = v.provider) = (o_u.provider = v_u.provider).
```

Every dependent profile, binder/path operand and evidence field moves by
that same action. Original rigid imports, operation witnesses, ambient
configuration and jointly attached use-supplied `K,D` remain fixed; they are
not freshened independently or generalized as extra free coordinates. There
are no captured environment endpoints or recursive binders in this case.
Two independent uses have disjoint fresh `q_u,b_u` and local ports; their
caller-supplied providers may legitimately coincide. Fresh type identities
do not force distinct runtime arguments.

The candidate publication is `(Σ_id,α_id)` itself. Its direct use query names
that transformed root. A successful comparison of a retained hidden Lambda
would provide no evidence for this publication.

## 5. Exact premises and conditional preservation theorem

| Premise | Classification and content |
| --- | --- |
| P0 source skeleton | Established selected core clauses in §3 plus scoped lexical resolution; current F5 independently characterizes the shared value ordinal only. Complete raw-source typed decoration is not supplied by F5. |
| P1 finite wire producer | Candidate constructor certificate validates source lookup, exact provider/result transport, boundary actions and every dependency operand before discarding the body. No unexplained source alternative remains. |
| P2 legal active descriptor | Open: the transformed arrow/wire has an existing legal inferred descriptor whose active whole membership/admission clauses are exactly the boundary/entry/result contracts below, not merely four ports or an opaque proof label. |
| P3 primitive laws | Retain actual receipt/rebind/consumer, Return/Request bind and finite-prefix laws at original scopes. `result(name x)` after validated lookup is the same Value-result operation on `v`; future provider interface transport is identity under its actual typed path. No boundary erasure or unproved effect equation is assumed. |
| P4 independent admission | Open: transformed admission accounts for every original initial context, response, raw resumption and future provider use, with the same full argument and joint dependencies; no `Q`, solved row spelling or comparison success creates admission. |
| P5 generalization/hiding | Open beyond the selected value skeleton: `q` and schema-local ports are eligible at the definition/use scopes, all rigid/ambient dependencies stay fixed and any hidden local witness has the original joint scope and admission certificate. |
| P6 principal factorization | Open: every independently valid complete public view has an admissible map and actual transformed-root query evidence; exact-public-projection extension must hold, not be assumed from a returned-value type. |
| P7 production extras | Open: exhaustive actual/transformed `W,Z,G` and primitive/future-use contracts are supplied and preserved, or another independently justified complete Option 2 proof is given. Source-base identity does not prove this. |
| P8 production consumer | Open: the eventual consumer interprets these active contracts and preserves atomic publication, required scope guards and whole evidence. Current F5 closed views are insufficient evidence for this premise. |

**Conditional source-base theorem.** Under P0–P5, the source and finite-wire
interpretations have equal independent admitted domains and equal whole
source-base observations, up to the single scope-preserving port map, on each
original fiber. Consequently their images under the same `Pi_xi` agree, and
injective whole freshening preserves this equality at every independent use.

**Proof.** Both interpretations retain the same EnterReceipt and the same
argument demand. At a Return, P1/P3 identify the source's resolved `x` with
the rebound port `v`; both sides perform the same result and invocation
consumer with the same value/provider package and current state. At a Request,
ordinary bind retains the same request and argument continuation and appends
the same just-proved suffix. Induction on any finite request/resumption
development therefore pairs observations and prefixes without bounding the
history length. Divergence and pending suffixes are unchanged because the
argument operation and its complete continuation are unchanged. Future uses
pair by the preserved provider package and identical existing contracts.
P4 gives domain equality independently; relation equality alone cannot give
it. P5 and whole capture-avoiding renaming preserve every occurrence of the
one binder and all dependent operands, so the same proof applies after
`rho_u`. Apply `Pi_xi` only after the whole pairing. QED, conditionally.

The theorem actually removes the source body from use-time inputs; it does
not remove its compile-time validation obligation. P2/P4 are precise missing
rules at the owning transformed-descriptor constructor. A tag interpreted as
"consult the original source relation" would violate both P2 and q1/a1.

**Value-only binder corollary.** In the isolated projected structural package
`Function(A,A) <: r`, replacing the two polarized occurrences of `A` by one
bound `q` and the publication node by its explicit Function predicate gives
an exact renaming of the shared value skeleton. For a direct client constraint
`C(Function(q_u,q_u))`, source extension and fresh-instance extension agree
by substituting `A_u=q_u`, with `r` interpreted at that explicit predicate.
This corollary assumes the isolated root has no omitted pre-existing upper,
environment or cross-definition constraints. It proves binder correlation
and the finite explicit-use extension for this projected package; it is not
all-valid-view principality or full polarized subtyping completeness.

No effect allowance is inferred by this corollary. No concrete-success chain
is composed. The required quantifiers remain `forall source solution exists
transformed solution` and `forall valid V exists m_V`; P6 is not replaced by
`forall V already admitting q-substitution exists q-substitution`.

## 6. Option 2 extension without source-tight membership

Source-base equality alone does not identify production membership with that
base. Source contracts §3.7 allow non-source-witnessed observations. A
conditional bridge here uses paired exhaustive positive abstractions:

```text
M_source = H_Gs(R_source)     M_export = H_Ge(R_wire).
```

Under the port correspondence, P7 must supply exactly the same independent
whole-tuple `W,Z`, all invariant/dependency operands and future-provider
admission rules, with `G_s=G_e` or actual finite proofs in both directions.
The guards retain the original descriptor, guarantees, scopes, authority and
joint `K,D`. The source-base theorem and induction on finite abstraction
derivations then give equality of complete membership: source leaf, unanchored
extra and rewrite step each transport, including every declared alternative.
Independent admission equality must still be proved by P4/P7. This is the
§3.7 theorem specialized to a transformed base, not adoption of its grammar.

If only base inclusion and one guard direction are proved, the conclusion is
that direction of containment, not solution-family equality or principality.
An unmatched extra or abstract provider that changes admission is a failure
of these premises. Taking `W=Z=empty` would only prove a source-tight subcase;
it cannot certify the approved production contract without exhaustive actual
membership accounting. No particular production abstractor is chosen here.

## 7. Smallest discriminating witness and named mutations

The admitted carrier `t = Request(q,C,k)` with `k` returning an Int is enough
to distinguish the proposed complete interface from an implementation that
uses the empty body effect to declare an effect-free complete invocation.
In an independently admitted context without an eligible handler, §9 exposes
that request before returning the Int, although the body `x` has empty effects.
This is one request and one return, with no source callback or recursion.
It is a semantic derivation, not a parsed-source acceptance test.

A zero-request pure divergent carrier separately distinguishes Value entry
from returning/ignoring the inert carrier. It does not itself show an effect
support discrepancy; admission and nontermination must be retained.

The following mutations attack different required premises; none was executed:

| Mutation | Failure condition / discrimination |
| --- | --- |
| Split `q` into independent argument/result binders | Loses the required shared value skeleton and admits unrelated output-type assignments absent from the projected `id` rule. |
| Omit entry demand because the body has empty effects | Loses the one-request witness and the divergent-carrier behavior. |
| Repeat receipt on resume | Changes the request's raw suffix and receiver/path evidence in §9. |
| Deep-force a returned latent value | Runs behavior after entry not selected by §§18/21; Value entry is one designated demand. |
| Freshen returned provider independently | Breaks later use of the actual returned provider and its original witness/contract dependencies. |
| Freshen `K,D` or hide operands separately | Changes the original joint fiber and invalidates P4/P5. |
| Add a port-compatible production extra without full guard | Can violate retained guarantees/authority; §3.7's original-bound counterexample applies. |

These discriminate omissions in a candidate construction. They do not prove
that the entire proposed `α` is minimal for type checking, or refute all
alternative legal abstractions. Proving minimality would require a fixed
independent type-use observation contract and witnesses indistinguishable
after deleting each claimed necessary field.

## 8. Current F5 consumer correspondence and exact gap

At the baseline, `emit_lambda` fixes the own-formal body's local effect to
Bottom/Empty and records no separate body value component. `admit_lambda_fact`
therefore uses the same live parameter ordinal in negative argument and
positive result, with empty argument-effect and the body's positive effect.
This corroborates the value sharing. It does not interpret those effect
children as the complete source invocation derived above.

`ClosedValueScheme` retains an arena-qualified positive predicate, quantifier
count and recursive bound interval. Its views expose polarized Function
children, unions/intersections and Q/R identities. Positive effect views have
only Bottom; negative effect views have only Empty. The shadow
`ClosedSchemeRef` qualifies ordinals by exact owner/scheme and explicitly
does not make them source identities.

`instantiate_and_route_closed_inner` allocates one fresh live value row per
Q ordinal, restores recursive bound endpoints and routes the instantiated
positive predicate at the use. This is a useful **structural** model for
`q -> q`: both occurrences resolve through one substitution entry, with
independent entries at independent uses. It exposes no interface for the
active independent admission, provider wire, original typed receipt/path,
full `K,D` or exhaustive abstractor required by P2/P4/P7. The scalar fallback
`generalize` inspected at line 15674 is not treated as the entire F5
generalization implementation or as successor semantics.

Thus a ClosedScheme printout or correct Q freshening cannot certify this
transformed export. The precise new construction point is a legal inferred
Function descriptor with the Value-entry/result-provider incidence contracts
active at its actual export, and a whole-use transport/query consumer for
that descriptor. Research permission does not authorize implementing it.

## 9. Oracle independence, checks and limits

The observation witness uses charter source decisions and typed-core laws,
not Oracle output or F5 effect interpretation. Current compiler inspection is
an independent structural cross-check for shared binder handling, with no
claim of independent semantic validation: the compiler and skeleton note
share the same inspected generation route. The conditional theorem and any
future checker using P1–P7 would share those premises; agreement would not
prove their raw-source generation, descriptor laws or production adoption.

Method: documentary construction, direct source-law derivation and narrow
read-only integrity checks. No executable search, seeds, sample ranges,
enumeration, mutation runs, tests or builds were performed. Coverage is one
isolated nonrecursive projection Lambda, arbitrary already admitted argument
carriers and finite histories under explicit laws; complete typed source
generation, all independently valid views, general effects/annotations,
captures, recursion, State, foreign meanings and actual Option 2 grammars
remain unverified. CPU/RAM and elapsed totals were not measured; commands
used one lightweight process at a time or bounded read-only command groups,
with no heavyweight process. No Git mutation or delegation occurred.

Checks: baseline `git rev-parse HEAD`; baseline-only `git show`/`git grep`
source reads; SHA-256/current-byte comparison for the twelve direct dependency
files. All twelve matched baseline bytes before publication. A final byte
comparison and lease-path integrity check are recorded in the return packet.
No independently reviewed result or closed DAG gate is claimed.

Recommended next action: independently review the finite wire's P2/P4
descriptor/admission rule as the smallest owning-constructor proposal, and
require an actual-root complete-query law before claiming P6 principality.
This changes method from relation retention to finite interface construction;
another toy model assuming P2/P4 would leave the same premise untouched.

## 10. Commit packet

- Exact leased path: `notes/theory/2026-10-08-projection-lambda-export-construction.md`.
- Baseline SHA: `9ddcc69a30f2be2039ce05c7abe50c9722dc8559`.
- Direct dependency hashes changed: none at the integrity checks; the twelve
  dependencies in §2 are baseline-pinned. Unrelated shared-record changes are
  excluded from premises and from this lease.
- Claim/review: Draft candidate and conditional derivation; independent
  review pending; no full principality, production or implementation result.
- Checks already run: pinned-source inspection and direct-dependency byte /
  SHA-256 integrity; final checks are supplied to the primary. No tests/builds.
- Proposed checkpoint message: `research: derive finite id export interface and exact preservation premises`.
- Shared-record deltas intentionally left for the primary/curator: link this
  constructive lane; record P2/P4 transformed descriptor/admission producer,
  P6 all-view factorization and P7 exhaustive Option 2 as open; change no DAG
  status or production authority on this evidence.

Artifact is frozen on submission. The primary owns review, shared integration
and all Git operations.
