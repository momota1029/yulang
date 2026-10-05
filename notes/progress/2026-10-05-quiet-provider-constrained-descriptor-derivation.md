# Quiet provider: constrained descriptor and guarantee weakening

Date: 2026-10-05
Status: conditional source/reference derivation; production presentation blocked at a named interpretation premise
Branch: `research/simple-sub-intrusion`
Baseline: `a674fcf72f4b10c0d69dc32e75e04e054fc18e53`
Scope: the constant provider `Q = lambda(Value(Unit), result(literal Unit))`; no choice of production context quantification
Implementation authority: none
Review status: reviewed by compiler_referee (semantic scope) and spec_auditor (authority/scope); no blocking, major, or minor findings within their assigned scopes. Production membership and conformance remain uncertified.

## 1. Authority and fixed dependencies

The approved `production-function-denotation/q1`, answer
`production-function-denotation-answer/d1`, selects A: production membership
restricts the original complete typed-observation `Rel_C` fiber by independently
interpreted endpoint, role/entry, path, origin, continuation, scope, authority
and dependency constraints. Admission is separate and comparison-independent.
The approved `production-function-bound-membership/q1`, answer
`production-function-bound-membership-answer/d1`, selects Option 2: complete
production members need not have source-constructor witnesses. Neither answer
defines the missing exhaustive rules or authorizes implementation.

Exact source locators:

- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §2, “Declarative input”; §6, “Source parameter-role generation” and
  “Structural rules”; §8, “Input and finite constraint construction” and
  “Source preservation theorem”; §9, “Entry is part of the interface,”
  “Finite classification, sharing and §8's stronger freeze,” and “One joint
  law for domain-changing comparison.” These are reviewed conditional
  constructions; the document remains Draft.
- [Source-generated theorems](../design/2026-10-04-source-generated-callback-structural-theorems.md)
  §§2.1–2.4 for the source envelope, local relations, selected occurrences,
  bind and complete histories; §3 for independent reference admission.
  Section 8.3 prohibits replacing a principal relation by one witness.
  This is a reviewed conditional package.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2.2 for active constrained-root interpretation and its unproved
  constructor-typing premise; §3.7 for the conditional Option 2 abstraction
  route; §10 for unresolved production interpretation and adoption.
- [Denotation approval](../../questions/2026-10-05-production-function-denotation/approved-answer.md),
  “Exact approved draft content,” decisions 1–5, and “Explicit approval
  provenance”; [membership approval](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md),
  decisions 1–4 and “Explicit approval provenance.”
- [Previous quiet-provider refinement](2026-10-05-production-function-denotation-followup.md#constant-provider-certificate-refinement)
  supplies the already reviewed parametric reference claim. This note exposes
  its retained descriptor and isolates the attempted presentation at `G`.

## 2. The strongest descriptor actually derivable here

Fix the original binder tree and one `xi = (nu,K,D)`. For each supplied finite
client graph in source-generated-theorems §§2.1–2.2, take its independent §3
admission certificate. Call this reference challenge set `D_ref(xi)`.
It includes its typed whole carrier, original profile and result path, ambient
owner/view context, and legal joint response/resumption/future-use history.
All exposed providers and consumers have preallocated source labels;
recursive references are monomorphic. Offered subgraphs are immutable and
exclude mutable cells, opaque imports, implicit adapters and handler-image
nodes. Ambient source-typed contexts remain supplied premises. This is a
conditional reference domain, not a choice of production admission.

The word “strongest” below means the exact generated source/reference
certificate, retaining every supplied constraint. It does not mean a
principal production type or a strongest solution of the unresolved
production membership rules. The latter cannot yet be derived.

For `h in D_ref(xi)`, retain this constrained presentation, written `C_Q` only
as proof bookkeeping:

| Retained field | Descriptor/certificate content |
| --- | --- |
| Introduction and entry | Q's original Pure introduction; `P = Value(Unit)`; one actual receiver and argument receipt before designated one-layer Force. |
| Body/result | `J_body = Comp(empty,Unit)` with the literal and `result` relations; the constant body ignores the rebound Unit. This is the source body/result skeleton. |
| `d-` | The entire received carrier `t` and its designated Force view; its typed result is Unit. No incoming support restriction follows from Pure introduction or the body's empty guarantee. |
| `d+` | The same argument-origin contribution as observed in the complete invocation view, with its distinct original occurrence and signed path. |
| `b+` | The body's/designated consumer's complete-call contribution, at reached post-Force states. For this source suffix there is no request-emitting instruction. |
| Complete image | Actual receipt, Force, typed rebind, constant return, and invocation return delimiter, composed in the original complete `CallView`. |
| Contracts and paths | Original result/response types, profiles, receipts, source labels, continuation suffixes, occurrence maps and event-specific `Flow`/`Observe`/`Path` evidence. |
| Scope and authority | Original binder positions, operation-local witnesses, live owner/slot identities and grants. Q introduces no capture grant and revives no owner. |
| Dependencies | One original `nu,K,D`, with all operand sharing and continuation incidence. Local logical hiding remains at its original scope. |
| Admission | The independently supplied `D_ref`, without a premise that Q satisfies a compared Function interface. |

The source table prints `Fun(Value(Unit), Comp(empty,Unit))` for the
body/result skeleton. It is insufficient to reconstruct the retained
complete-call presentation from that display.

The complete source relation is the following existing constructor image:

```text
receive t at the actual receiver; establish the original receipt;
within the complete invocation view:
    Force_argument(t) >>= lambda(v,C1).
      RebindResultPath(t,v,C1);
      Return(Unit,C1) >>= ReturnFromInvocation
```

Let `F_Q(h,O,w;xi)` denote this generated whole-tuple composition, including
the admission premises and retained metadata above. Its reference observation
bound is `P_ref,Q(h;xi) = { Pi_xi(O) | F_Q(h,O,w;xi) }`, with only genuinely
local witnesses hidden at their original positions. `F_Q` names the existing
generated relation; it is not a new compiler carrier or a definition of
production `DescMem`.

**Derivation.** Literal synthesis produces `Value(Unit)`; normalization is
`result(literal Unit)`, so body synthesis gives `Comp(empty,Unit)`. Value entry
forces the whole argument after receipt and rebinds its result. When Force
returns, the suffix returns Unit in the reached state. When it requests,
the existing bind clause retains the request's original operation instance,
origin, response endpoint and dependencies and appends rebind/body/return to
the same raw continuation. Resumption uses the current resumed configuration;
it does not replay entry or freshen the request witness. Induction over the
independently admitted finite history proves the same clause after repeated
resumptions. A divergent Force contributes its finite prefixes and need not
reach the Unit suffix. Returning Q as latent data executes none of this;
each later admitted invocation uses its retained source descriptor.

Consequently no body-origin request is generated, but Force-origin requests
can contribute at `d+`. The occurrence identities of `d-` and `d+` stay
different although their selected component coordinate is shared. Neither
row equality between their observation positions nor an unconditional union
of outward rows follows. The complete bound is the relational image above,
not `Comp(empty,Unit)` at `J_call`. This remains true when an ambient handler
consumes a request: pre-dispatch observation and authority retain their own
obligations.

## 3. What §8 can weaken

Take a well-formed guarantee support `E` at the same original fiber. Suppose
the compared graph identifies the body guarantee as a genuine support
upper bound, classified `G` only by §8, with `empty` included in `E`. Suppose
all §8 structural and original-certificate premises hold. In particular,
keep `D_ref`, actual entry, all endpoints, source operations, profiles,
receipt identities, complete typed paths, original scopes and `K,D` fixed.
If the body field is also an assumption, routing contract, shared imported
field or dependent invariant in the actual graph, §8 requires equality there;
the `G`-only premise cannot be inferred from its printed row position.

Under those conditions §8 produces a certificate `C_Q^E` with the displayed
body/result skeleton

```text
G = Fun(Value(Unit), Comp(E,Unit)).
```

It retains the full `C_Q` presentation above. The sole relaxed predicate is
the body's genuine support guarantee. `d-`, `d+`, their shared coordinate,
the Force/bind image, continuation suffixes and their constraints are not
erased. The weakening certifies Q's original executions for the same
challenges; it does not make the source body emit arbitrary E requests or
establish production membership for those requests.

In particular, §8 seeds the entire incoming carrier descriptor as an
assumption. Its closure freezes that descriptor even below nested Function
reversals. A shared coordinate occurring at both `d-` and `d+` does not become
freely widenable merely because its second occurrence is positive. The
support weakening cannot add a capture grant, weaken a routing profile,
change response admission or replace the challenge domain.

Thus **a retained constrained certificate can display G conditionally**.
Its complete-call constraints are preserved precisely because G is a display
of the body/result skeleton plus retained evidence. The theorem does not
derive the meaning or membership of a production descriptor printed G.

If a proposed target instead uses `E` as the upper bound of the entire
`J_call`, another premise is necessary: every complete observation of the
admitted Force/bind image must satisfy that bound at the complete-call typed
position. `empty subset E` for `b+` supplies no such premise for `d+`.
§8 could weaken an already certified complete-call guarantee to E if its
full premises and prior inclusion were supplied, but the body skeleton
alone is not that original complete-call certificate. Restricting incoming
carriers to obtain the premise would change the domain and is not licensed
by §8. No generic `[E,d]` row algebra is needed or inferred here.

## 4. Exact first non-derivable production premise

Even grant identical challenge domains for this local attempt. The first
missing production bridge is a comparison-independent formation and
interpretation rule connecting the retained `C_Q^E` to the actual production
descriptor G. In source-contracts §2.2 notation it must supply the concrete
active endpoint/provider clauses of `M_G` and `DescMem_G`, and establish

```text
F_Q(h,O,w;xi)
    implies M_G(h,O,w';xi) and DescMem_G(h,O,w';xi)
```

with the same original coordinates, scopes and retained complete evidence.
The rule must say where G's E constraint is incident, retain `d-`, `d+`,
`b+` distinctly, and preserve the latent descriptor through return and later
invocation. This is the constructor-typing bridge named in §2.2. The source
lambda table supplies only its body/result skeleton; §8 takes an original
complete certificate and does not define `DescMem_G`.

For full production containment, independently permitted non-source members
must also satisfy these exhaustive rules. The implication above covers only
the source base; setting production membership equal to `F_Q` would violate
the permitted scope of Option 2. Section 3.7's paired positive abstraction
offers one conditional route, but its W/Z rules and envelope certificates
are unselected and are not used by this derivation.

This missing interpretation premise is independent of the unresolved choice
between universal and generated production context admission. No claim
about either domain is required to expose it. Production admission and any
actual-to-checked domain inclusion remain separate obligations once that
choice and its rules are settled. No absence of an expressive carrier has
been proved, no source acceptance is inferred, and no new policy is selected.

## 5. Verification, limits and handoff

Verification: source-section comparison and producer reread of the displayed
Return/Request bind derivation, occurrence inventory, §8 freeze conditions,
and approval boundaries. Confirmed branch and exact baseline by read-only
Git queries. No tests, builds, executable searches or measurements ran; zero
measurement processes and samples. Only this leased note was written.

Unverified: independent proof review; concrete production `DescMem`/`M` and
admission rules; current F5 conformance; generalization/use transport of such
rules; arbitrary raw-source, State/import or adapter coverage; principality
and source acceptance. The exact source/reference relation remains within
Theorem C's decorated finite-client and admission-certificate envelope.

Recommended next action: independently check the constrained occurrence
inventory and §8 application, then derive the constructor-typing rule for
G at those retained incidences. The primary owns any integration and updates
to `tasks/current.md`, design/index or theory records; this packet supplies
their proposed delta rather than editing those paths.
