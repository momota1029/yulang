# Native PE constructor renaming at a fixed external fiber

Date: 2026-10-09
Baseline: `c27870a13d2ff9205c94e973224ab1a1b4df9360`
Branch: `research/simple-sub-intrusion`
Status: frozen, unreviewed, non-authoritative research derivation
Gate: bounded evidence toward IFACE_EQUIV / CI_USE; neither gate discharged
Exclusive write lease: this file only
Production implementation / semantic selection / cutover: none

## 1. Objective, authority and claim class

Derive the renaming law actually available for the selected native PE-ID and
finite-public-import PE-PICK constructors, without assuming nominal laws for
their opaque dependencies. The method is structural induction on the selected
dependent records, finite proof syntax and forced-alias graph. There is no
checker, model search or source-semantics oracle.

Governing inputs at the pinned baseline:

- `notes/design/2026-10-08-native-projection-public-export-definition.md`
  §§2–4: authentic owning constructors, actual final root, finite public object,
  whole-frame decode, ordinary checking and bounded native closure.
- `notes/theory/2026-10-08-projection-public-export-construction.md`
  §§3,3.1,4.1–4.3,6–8: retained fields, extraction, decode equations, exact alias
  maps, Direct cases and fixed finite public capture.
- `notes/theory/2026-10-08-native-projection-certificate-constructors.md`
  §§3–4: typed local registry and actual native certificate records.
- `notes/progress/2026-10-07-successor-recursive-synthesis.md` §5.1:
  original identities rigid; actual operation covariance requires independent
  laws and a complete identity-observer inventory. Its §5.2 identifies the
  conditional joint-use consequence; it is not an additional premise here.
- `notes/theory/successor-proof-obligations.md`, IFACE-EQUIV and CI-USE rows:
  actual operation laws remain open; the supplied-law CI-use theorem is
  conditional.

Accepted meanings are retained: one original `a` and telescope, the fixed
generic raw inlet, complete VP production with Echo or Fixed(J), all original
proof-choice fibers, Option 2 alternatives, original current-event ownership,
and the full fixed public capture closure. This note selects no new meaning.

**Established input:** the selected PE construction and its exact F/G raw
alias expansion. **Research result:** the fixed-external-fiber structural lemma
below, derived from that construction but not independently reviewed.
**Conditional extension:** transporting changed opaque operands would require
additional laws explicitly listed in §5. **Bounded characterization:** which
selected constructor checks reduce to fixed calls versus those laws. No
universal semantic-equivariance theorem or actual-compiler claim is made.

## 2. One action and its exact hypotheses

Fix one finite authentic PE-ID or included PE-PICK source/public record family,
one original finite client use tree, and one sort-preserving bijection `h` of
its represented alpha-local coordinate names. Its inverse is `h^-1`. This
renames coordinate labels and their references; it does not replace a runtime
provider, source binder, event, actual root handle or semantic evidence object
by a different object merely because the labels have corresponding shapes.

Hypotheses for the lemma:

1. `h` preserves the complete original binder tree, predecessor order, sort,
   ownership, scope, slot classifications, ordered field positions, chosen
   proof constructors and references. It fixes source/binder/provenance
   identities, original sigma/nu/K/D operands, provider/capture anchors,
   intrinsic permissions and all rigid inputs. A renamed coordinate denoting
   an actual identity is distinguished from that unchanged identity value.
2. Native records have the selected full operand inventory. Shared fields,
   actual-event fields and frame-owned ViewLogic/EventProof fields retain
   their original incidence. The selected final source root is retained;
   a conversion or annotation is not replaced by an interior projection root.
3. At an external operation occurrence, corresponding assignments supply
   **literally the same complete actual operand tuple**, including any actual
   root/slot/event/authority/evidence identities it reads. The operation and
   external registry version are the same. Its output or relational witness
   is carried unchanged as an opaque operand. Calls not meeting this condition
   are excluded, rather than assumed covariant. Opaque witness internals are
   not recursively renamed without an independently exposed constructor.
4. The actual source/public root records and any allocation outputs used below
   have already been supplied. Their semantic handles stay fixed. The lemma
   does not prove equivariance of running an allocator twice, freshness supply,
   Generalize's opaque guards, source legality, proof search or foreign
   certificate formation.

Hypothesis 3 is a restrictive comparison criterion, not a selected semantic
law: it says exactly which comparisons this lemma covers. It can force `h`
to fix additional coordinates, possibly leaving only the identity action at
an identity-sensitive boundary. A nontrivial action still exists on private
alias names, proof-variable labels and internal references when they are not
passed as changed actual identities. No claim that such freedom exists for
every actual interface is needed.

Define the action on native syntax recursively: keep tags and rigid atoms;
rename alpha-local labels and bound references by h; act on each ordered
record field, telescope, finite proof subtree and declared equation-reference
argument. On assignments, move the value at coordinate x to h(x), keeping
opaque semantic values fixed; act recursively only on explicitly represented
native records. This is transport of a presentation at one external fiber.
For an operation reading a coordinate name as an identity operand, hypothesis
3 must be checked separately; assignment pullback alone does not justify it.

## 3. Constructor-specific derivation

### 3.1 Forced aliases and certificate choice slots

Let s be the extraction substitution of §4.1, acting simultaneously on every
incident predicate and W occurrence. Its id graph assigns the formal/read/
body/outward raw value/provider aliases to the retained entry value/provider.
Its pick graph assigns read/body/outward aliases to the fixed J_z value/
provider; the argument remains distinct. Worlds, descriptor roots, ports and
proof witnesses are not aliases in s.

Define `s_h(h(x)) = h(s(x))` on the corresponding alias graph. Induction on
terms, with binder references transported at their original scopes, gives

```text
h(s(t)) = s_h(h(t)).
```

The alias graph is total and defining: `z=t` forces the raw value at z. Its
reconstruction G therefore obeys the same equation; extraction F obeys it
because F is this substitution plus removal of the alias fields. Thus

```text
F_h(h(X)) = h(F(X))
G_h(h(Y)) = h(G(Y))
```

on the selected full native tuples. The h subscripts denote the same displayed
constructor at renamed coordinate labels, not a new semantic operation.
Any incident opaque predicate meets hypothesis 3 or remains uncovered. This
retains, rather than derives anew, the selected F/G equality of source/public
fibers. In particular Identity and Compose keep their distinct tags, all
intermediate evidence and W fields; no proof normalization is used.

### 3.2 The four actual native families

For each row, the outer operation calls and their guards are fixed calls under
hypothesis 3. Their equality is reflexivity on the same actual operands; no
general covariance law for the named operation follows.

| Selected constructor | Exact defining fields and structural transport |
| --- | --- |
| BindIntro / BindCert | `C1=Install(C0,b,(v,p))`; beta1 keeps that same value/provider and the supplied hereditary restriction. Transport the ordered C0/C1/world/binding fields and original receipt/rebind guards. Install and the compatible action are fixed external calls. |
| ProjectIntro / ProjectCert | `beta=omega.environment[b]`, `Lookup(C,b)=(v,p)`. A consistent renaming of represented record labels/references preserves field projection. Actual registered b and lookup incidence stay fixed; changing the authentic registry key is outside. |
| RestrictIntro / ReadCert | Retain the actual binding/root/provider, supplied compatible action chi, input/output theta, original read event and full project-then-restrict proof. Hereditary restriction itself is an unchanged external call. |
| ReturnIntro / PureReturnCert | Outcome `Return(v,p,C)` has the same raw fields, original result port, theta/omega and incidence guards. The native tuple constructor commutes with h. Prefix transport preserves only present fields, including the zero-step case; it introduces no completion certificate. |
| InvocationReturnIntro / InvocationReturnCert | `C_out=ExitOwn_IF(C,r,e)` with the original current own occurrence. Same completed PureReturn and same outward raw value/provider are retained. Exit and hereditary/world restriction are fixed external calls; a saved activation cannot replace r. |

For the complete families, the selected grammar is

```text
Cert_f ::= Elementary_f(record)
         | Check_f(Cert_f,d_L,all intermediate/output fields)
         | Local_f(registry entry,full telescope,independent witness)
         | Ref_f(registered equation,original scoped arguments).
```

Elementary follows by the row's field/equality argument. Check follows by
induction on its nested family and finite L term, retaining every premise and
intermediate. Local remains the identical authentic external-law application
when hypothesis 3 holds; a bare name is not a supplied law. Ref transports the
finite reference graph and its original scoped arguments without unfolding
or manufacturing a recursive proof. Any semantic equation-rule application
is also an external call subject to hypothesis 3. Inverses give reflection
of the same constructor checks, not existence of missing certificates.

### 3.3 Extraction, decoder equations and Direct wrappers

Extraction's retained inventory—display template, Omega, whole inlet/IF/Delta,
result dependency and typed slot/telescope schema—is transported field by
field. Forced-alias substitution commutes by §3.1. Removing the four private
source positions and installing the ordinary family references commute as
finite record transformations. This statement starts after authentic rule
inversion and the original eligibility/fix classification are supplied;
it proves neither operation's full source semantics.

For supplied ordinary root u_i, the actual id equations are

```text
head(u_i)       = Function(Pure,Value,ValueResult/InvocationReturn)
inlet(u_i)      = I_q[A_i;Delta_i]
result(u_i)     = A_i
dependency(u_i) = EntryValue
admission(u_i)  = the four independent VP challenge/history constructors
production(u_i)= exhaustive VP phase/development grammar + Echo
proofs(u_i)    = ordinary CE schema at the original slots.
```

The finite equation presentation commutes with h at fixed interpreted operands.
Pick substitutes the actual fixed `J_z.value_type` and `PublicValue(J_z)`,
with VP+Fixed(J_z), and its entire free capture closure stays fixed. This
retains pending/divergent Force and non-source production alternatives as
selected. It neither equates production to execution nor independently proves
the external VP/carrier/history/future relations covariant.

Direct's three selected wrappers are

```text
Direct(u,V;Value(d_V))
Direct(u,V;Computation(d_T))
Direct(u,V;Function(d_D,d_P)).
```

The actual u and V are retained separately from the source r. At fixed
readouts and fixed external local-law calls, bottom-up constructor recognition,
typed-reference matching and whole ordered premise checks have the same result
under h. Function retains both complete domain and observation trees; Value
Top/union does not gain a Function domain. Finite L proof tags, operands and
equation references are preserved. This proves structural certificate
recognition at supplied records, including failure from a mismatched rigid
root. It does not prove query resolution/search equivariant or manufacture a
proof for a target from its printed type. Executed conversion is a fixed
external constructor/handle, not an additional Direct case.

### 3.4 Exact result and finite joint extension

**Fixed-fiber native structural lemma.** Under hypotheses 1–4, h and h^-1
give mutually inverse transports of the represented native constructor
records and their structural checks, forced-alias maps, extracted public
schemas, supplied decoded-root equations and supplied finite Direct proofs.
Every fixed external relation application has identical truth on both sides
because its complete operand tuple is identical. Consequently, preservation
and reflection cover the finite conjunction/alternative of those native
checks at this fiber, including all retained evidence choices. They cover no
external occurrence with changed actual operands.

For a supplied finite joint new/alias tree, extend the same action coherently
by `(i,x) -> (i,h(x))` on frame-owned alpha names, retaining original Shared
and actual-event ownership and client/public coordinate values. Aliases use
the same frame; distinct real-new events remain distinct. This preserves the
joint schema, correlations and original quantifier order under the same
fixed-call restriction. It supplies no fresh-allocation law and no transport
for a client W that observes changed internal identities as data. Such W is
uncovered unless its full call tuple is fixed or its independent law supplied.
This restricted corollary is not the arbitrary finite joint-use CI_USE gate.

## 4. Identity observers and rigid coverage

The following inventory is drawn from the selected records and CI §5.1; it is
not a claim that every compiler/foreign operation has been inventoried.

| Observer in this bounded family | Required treatment |
| --- | --- |
| Raw equality, Echo and Fixed(J), alias/sharing tests | Keep actual value/provider fixed; consistently rename represented references. Pick's J cannot be replaced by a same-typed J_other. |
| Source introduction, final-root selection, provenance and original binder levels/order | Actual identities and source choices rigid; no shape reconstruction. |
| Slot/binding registration, Lookup/Install keys and field incidence | Authentic registry identity fixed. Coordinate labels may rename only without changing the actual registry call. |
| World/path/ownership, receipt/receiver/continuation and current invocation occurrence | Original actual event, scope/order/authority dependencies rigid; Strict/Exit operations are fixed calls. |
| Permissions, grants, lifetime/compatibility and hereditary restrictions | Full authentic operands fixed; historical identity supplies no compatibility law. |
| Complete input image, carrier/Force/admission, IF and Delta guards | Whole proof/contract tuples retained; changed operands need independent laws. |
| Proof tags, intermediate evidence and typed equation references | Native tags/references transported structurally. Identity and Compose distinct. Opaque witnesses and registry meanings fixed. |
| Actual ordinary root readout and query certificate identity | Keep u,V and their authentic interpreted handles fixed; no certificate for r in place of u. |
| Client W, adapters, conversions and additional authentic local primitive | Fixed complete calls or uncovered. An unenumerated identity observer invalidates any broader claim. |
| New/alias allocation, eligible/fixed classification and import capture | Supplied ownership classification/output fixed; operational allocation transport unproved. |

## 5. Precise obstruction to a broader claim

The selected local registry says each primitive has a genuine typed semantic
law. Soundness of a law is not a nominal preservation/reflection law when its
operand identities change. Similarly the selected proof registry permits
additional authentic primitives, independent V/W/T/Car evidence and imported
opaque certificates. Their full internal identity observations are not defined
by the four native record constructors.

For example, deriving

```text
Apply_L(d;X;Y,Z) iff Apply_L(h(d);h(X);h(Y),h(Z))
```

for an authentic primitive with changed operands requires its own transport
law. Syntax induction reaches that leaf and stops. Rewriting its signature,
or checking a model that defines the leaf to satisfy this equation, would
assume precisely the missing premise.

Unprovided laws include changed-operand registry/authority/port predicates;
semantic V/W/T/Car and whole Delta observation-image evidence; independent
admission and VP history/development/future operations; compatible hereditary
actions; Strict Install/ExitOwn_IF beyond identical calls; authentic local
primitives/equation rules/converted handles; actual fresh ordinary-root
allocation/readout; and client/query operations reading changed identities.
These are obligations, not counterclaims that the operations fail to be
equivariant. The actual-compiler producer/consumer correspondence is also
absent from this research proof.

Failure conditions for the proved scope are concrete: an omitted external
operand, changed authentic key/root/provider/event/registry version, renamed
opaque witness internals, altered binder predecessor order or classification,
independent per-port/frame substitutions, dropped production alternative,
proof-tag normalization, or source-root substitution for the actual final or
public root. Any such change exits the lemma's hypotheses. No counterexample
to the selected PE-ID/PE-PICK theorem is alleged.

## 6. Checks, independence, resources and next action

Checks: read the exact governing sections and policies; inspect pinned HEAD,
branch and lease path; compute dependency SHA-256; inspect this artifact's
complete scope and whitespace with narrow deterministic file checks. No
compiler edit, cfg(test), test/build/benchmark or executable probe occurred.

Oracle independence: no executable oracle was used. The derivation shares the
selected native transition/record meanings with PE; it proves an algebraic
consequence of them and does not prove those source meanings independently.
Identical external calls provide reflexivity, not hidden covariance evidence.
No independent review of this authored derivation has occurred.

Coverage: one finite included PE presentation/use family at the same rigid
external fiber and one arbitrary permitted h satisfying the fixed-call
criterion. No seeds, numeric ranges, search shards, mutation runs or sample
counts apply. Named invalid transformations in §5 are proof failure conditions,
not executed mutation results. There was one derivation attempt, not repeated
toy models of the same missing law.

Resources: read-only shell inspection and one note write; zero heavyweight
processes, builds, tests or benchmarks. CPU/RAM and end-to-end wall-time were
not instrumented; no performance claim is made. No scratch outputs or other
leased paths were written. Shared status/authority files remain primary-owned.

Recommended next action: independently review this bounded derivation, then
lease one actual nominal-law supplier for the earliest changed operand in a
concrete PE new/decode use (including its root allocator and complete identity
observer list). Do not replace that missing law with another abstract model
that stipulates it. IFACE_EQUIV stays OPEN-PROOF and CI_USE retains its premises.

## 7. Frozen dependency snapshot and commit packet

Direct file SHA-256 at baseline and freeze:

| Dependency | SHA-256 |
| --- | --- |
| native projection selected definition | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| projection public export construction | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| native projection certificate constructors | `04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8` |
| successor recursive synthesis | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| successor proof obligations | `41e25bc633f69df302361f41c60c0c324e9713a7194373f23f9f7a182724e4a1` |

Commit packet:

- Exact leased path: `notes/progress/2026-10-09-native-projection-interface-equivariance.md`.
- Baseline SHA: `c27870a13d2ff9205c94e973224ab1a1b4df9360`.
- Changed dependency hashes: none at freeze; direct inputs rechecked against
  the pinned revision. Unrelated later branch movement requires no new claim.
- Claim/review status: frozen, unreviewed structural fixed-fiber derivation;
  non-authoritative research checkpoint; no IFACE_EQUIV/CI_USE gate closure.
- Checks already run: selected section/policy reads, branch/HEAD/lease scope,
  dependency SHA-256 and narrow final artifact whitespace/scope inspection.
  No semantic executable verification or independent review.
- Proposed commit message: `research: derive native PE renaming at a fixed external fiber`.
- Shared-record deltas left for primary/curator: optionally link this bounded
  evidence from `tasks/current.md` and the IFACE-EQUIV/CI-USE rows in
  `notes/theory/successor-proof-obligations.md`; retain existing gate statuses
  and flag changed-operand/root-allocation laws as unsupplied. No design/index
  selection, production authority or question-board delta is proposed.
