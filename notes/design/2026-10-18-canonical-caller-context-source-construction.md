# Canonical caller context for the choose source package

Status: R27 source-construction candidate; **not adopted**. No compiler API or
semantics changed. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`
remains OPEN/closure0 with all original quantifiers.

## Existing rule result

The reviewed bootstrap/profile construction does more than a syntax sketch: it
constructs the actual source-owned `Sigma0` telescope, `theta0`, `Op0`, full
`PortProv` catalogue, source root `r0`, clause `q0`, and
`j_decl(h)=ins_(r0,q0) o rho_h`. It preserves the original binder/scopes,
private/shared positions and every declared port. Its Pi0/Op0 derivation is
source-native and applies actual entry, return, request and response rules.

That constructor is still structural/local. The selected `PhiW` clause requires
the full immediate `j0` registry/scope/current-authority/incidence judgment and
`a0` alias/capture/shared-witness agreement at the same `(C0,w0,e0;xi)`. The
bootstrap rule does not introduce these. `L-DeclaredPort` consumes an actual
`DeclContribution`; native signature formation constructs the support and
license schemas, but schema formation does not inhabit the local typing,
primitive-license or inherited `original_license_fields`. Structural alias
projection equality proves only that the same registered field is projected;
it does not establish semantic agreement of arbitrary private/shared witnesses.

R26 independently confirmed the selected public caller has no authentic
context to transport. Therefore the adopted rules inspected here do not yield
a non-circular derivation of all `j0/a0/license` fields for the original choose
registration. This is a source-rule boundary, not a refutation or a claim that
no external caller could supply the context.

## Candidate caller-side source initialization rule

One possible completion is to let the **compilation caller** construct the
initial context from the resolved module before evaluating `f0`, preserving
L4's owner. The candidate rule is named `CallerModuleInit`; it is a proposal
for a new source-semantic introduction, not an existing theorem:

```text
resolved module derivation M, including its complete declaration/signature
  graph, theta0 and original scope/dependency/shared-position maps
caller-supplied predecessor context P at xi, with its complete old roots,
  imported dependencies, histories and opaque original contracts
module-init event e0 with an explicit visibility/authority policy
actual local typing/primitive licenses for each emitted DeclContribution
one joint dependent construction that preserves every old coordinate
--------------------------------------------------------------------------
CallerModuleInit(M,P,xi,e0) yields W0,Gamma0, j0, a0,
  DeclContribution/L-DeclaredPort licenses for its actual registrations
```

The rule may not take `j0`, `a0`, `JointWF(W0)`, `OriginalInitial`, a valid-world
flag, or a license conclusion as a premise. Its candidate field construction
must be explicit:

- `Registry0` is the predecessor registry extended by the exact resolved
  `(module, declaration, member)` identities of this module. It does not erase
  or rename any old root.
- `Scope0` is the predecessor scope plus the source binder tree's actual
  lexical visibility relation. It cannot use equal names or family IDs as
  source identity.
- `Authority0` preserves every old authority field and adds authority only
  for a direct source occurrence whose resolved reference targets this exact
  declaration and is visible from the active module scope at `e0`. The
  proposal is silent on external visibility until an explicit policy is
  adopted; it grants no authority to an unreferenced port.
- `Incidence0` preserves old incidence and adds only the actual source
  occurrence-to-declaration/port path in the resolved source graph. It does
  not infer a runtime receipt or future activity from a declaration alone.
- Shared positions are constructed once under the original `theta0` and
  binder map; all aliases project from that one retained witness. The
  derivation must still show the original semantic overlap/equality at the
  joint scopes, not just equal Rust keys.
- Each `L-DeclaredPort` result must be derived from an actual
  `DeclContribution(q0,h,c;Omega,rho_h)` inhabitant and exact
  `j_decl(h)=ins_(r0,q0) o rho_h`. The declaration/signature schema alone does
  not supply that inhabitant. An empty applicability fiber stays empty; no
  support entry is silently granted a license.

The constructor must state its non-target inputs: a predecessor context with
its own old-root interpretation/dependencies, a resolved whole module and
scope map, the actual module-init/use event, and independent local typing and
license evidence for each new `DeclContribution`. It must specify whether and
how this transition preserves every old dependent registry/authority predicate
at the same `xi` and event. If these inputs cannot be independently produced
from existing rules, the conclusion remains conditional and the exact first
missing field is reported. Static license does not create event-current
authority. The module-init event and all later compatible-history actions need
distinct rules.

This candidate changes caller-side source semantics: a resolved declaration
would participate in a canonical initialized registry under an explicit
visibility/current-authority policy. It might also require a rule for how
module initialization extends `P` without invalidating old registry or
dependency guards. Those consequences need exact same-index admission tests
against the original `PhiW`, `PhiT` and license interpretations. If the
existing guards cannot be satisfied under any faithful construction, changing
their meaning is a separate and larger choice; it is not included here.

## Choice boundary

- **Keep L4 external construction:** caller supplies an independently
  introduced, complete context. The repository has no such selected host input;
  this route waits for one and yields no code slice.
- **Adopt a caller-side canonical initializer:** define and review
  `CallerModuleInit` with its exact visibility, authority, dependency, license
  and history rules. The compiler still only receives authentic evidence.
  This is a language-semantic choice, not a Rust-API choice.
- **Keep the example-specific constructor structural:** do not infer guards;
  the original parent remains open at the same first application.

The second option is a candidate, not a recommendation disguised as a proof.
R27's conditional prover may check whether its stated premises actually imply
the original guards and where the remaining premise lives. A rule proposal,
conditional derivation, or review cannot count as a parent condition discharged
until the rule is adopted and its actual source premises are established.

## Falsifiers and review seam

Reject the candidate if it derives current authority from static `PortProv`,
accepts same-name or foreign operation members, mixes per-field witnesses
across fibers, drops old/private/shared dependencies, assumes any target guard
or valid world, or treats `OriginalInitial` as available before its owner rule.
Test admissions at the same original `(C0,w0,e0;xi)`; do not narrow providers,
carriers, requests, divergence, responses, future events, F1/FK1 or any original
parent quantifier. Independent review must judge the rule's semantics and the
conditional application separately.

## Frozen basis

- Adopted bootstrap profile: `d3ffc07772883737d76d80ef43a834f145c4c42dab71a99074642f0a258c38e4`
- Structural caller registration: `3a7cb66fd67faf01944d043277a83b1118aa25c50ed16d468f88098db3d6ea07`
- Prior joint-guard candidate/stop: `6d6c14bd26ad4e026b3f88799226c467aa74099a90a458392418d92fbc8e1fe5`
- R26 authentic caller obstruction: `bedf403a40b78264fd81ea147b49f84145311b5da70272211578e7718ee5fe58`
- R26 independent caller audit: `5a0e7fde1aa57477b2267eb2dabc30e376f84552bbd5616eed3e4933c6cab2f4`
