# Research definition: caller-side module initialization

Status: Draft, R28 candidate; not adopted and not production-authoritative.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
OPEN/closure0 with its original domain and quantifiers. This candidate develops
the caller-side initializer route selected by the user for one reversible
research attempt. Its adoption alone discharges zero parent conditions.

## Why this route, and what the prior rules actually give

R27's reviewed bootstrap derives the actual source registration:
`Sigma0`, `theta0`, `Op0`, the complete `PortProv` catalogue, root `r0`, clause
`q0`, and `j_decl(h)=ins_(r0,q0) o rho_h`. At the original
`(C0,w0,e0;xi)`, `PhiW` still consumes the independent `j0` and `a0`. The
selected rules neither construct those judgments nor inhabit the required
`DeclContribution` fibers.

R27's fresh review was CLEAN only for that bounded result and the conditional
`L-DeclaredPort` consequence. Its reviewer confirmed this candidate must
specify a real authority/activity policy and an old-dependent extension before
adoption. Separately frozen Operation constructor audits locate no authentic
original `DeclContribution`/`PrimLicenseContribution` for the fixed `c`; this
document does not solve or weaken that distinct gap.

## Proposed research rule and independent inputs

At one unchanged `xi=(nu,K,D)` and one original module-init event `e0`, use:

```text
M      actual fully resolved and typed module/declaration graph, including
       source occurrence keys, binder tree, visibility, and complete signatures
P      caller-owned predecessor context with its complete old roots,
       interpretation, dependencies, witnesses, and old-root evidence
theta0 the original joint declaration substitution; no per-alias substitution
Init0  an actual source/host module-initialization transition at e0, with its
       resulting configuration C0 and independently observed active module
xi     the original full dependent index (nu,K,D), unchanged
```

`Init0` is a required source/native input, not a constructor invented by this
document. It must denote an actual event at which the module and its registered
declarations are active. A compile-only parse, an allocated ID, a Rust object,
or a future runtime receipt is not `Init0`. If the accepted source/runtime
semantics has no such event or the actual runner cannot realize it, the
candidate stops before `j0` and remains unadopted.

The candidate extension is:

```text
Registry0 = Registry(P) extended by the exact resolved declaration/member IDs
Scope0    = Scope(P) extended by the source binder tree's resolved lexical edges
theta0    = one joint assignment for every new binder/shared source position
Auth0     = Auth(P) plus the directly resolved declaration's complete port
            interface, only where visible from M at Init0
Inc0      = Inc(P) plus each actual source occurrence -> declaration/port path
            whose referenced declaration and receiver are active at Init0
W0        = the dependent record extension carrying the above, retaining all
            old/private/shared fields and the original index xi
```

This is a *candidate semantic action*, not an inference from names. Its
authority policy grants no unreferenced declaration, same-name foreign member,
hidden declaration or future activity. Static visibility and the actual
`Init0` activity witness are separate premises. Every old coordinate is
preserved by an explicit dependent embedding; every new cross-root dependency
must come from the resolved module graph and receives one exact witness.
Failure to prove that the extension preserves an old field at the same `e0`
rejects the candidate rather than dropping that field.

The proposed conclusion is deliberately written without the target judgments
as premises:

```text
resolved source M; authentic predecessor P; theta0; actual Init0; exact xi
resolved visibility and dependency derivations; old-field extension proof
--------------------------------------------------------------------------
CallerModuleInit(M,P,theta0,Init0,xi) yields W0 and a candidate j0 derivation
```

The last line is not yet a valid rule. It is accepted only if the following
field-by-field derivation produces the *existing* judgments at their original
indices. It may not define `j0` as the structural bullet list above or assume
`j0`, `JointWF(W0)`, `OriginalInitial`, a valid-world marker, or the resulting
license as an input.

## Exact original-field obligations

| Existing judgment component | Required constructor evidence at the original tuple | Candidate rule source and failure condition |
| --- | --- | --- |
| Registry | Exact `(module,declaration,member)` registrations plus resolved cross-root edges | `M` and `P`; fails if any old registration or dependency witness is erased, renamed or reconstructed from equal names. |
| Scope | Original binder tree and resolved lexical/import visibility, with every witness at its original scope | `M`, `theta0`, and `P`; fails if family/key equality replaces a source edge or any private/shared scope is hoisted. |
| Current authority | Original current-authority predicate for every required root/port at `e0` | Direct declaration reference, exact visibility, and actual `Init0` activity; static `PortProv` alone is insufficient. If the original predicate has additional independent authority conditions, they remain required and the derivation stops. |
| Incidence | Original `Path` plus event-current activity for the referenced member, owner and receiver | Actual occurrence/declaration/port paths from `M`, and the same `C0,e0` activity evidence. No inactive declaration can be made live by registration. |
| Old-field preservation | Original dependent registry/scope/authority/incidence facts for all predecessor roots after extension | Explicit old embedding and proof that each original predicate is preserved under the new root. Copying bytes is not enough when a predicate depends on the extended registry. |
| `a0` alias/capture/shared-witness agreement | Original semantic equality and scope agreement for all jointly shared and captured positions | One `theta0`/one source witness per actual resolved sharing class, plus preserved old witnesses. Projection equality alone does not establish agreement with independent old certificates. |
| Static license and licensed incidence | Actual `DeclContribution(q0,h,c;Omega,rho;d)` and exact `j_decl`, then the selected `L-DeclaredPort` rule | **Not supplied here.** The fixed Operation input audits find no original d/license projection. Module-init authority cannot generate one; this remains an independent source-owner input. |

The proposed source rule may therefore derive `j0` and `a0` while license
remains open, but only if every existing component of those judgments is
actually constructed. A formal `j0/a0` result that omits a dependent field or
changes the original predicate is a failed attempt. The fixed original
bootstrap is not fully applicable until its independent license premise is
also present.

## Shared witnesses, provenance, and old dependencies

For new source binders, construct one dependent witness for each actual
resolved binder identity and share it across all aliases that point to that
identity. For an overlap with a predecessor field, reuse the predecessor's
original witness only when the source dependency map identifies that field;
otherwise the overlap premise is missing. Do not choose independent witnesses
for ports and later equate them by key.

`PortProv`, field injections and `j_decl` stay exactly those of the adopted
native signature construction. The module-init action changes the caller's
context, not the source-port origin partition. `DeclContribution` still
requires the original primitive/operator leaf and full field correspondence.
No receiver is substituted for an original owner, and no runtime action is
derived from a static license.

Later compatible histories need separate event rules. `j0` at `e0` cannot
stand for entry, Request, response, Resume, FutureUse, or any other later
configuration. This candidate proves no phase action, hereditary closure,
`OriginalInitial`, full Call, F1/FK1, soundness, principality or universal
parent result.

## Source/native boundary and research implementation seam

The existing HIR path retains resolved `SourceOperationDeclaration` IDs,
visibility and signature occurrences, and R25 can retain opaque payloads bound
to one admitted source declaration. Neither the selected `prepare` caller nor
HIR currently supplies `P`, `Init0`, `theta0`, `j0`, `a0`, or original license
evidence. Existing candidate inference retains HIR but has no semantic consumer
for this payload.

A provisional playground adapter is safe only as a source-correspondence
collector: it may bind actual parsed declaration/occurrence IDs and retain
caller-provided predecessor and event records through the existing HIR and
candidate path. It must expose these as **unvalidated/provisional** and must
not report a derived guard, successful acceptance, or theorem evidence. It is
not a `CallerModuleInit` implementation unless the reviewed source definition
and proof supply the exact semantics above. If the owner-path audit finds no
actual input supplier or consumer, record `NO_SAFE_CODE_SLICE` instead of
repeating payload transport.

Source/native falsifiers include a fresh same-text parse, foreign declaration,
same-name member, mismatched `xi/e0`, expired authority, inactive endpoint,
lost predecessor/private/shared dependency, independently split aliases,
fabricated `DeclContribution`, or a consumer treating payload presence as
truth. These reject the candidate.

## Selection and review boundary

The user selected the recommended route for one attempt. This is authorization
to develop and review the caller-side initializer candidate; it does not make
the candidate `Authoritative` or alter production behavior. The exact policy
above must pass a fresh independent semantic/compiler review before any code
lease starts. If review finds a new externally observable choice outside this
selected route, keep the prototype blocked and present only that narrow choice.

Required reviewers: a fresh compiler referee attacks same-tuple field
construction, event/current authority, dependencies and source/native
correspondence; an independent specification review checks that no source
domain or original guard was narrowed. Review cannot certify the proof
producer or close the parent.
