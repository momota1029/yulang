# Adoption: module Name and IF consumers in `Sigma_MI`

Date: 2026-10-17  
Authority: user authorization for proof-oriented semantic interpretations; Luna adjudication after independent review.  
Sprint: `module-registration-call-consumer-20261017`, revision 1.

## Adopted scope

I adopt the reviewed relative extension `Sigma_MI` from
[`2026-10-17-module-registration-call-consumer.md`](../theory/2026-10-17-module-registration-call-consumer.md), revision 1,
SHA-256 `010f819ddcab4348b8f658bf381d69d830ce9035db7bb104f1c2f510d5100a13`,
with handoff SHA-256
`66f7e06efba4c73e2b7db0535052ffc0984377c9ea98c8476a3e3c4a585386bf`.
Compiler/source, specification and architecture reviews were CLEAN within
stated bounds.

The extension adds these explicit cases at the actual `u_id` source occurrence
for the fixed reviewed source `my id x=x; my answer=id 0`:

- `MRef-Name*` introduces a module-root reference from the adopted `reg_M`,
  actual `b_use`/`Resolve(u_id,d_id)`, and dependency-preserving scope inclusion.
  It uses identity on already allocated `C_use`; it does not apply `mu_id` a
  second time or equate `R_M` with the source leg `mu_id(r_id)`.
- `IF-Insert-M*` and `IF-Use-M*` form contextual slots from the actual stored
  equation body and that reference. They preserve all original fields, origins,
  guards, arms, providers and dependencies and establish incidence only; they
  introduce no membership witness or license.
- `Name-Module-M*` adds the actual published module-instance certificate, and
  `Data-Name` forms `Data_MI(...,Value(A_id_use))` in the extended grammar.
  These are `Sigma_MI` judgments, not old `Data_orig`/`Reg_orig` derivations.

This adopts a local reference/IF/Name derivation at the same original source
indices. One local consumer subcondition, `MODULE-DATA-NAME-u_id@Sigma_MI`,
is closed. It is not a fixed-family condition or an original global theorem
gate.

## Explicitly conditional and still open

`MResult-Register*` and `Code-Result` are adopted only as conditional schemas
whose domain includes the actual complete original `Fam_Return` application,
source normalization and registered Result port. This sprint does not construct
that application for an independently fixed opaque registry. Thus it produces
no unconditional `q_f_M` and closes no Result, complete Call, fixed-`Reg_orig`,
source/native, admission-equivalence or global theorem condition.

The first missing original Application producer remains the module/literal
scoped demand introduction `rho_c/F_c`; Call-owned argument Reify registration,
all checking clauses/origins, guards/alternatives, Function elimination and
authentic `e_c` remain open. No `Sigma_M` or `Sigma_MI` object is passed to an
old consumer without an explicit compatibility derivation. Old constructor
domains and meanings, opaque predicates, quantifiers, source domain and all
original Call operands remain unchanged.

## Review scope and limits

- Compiler/source review: CLEAN; exact artifact/contract/handoff hashes and
  pinned dependencies matched. No source producer or safe code slice found.
- Specification review: CLEAN; original indices, quantifiers, source domain,
  guards, alternatives, strategies and futures preserved; no `Reg_orig` cast.
- Architecture review: CLEAN as an unadopted relative extension; verified the
  conditional Return-port boundary and identified the precise compatibility
  falsifier: an old consumer requires `Reg_orig`, `Data_orig` or an old port,
  while an application supplies only the new judgment.

Reviews were bounded and read-only. They do not establish whole-kernel
compatibility, a complete Return application, source/native correspondence,
soundness or production behavior. Astra was not used.
