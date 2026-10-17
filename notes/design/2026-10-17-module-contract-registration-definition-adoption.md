# Adopted module contract registration extension

Status: **Authoritative, scoped semantic extension**  
Adopted by: Luna under the user's explicit authorization for proof-oriented semantic interpretations  
Date: 2026-10-17  
Reviewed candidate: [module contract registration proposal](../theory/2026-10-17-module-contract-registration-definition-proposal.md), SHA-256 `074455cef680c22a4d0eb471406c7aa6945d7d85543769c1b57fdb5de0d73353`  
Review: fresh compiler/source, spec and architecture reviews CLEAN within their stated scopes

## Decision

Adopt the proposal's `MReg-Intro*`, elimination, and `Expand_M` / `Meaning_M`
clauses as a **new module registration case** in the scoped extended
interpretation `Sigma_M`. This selects a semantic extension; it does not assert
that the rule was already present in `Sigma_orig` and does not embed its result
into the unchanged `Reg_orig` family.

For the reviewed source `my id x=x; my answer=id 0`, the complete declaration
`C_decl` is projected from the typed source presentation retained by the actual
`D_pub/G_id`; `m_C` is the whole allocation map `mu_id` restricted to that
declaration and its dependency-closed base; `C_use` is its simultaneous typed
image. The adopted constructor retains the full binder tree, all clauses and
alternatives, guards, provider/future dependencies, shared incidences, source
reference, original scopes and actual formation derivations. The source leg
`mu_id(r_id)` remains distinct from the registered module root.

The exact constructor domain remains the genuine source derivations at their
L1–L5 local-law premises. Neither solving, successful execution, satisfaction,
native IDs nor provider identity forms the declaration. A failure of any local
premise blocks that instance of the constructor.

## Conservative scope

Every old constructor, old registered declaration/equation, operand, and
meaning stays at its original registry domain. Old-only derivations retain
their original interpretation. The new registered roots live in the explicit
`Reg_orig^M` extension case; old opaque predicates or consumers do not
implicitly quantify over or accept these roots. This adopts exactly the
proposal's old-constructor preservation law, not a global conservativity or
all-axioms model-extension theorem.

For the same fixed indices, the actual `MReg-Intro*` derivation now discharges
the **local module registered-root construction premise** in original-generation
§7.2(2), when that operand is interpreted in `Sigma_M`. This closes one
localized parent premise for the reviewed source. It does not establish an
unchanged-family `Reg_orig` member or make the new root usable by existing
IF-Insert/IF-Use, OSig-Demand, O0 or complete Call rules. Those applications
still need their actual original-compatible registration and call derivations.

## Open obligations

The adoption does not prove old/new whole-source admission or observation
equivalence, source/native field correspondence, implementation lifetime or
invalidation, complete Call signature applicability, argument Reify/carrier,
all original checking clauses, F1/FK1, N-Transport, soundness, principality,
termination or production. The audited compiler has no complete typed source
producer/native `Phi_u` mapping for these fields, and inherited write ownership
for `candidate_source.rs` and `candidate_call.rs` remains UNKNOWN and quarantined.
No compiler code, test expectation or runtime behavior is authorized or changed
by this adoption.

Original theorem quantifiers, client/source domain, guards, alternatives,
assignment and strategy requirements, future/lifetime obligations, and source /
native correspondence requirements remain unchanged. The new constructor
supplies only the selected module-registration interpretation described above.
