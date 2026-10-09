# Complete-Call Reify construction direction

Date: 2026-10-10
Status: user-approved bounded design direction; source construction and conformance open
Authority: approved `call-reify-registry-construction/q2/d1`; integration receipt at the matching q2 directory

## Scope

For the complete Call contract, including `f 1`, adopt the four independently
reviewed construction choices in
[`2026-10-10-original-call-reify-constructor-proof.md`](../theory/2026-10-10-original-call-reify-constructor-proof.md):

1. Retain the old registry binder and place new registrations in a typed tagged
   registry sort.
2. Add the structural Call-argument registration and license case.
3. Retain a suspension attachment at new argument payloads.
4. Construct the source-owned literal image domain, clause, and root `J_lit`.

`J_lit` remains distinct from arbitrary old image `J`; no equality or fixed-old-
root identification is selected. Preserve all complete Call fields, including
effects, protection, admission, licensing, and image obligations. Four-port
endpoint solving is not the success criterion.

## Required next construction

Construct and check the actual selected-source `P_old`, including its complete
registrations, lookup/inversion, and old-consumer dependency closure. Then
construct and check remaining complete-Call dependencies against the original
source and selected laws. The reviewed proof assumes `P_old`; it does not
discharge this source obligation or establish untagged `H_oldext`.

The later upstream `RuleCall_L`/`CertCall_L` construction at `c0d304113` is a
separate, unadopted research extension. This direction does not incorporate its
new declarations or semantics.

## Explicit exclusions

This direction does not establish complete Call emission/O0/O1, C0/admission,
complete solving, principality, public export, acceptance of `f 1`, compiler
implementation, or F5 cutover. Each remains behind its own source-conformance
and implementation gates. The approved handoff adopts a construction route;
it is not a claim that its premises already hold in the selected source.
