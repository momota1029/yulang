# NPAIR source-admission code continuation

Sprint: `npair-source-admission-correspondence-20261018`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original
quantifiers and source domain retained.

## Authorization and frozen inputs

The exact adopted source slice was specified in
`notes/design/2026-10-18-npair-source-admission-contract.md` (SHA-256
`692aa39ec37f522e921634134551dad1933b736e5afd2eff463213970a0fb609`) and its
inbox (`91e5b35b776f9b3052cbc73a0a4c39d59dd3fdac946eec2b0a8d337d2855cf4d`).
Fresh independent compiler review found no findings on these exact bytes;
fresh independent spec review also found no findings and confirmed this is
already adopted semantics. Both reviews left the parent closure at 0.

Source correspondence proof and HIR continuation inputs are frozen at
`notes/theory/2026-10-18-npair-source-admission-correspondence.md`
(`7d29e2ebcf9a0509b1ddd2fc101905e7f865509012aebf193351fedf72bf91f7`) and
`notes/theory/2026-10-18-npair-hir-source-admission-correspondence.md`
(`930f99d168ede5e5592a6348ffc4a6f84ccd40c8d78128befaf91297816bafc2`). The
HIR proof closes the inspected HIR clone/source-identity premises and records
the scheduler/publication boundary. Text-to-CST formation remains an explicit
runtime regression premise; this implementation must falsify it through the
normal source entry.

## Exact write scope

Luna grants a conditional, bounded primary write lease to
`crates/yu-solver/src/candidate_source.rs` only. Change the negative
`preflight_formal` row predicate to admit nonempty concrete-only rows and add
the single focused regression defined by the frozen implementation contract.
`candidate_call.rs`, `candidate_effect.rs`, the HIR parser, all expected outputs,
and other files remain outside this write lease. No semantic decision is added.

The regression exercises `parse_file` → `lower_module_with_local_source` →
`CandidateInference::solve`, checks the authentic concrete row in HIR, proves
normal completion for the adopted result/result negative port, and preserves
accepted omitted/singleton-symbolic/positive cases and rejection of explicit
empty/mixed/multiple-symbolic negative neighbors. The exact targeted test is
the only Cargo command authorized in this continuation. Any code delta must
receive fresh independent compiler review before integration.

## Gate accounting and limits

At continuation start, the sprint had charged 660/1500 seconds. Contract
compiler and spec reviews consume their full 120-second grants, and this code
continuation consumes its 300-second grant. Astra remains 0. This leaves 300
seconds for the code-delta compiler/spec review and contingency. No parent
source/native condition is counted closed until the implementation result and
its source proof are independently reviewed and applied to the parent.

The proof composes the adopted source admission with the reviewed local
producer only conditionally. It does not establish a consumer, `At`,
N-Transport, N-Subtract-Elim, complete Call/effects, F1/FK1, soundness,
principality, termination, or production readiness. Errors discard the private
candidate attempt; the route does not claim producer-style local rollback.
