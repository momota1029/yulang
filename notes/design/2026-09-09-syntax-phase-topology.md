# Syntax-phase public topology

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the explicit request to reconstruct parser
responsibilities rather than mechanically rename temporary paths.
Reviewed-by: scoped read-only topology audit.

Scope: replace the private omnibus `parse.rs` topology with direct owners:
`syntax_environment.rs` for selected imported syntax inputs and provenance,
`syntax_diagnostic.rs` for recovery and operator-construction diagnostic model,
and `full_parse.rs` for HeaderInfo/environment assembly into ParsedFile. Public
root exports, source/header behavior, syntax acceptance, diagnostics, and test
contracts remain unchanged.

Authority: the user's current topology direction, existing public syntax phase
boundary, and repository topology-cleanup authorization in `tasks/current.md`.

The dependency direction is strictly `syntax_environment` and
`syntax_diagnostic` into `full_parse`; `full_parse` alone owns HeaderInfo's
private recovery/table assembly and calls `source_file` for direct root
construction. `ParsedFile` stays with `parse_file`: it is the immutable product
of that same assembly boundary. No generic `parser/` directory, compatibility
forwarder, or duplicate public API is introduced.

Before closure preserve root re-exports exactly, retain all existing public
two-phase/header identity/diagnostic ordering controls, run the direct public
and full-parse tests plus package check, format and diff. Measurement budget:
zero samples/processes.

Construction completed 2026-09-09. M2 topology preflight and delta review
confirmed one-way dependencies, unchanged root re-exports, private opaque
environment identity, and tests co-located with their semantic owners. Syntax
environment/diagnostic tests (5), full-parse assembly tests (9), public
boundary tests (8 passed, one existing manual measurement harness ignored),
package check, format check, and diff check passed. Benchmark use: zero
samples/processes.
