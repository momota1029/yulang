# Prior-publication construction checkpoint

Status: accepted bounded static obstruction report. No compiler semantics or
production code changed. The full Yulang inference/executor obligations remain
open.

## Fixed instance and evidence

The packet examined `pub id x = x`, explicit exposure `identity`, and implicit
prelude exposure `id`. It tested whether the existing prior-publication route
could construct and transport the provider certificate. The source handoff
traced export identity through provider `DefId`, module action, dependency-
ordered candidate graph storage and FreshUse reconstruction. That Rust path
did not establish a corresponding `OriginalSource.PublicationRecord`.

The proof handoff traced the existing Source binding and initializer → Return /
rebind → Shared route. `publicationCandidate` reconstructs a candidate record
from those event inputs. `publicationValid` also requires the fixed solution
map to contain the exact record. Existing Environment transitions preserve
that map; `publish` updates lexical names only. Native Context readback stores a
different `PrefixPacket` payload.

The independent reviewer accepted this bounded result. One source citation
was corrected: the production-certificate-disabled comment is at
`crates/yu-solver/src/candidate_source.rs:2381–2383`, not `2374–2377`.
Review inspected the relevant resolver/FreshUse tests but did not run them.

## Exact obstruction

Candidate reconstruction alone does not construct the fixed-map equation
`E3.publications p = some record` required by validity. Replacing the map with
an everywhere-`none` map leaves the candidate unchanged and makes nonempty
validity impossible. This is a direct unchecked definitional observation, not
a checked Lean theorem, a compiler-semantic counterexample, or proof that the
adopted source rules are inconsistent.

The missing evidence is a genuine provider Source, incoming Context and
environment correspondence; independent local admissions; and an
independently justified realization of the fixed publication map from the
provider derivation and event data. The existing replay theorem assumes
validity. The Rust candidate Graph/FreshUse path and Native PrefixPacket map
have no demonstrated correspondence to that original publication record.
Resolver exposure names also do not establish SRC-J monomorphic Alias.

Complete ordered import-root → Source/Context elaboration remains a separate
open equation. No new constructor, import classification or semantic choice
was adopted. No production implementation slice is justified by this packet.

## Execution and scope

All 55 rows across four pin manifests were independently rehashed; 36 unique
paths matched. Lean/Lake, Cargo, compiler, tests and formatters ran zero times.
The Lean gate was unmet, so there are no theorem types or axiom audits. Static
`agent_sprint.py check` passed; it is workflow evidence only. All parent gates
remain OPEN.

The user's capacity-release instruction remains capacity-only: nine
reservations were already released, so this repetition was idempotent. UNKNOWN
worker observations and quarantined path leases remain. Both active source and
proof lanes acknowledged synchronization; the independent reviewer was
launched after handoff freeze.

## Next evidence

Trace an actual provider source derivation and incoming Context through the
fixed publication-map realization, then establish both consumer exposure
lookups while preserving the complete record. Keep full import-root
elaboration separate. If new semantics become necessary, prepare concrete
alternatives and consequences for independent review before adoption.

The END dispatcher recommends `PROVIDER-SOURCE-SOLUTION-REALIZATION-20261027/r1`
for the next packet. Its goal is to construct the provider-specific chain from
authenticated declaration/formal/body through original Source and incoming
Context, actual initializer/Return-rebind/Shared events, fixed-map equation,
and full-record transport to both exposures. The source and proof lanes should
construct this witness rather than wait for it as a prerequisite. Keep the full
ordered import-root equation separate; admit paths, baseline, pins, boundary
and resources before assigning workers. No workers were started by the
dispatcher.

Evidence: `tasks/agent-loop/inbox/import-publication-construction-20261027-source.md`,
`tasks/agent-loop/inbox/import-publication-construction-20261027-proof.md`, and
`tasks/agent-loop/inbox/import-publication-construction-20261027-review.md`.
