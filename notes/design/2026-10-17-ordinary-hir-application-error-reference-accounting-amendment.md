# Candidate amendment: ordinary HIR Apply error-reference accounting

Status: candidate correction to the adopted rev4 resource statement; independent
compiler, spec and pre-code architect review pending. This amendment is limited
to asymptotic resource accounting. It preserves all rev4 syntax admission,
error behavior, error/diagnostic payloads and ordering, dense IDs, the public
`Box<[HirErrorId]>` representation, carrier identities, source keys and atomic
publication contract. It does not authorize code until the listed reviews and
Luna's adjudication are recorded.

Adopted input:
`notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`,
revision 4, SHA-256
`2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
The adopted §2 claim that *all* retained entries including aggregate Apply
error-reference arrays, and their construction work, are linear in the number
of expression nodes is falsified by the frozen lower bound in
`notes/theory/2026-10-17-ordinary-hir-call-projection-preservation.md`, §1,
SHA-256 `226d389d8fb68b6ddec328dd0f6ece4a4f3f2e344eff3f434d10b0a3d02b37ad`.
The rev4 bytes remain unchanged and preserved.

## Proposed output-sensitive replacement

Let `V` be the number of unique retained canonical expression nodes in one
admitted body, `E` the number of distinct operand `HirError` records emitted
for it, and `R` the total number of `HirErrorId` references physically stored
across all retained `Apply.errors` arrays. The retained HIR contract requires a
parent Apply to expose the ordered unique errors of its complete subtree, so
`R` counts repeated references to one authentic child error in distinct
ancestor arrays; it does not count additional error or diagnostic records.

The linear claim is replaced by these separate bounds:

- Shape preflight, the explicit node worklist, source-node/key validation and
  occurrence-plan records visit/store each unique retained syntax/HIR node once:
  `O(V)` node/control work and storage, with the concrete identity-map lookup
  and unchanged whole-module/carrier costs stated separately.
- Each operand error event is emitted once, so error/diagnostic records are
  `O(E)` and `E <= V` for this grammar.
- Flattening the specified descendant lists performs work proportional to the
  output it actually writes. The children of each Apply are disjoint source
  subtrees, each leaf error handle is unique, and Group forwards its child's
  ordered list. Therefore concatenating child lists in source order requires no
  per-list deduplication scan: every destination reference is written once.
  Aggregate-list assembly is `O(R)` time and storage.
- The total projection accounting is consequently `O(V+E+R)` node, event and
  error-reference operations/storage, excluding spelling bytes, source-map
  implementation costs and the existing module/carrier passes. Since `E<=V`,
  this is `O(V+R)` under that explicit accounting. The bound is output-sensitive;
  it is not a linear-in-V guarantee. Worst case is `O(V^2)` for flat owned
  subtree lists. No global wall-clock, parser, solver or termination theorem
  follows.

The lower-bound family `E_0=Name(f)`,
`E_i=Apply_ml(E_(i-1),Name(x_i))`, with all names unresolved, has
`V=2m+1`, `E=m+1`, and
`R=Sum(i+1, i=1..m)=m(m+3)/2`. It satisfies the unchanged duplicate-free
subtree lists, but requires `Theta(R)=Theta(V^2)` independently owned ID slots
and writes. This is the real output size imposed by the adopted API and error
ownership contract, not avoidable worklist overhead.

## Construction and failure obligations

For a candidate implementation, compute child aggregate lengths with checked
arithmetic. Reserve every per-node `Apply.errors` destination for its exact
length before publication; append the callee list then argument list. Distinct
subtree ownership plus one error event per unresolved/ambiguous name proves no
same-list duplicate. Do not emit a second diagnostic when copying a child ID
into a parent list. If aggregate counts, occurrence ordinals, or any required
allocation fail, return the specified availability failure and publish no HIR
module or partial source-identity stage. Reserve and account for all `R`
references, not just `V` nodes. Actual allocation strategy and measured fixture
counts remain implementation evidence required by the sprint.

This interpretation keeps rev4's public flat-list contract and every observable
error. A shared/lazy error-list representation, local-only Apply errors, omitted
ancestor references, a syntax-depth limit, grammar narrowing, or deleting
operand diagnostics would change the adopted API or behavior and is not covered
by this amendment.

## Review gate and theorem boundary

Fresh compiler-referee and spec-auditor reviews must check the exact family,
count, flat-slice lower bound, output-sensitive construction and unchanged error
observations. A fresh architect review follows those two and checks checked
counts/reservations, failure atomicity and the resource allocation transfer
before any implementation writer starts. Luna adjudicates only after all three
are CLEAN. This note alone is not adopted authority.

The lower bound refutes only rev4's linear-all-retained-entries resource clause.
It refutes no original Call/F1/FK1 theorem and closes no original theorem gate.
No test, implementation, production or inference semantics follow until review
and adjudication.
