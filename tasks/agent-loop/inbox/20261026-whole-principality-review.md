# Independent review: original principality algebraic boundary

Review-ID: WHOLE-PRINCIPALITY-REVIEW-20261026/r1.
Reviewer: `/root/effect_hygiene`, assigned by the primary after freezing the
disjoint Effect hygiene production packet. No authorship, co-construction or
repair contribution to the principality artifact; no descendants.
Decision: **ACCEPT for the stated local algebraic result and its fully
discharged example.** No blocking, major or minor findings in the reviewed
scope. Original whole-Yulang principality remains **OPEN**.

## Frozen review target

| File | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalPrincipality.lean` | `c9d214cd086aa1fbdf8f471e7b52c8cccddaa971fc68a8bb0956c9539d098dc7` |
| `tasks/agent-loop/inbox/20261026-whole-principality.md` | `1fa16f53dbac6ae7f471dba66c1cd867c5aef389a81f3a55fb17508694b2bdb4` |

Baseline stated by the packet: `a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`,
`yulang3`. The review concerns exactly those target bytes.

## Inspected scope and reasoning

I read the full new Lean module and handoff, the actual
`SimpleSubGeneralizationSoundness` definitions and required proof dependencies,
`SimpleSubConstraintSyntax`, the original source-preservation claim §§1, 3, 5,
the birth-level correction §§2–6, and `SourceProblem.PrincipalCoverage`.
I inspected the complete originating-module census output, its audit program,
the named audit's printed roots and execution receipt, and checked the input
and output hashes against the frozen handoff. The four relevant source modules
match the producer's isolated build copy byte for byte.

### Retraction and exact joint descent

`transport_idempotent` covers every coordinate, not just store occurrences.
For base coordinates, canonicality makes the second quotient application
idempotent. For a copied coordinate, the proof recovers its bounded use and
row, applies the quotient once, and distinguishes a lowered anchor from an
eligible copied representative. Both cases use the same canonical row on the
second application. Beyond all reserved blocks, transport is identity. The
zero-width and zero-use cases are handled by the same case split; division is
used only after establishing positive width.

`FiberConstant` is equality of complete assigned Terms on every same-kind
transport fiber. It does not assert source validity or hide the existence of
a quotient witness. The iff's forward direction derives fiber constancy from
one supplied descent. Its reverse explicitly chooses the original valuation
on canonical representatives, with idempotence proving the coordinate equation.
It neither selects separate per-use witnesses nor invokes choice.

### Genuine reverse store direction and observer quantifier

`quotient_uses_complete_on_fiber` starts with satisfaction of the original base
store, all requested use copies and arbitrary clients. Fiber constancy gives
the one function equality `rho o transport = rho`. The imported base and fresh
term squares then supply equality of interpreted endpoints for every retained
clause. The fresh square has the actual preserved-anchor and use-bound
premises; they are not inferred from canonicality alone. Client satisfaction
uses the existing renaming equivalence in the reverse direction. This is a
genuine pre-to-post result under the exposed fiber condition.

`joint_solution_coverage_iff` composes that reverse construction with the
existing forward pullback. Its `observe` argument is one predicate of the
entire valuation, so correlations between roots, kinds, shared anchors and
future coordinates remain in one existential witness. There is no exchange of
quantifiers into independent marginal observations. The theorem is per finite
count/client store; the handoff correctly does not turn it into one source
strategy for all future families.

### Concrete example: all premises actually discharged

For `n=3`, two uses, boundary 0 and quotient `2 -> 1`, the explicit map is:

| Coordinate | Transported coordinate | Valuation before and after |
| --- | --- | --- |
| 0, 1, 2 | 0, 1, 1 | atom 2 |
| 3 | 0 | atom 2 |
| 4, 5 | 4, 4 | atom 0 |
| 6 | 0 | atom 2 |
| 7, 8 | 7, 7 | atom 1 |
| 9 | 9 | union(atom 0, atom 1) |
| all later coordinates | unchanged | atom 2 |

This is the same assignment rule in both kinds. The class minimum at
representative 1 is 1, which remains above boundary 0. Thus rows 4 and 7 remain
distinct use coordinates rather than being identified with a shared base row.
Canonicality, store bounds, use bounds, valuation invariance and fiber
constancy are separately proved from the definitions. The anchor condition is
supplied by the existing quotient-level theorem with these concrete arguments.

The complete original store has three constraints. Both copies retain all
three, yielding nine base/use clauses; the future client adds three more.
The four-port Function packages become reflexive under each use's common
assignment. Their optional flag, required flag, field labels, tuple structure
and variant tag remain present. The clients are justified by union-left,
union-right and reflexivity. The final theorem uses the actual `before_satisfied`
proof and explicit valuation, not a presumed solution or LocalLaws argument.
Its forall-root equation covers every `Term` constructor in both kinds.

The noninjective equality `q 1 = q 2`, with `1 != 2`, is also discharged.
The separate disagreement obstruction uses the existing collapse-to-anchor
map and is correctly classified as algebraic, not a source-qualified
counterexample.

## Source and metadata boundary

The new module does not claim to prove `SourceProblem.PrincipalCoverage` or
construct its principal witness and original instance order. `Term` and `Sub`
remain the imported finite structural representation. They retain Function's
four ports, record optional bits/shape, tuple order, variant tags and kind, but
do not encode the full original Call/effect/evidence or recursive semantic
domain. The producer states that limit accurately.

The authoritative birth-level rule concerns immutable source Value births and
paths entirely inside one induced graph. The example's numeric type levels do
not establish such source qualification. No theorem in the new module equates
those two notions, and the handoff explicitly requires authentic occurrence
and source-demand correspondence. The obsolete cross-level helper rejection
is not used as a current counterexample.

The remaining source-derived shared strategy, actual freshenAbove allocation
and bound closure, complete semantic evidence, scheme ordering and uniform
future-family obligations are necessary parent work. They are neither silently
assumed nor discharged by this review. Acceptance is for the exact conditional
general theorems and unconditional finite algebraic example.

## Verification evidence inspected

No Lean build or audit was rerun: the frozen source/input hashes match the
already accepted producer outputs, and inspection revealed no concrete risk
requiring repeated execution. This review is independent semantic/proof review,
not a claim to have personally rerun the checker.

Verified log/program hashes under
`/workspace/scratch/e3678bef96db/lean-principality-work`:

| Evidence | SHA-256 |
| --- | --- |
| `named-audit.log` | `aa610fa959ed967b1b61c62535e3ce49f82adff3847ee61f4c3a86a503ec8442` |
| `census-audit.log` | `ff0d73dcbeff7b82a857564c4e2bfd266ee8441d8ae3a8bcbbecf36dc37f4818` |
| `AuditPrincipality.lean` | `40b4e9603d45d7c1c52b13c5bf26403899ace06dff75da7994dc8bf84a44dc12` |

The named log records Lean 4.35.0/Lake 5.0.0-src+eb6cafb, focused build exit 0
and 17 authored theorem audits. The census selects by originating module index,
not namespace prefix, and rejects project axioms. I confirmed 36 unique ordered
begin/end pairs, 36 complete axiom reports and the asserted distribution:
9 empty, 4 using only propext, and 23 using propext plus Quot.sound. The two
on-demand Generalization equation theorems are included. No choice or
nonstandard axiom is reported.

Verified direct input hashes:

| Input | SHA-256 |
| --- | --- |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| Original source-preservation note | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| Birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

Uninspected/unverified here: the unavailable original external PDF, Rust
execution and whole-machine correspondence, source strategy construction,
ordinary inference success/termination, repository-wide builds, and primary
integration across other new modules. None is needed to accept the stated
local algebraic theorem; none is certified by this review.

## Stopped receipt

The only repository write was this exact leased review file. No code, earlier
handoff, shared import/status, Git index/ref or other worker output was changed.
No child or long-running process was started. Review writes are stopped after
this revision. The primary owns adjudication, integration and any promotion
within this explicitly bounded accepted scope.
