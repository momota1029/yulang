# Retained Function-port context fibers

Date: 2026-10-10
Baseline: `3c42971ea6f53604537cf2c66ed3873f94ee248b`
Status: frozen, unreviewed research-only conditional information-recoverability
derivation and minimized detached witness. No source-reachable compiler
mismatch, executable Function-context conformance, or theorem closure claimed.
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–6, especially §4 Function ports, opposite replay, capture/freshening and
extrusion. Attachment grouping follows selected §3.1; it is not altered here.
Method: inspect pinned owning source and retained evidence; attack projection
of multiple contextual parent fibers to endpoints. This differs from the older
Effect-port field-collision and child-local closed-filter attacks.

Primary follow-up: implementation commit `0d2986b6f` now constructs the
approved child context from its exact parent relation, including the ordered
argument Swap/result Preserve and supported child-local prefix. The conditional
[Function-port effect-order proof](2026-10-10-function-argument-effect-contravariance-proof.md)
records its frozen-source basis. This baseline characterization remains
unreviewed and does not establish nonidentity execution, fresh-use transport,
or lifecycle conformance.

## Objective and result

Determine whether the current records can distinguish a Function operation
on its exact parent context from reconstructing context solely from endpoints.
They retain enough information for each ordinary port's local distinction:
`FunctionPort { parent, child, field, operation }` identifies the exact parent
relation, whose `RelationKey` includes its context. Distinct contextual parent
fibers remain distinguishable even when child-local admission interns one
shared child relation. The current executor does not consume that distinction.

The exact premise for recoverability is that a valid retained FunctionPort
incidence and its parent relation/context graph remain available in the same
source state. This is weaker than saying that the child already has the
required inherited context, or that an entire fresh use has a correctly renamed
operation graph. Neither latter claim is established.

## Actual owning path

Pinned `crates/yu-solver/src/lib.rs:11859` installs the work item's retained
relation as `context.processing`; `candidate_context_execute` runs before Value
memo handling. Function decomposition at `:12023` emits these ports:

| Field | Child pair relative to lower Function L and upper Function U | Recorded operation |
| --- | --- | --- |
| Argument | `arg(U) <= arg(L)` | Swap |
| ArgumentEffect | `argE(U) <= argE(L)` | Swap |
| ResultEffect | `retE(L) <= retE(U)` | Preserve |
| Result | `ret(L) <= ret(U)` | Preserve |

At `lib.rs:12073` each task receives the result of
`candidate_function_port_admit` before enqueueing. In pinned
`candidate_context.rs:1652`, `candidate_context_admit` constructs the child's
context using `candidate_context_source(child_pair)`. That function introduces
a closed filter only for an Effect pair with an upper closed Allowance; a Value
pair receives identity. The Derived edge uses the retained processing parent
when its canonical pair matches. `candidate_function_port_admit`, at `:1675`,
then records `state.processing` itself plus the field and operation. It does
not replace the child's context with an operation on the parent's context.

`RelationKey { pair, context }` and `State::relation` (`:1414`) distinguish
contexts on the same pair. Dependency interning at `:1445` compares the full
enum record, so different parent RelationIds are not removed merely because
child/endpoints coincide. A second Derived edge may be redundant, but the
typed FunctionPort edge remains available with its operation and field.

## Conditional recoverability derivation

Fix a valid incidence d and assume:

1. Its parent and child handles identify retained relations; the parent was
   the actual processing relation for this Function decomposition.
2. The parent's context handle identifies its exact retained construction DAG,
   including weight/source owners and shared child handles.
3. The incidence field and operation have not been projected away or changed.

Read P from `relations[d.parent]`, C from `P.key.context`, and o from
`d.operation`. The inherited ordinary-port operation is determined uniquely:
`Preserve` selects C; `Swap` selects the operation `Swap { input: C }`.
This describes construction to perform; it does not assert that such a node
already exists or that structural `Swap(I)` may be admitted into the current
executor. Source-owned child wrappers still require their separate admission
at their construction point.

The same child RelationId can participate in several incidences. The inherited
obligation belongs to each incidence's parent C, rather than to a single value
reconstructed from that child's endpoints. No reverse lookup of a parent from
the child pair is needed. Source owner and attachment identities are read
through the retained DAG; neither nominal family equality nor source spelling
is used to replace them.

`State::retained_input` (`candidate_context.rs:400`) closes over both ends of
each Dependency. Therefore, if a child root touches two FunctionPort edges,
both parents and both context DAGs enter the evidence closure. Its
`CircuitEvidence::dependencies` iterator preserves those exact enum records.
The routine marks FunctionPort incidence `InertOperation` (`:494`), correctly
preventing this local information result from certifying executable readiness.

This is a conditional finite information argument, not the main constructive
compiler theorem assigned to the prover. It proves no runtime discharge,
source reachability of nonidentity Value contexts, or complete activation.

## Smallest contextual-fiber witness

Use fixed source-owned Function constructors L and U, with result endpoints
`ret(L)=a` and `ret(U)=b`. Keep their original owners and endpoints identical
in both derivations. Let w be one existing source-owned closed zero-word
Allowance payload with allowed set empty, its original owner O, exact source
position S, boundary view V, and original weight identity w. No nominal effect
family or attachment identity is merged. Define:

```text
I  = identity
C  = PrefixLeft { weight: w, input: I }
P0 = Relation(Value(L, U), I)
P1 = Relation(Value(L, U), C)
Q  = Relation(Value(a, b), I)
d0 = FunctionPort { parent: P0, child: Q, field: Result, operation: Preserve }
d1 = FunctionPort { parent: P1, child: Q, field: Result, operation: Preserve }
```

The required inherited result contexts are I and C respectively. In the
detached zero-word algebra, I has filter All and C has filter the empty set, so
they are semantically distinct as well as structurally distinct. Endpoint-only
reconstruction sees the same `(L,U)` and `(a,b)` in both and yields identity
for both Value pairs. Any deterministic function of only these endpoints
therefore cannot recover both inherited result contexts. Keeping d0/d1 and
P0/P1 resolves this exact ambiguity.

Within this fixed-pair/ordinary-result collision method, two parent fibers,
one common child, two labeled incidences and one nonidentity context node are
minimal: one fiber gives no collision; removing the context distinction gives
the same obligation. One zero-word payload avoids POP/PUSH counts, replay
bracketing, residual gamma generation and inferred-entry authorization.
This is not a global minimum over all source programs.

Reachability classification: L/U and a/b have the actual Function result-port
shape; w/C have an actual closed-Effect-payload shape. P1 deliberately combines
them into a detached Value relation. No current source route for that combination
is established. More strongly, the pinned live executor at
`candidate_context.rs:1790` rejects any nonidentity Value context before the
Function comparison can emit these ports. The witness falsifies universal
endpoint reconstruction on the retained representation, not current supported
source behavior. The existing tests `function_port_incidence_*` were read,
not run: they assert identity direct Function-child contexts on their source
cases and do not supply P1.

## Lifecycle limits and precise missing premise

Opposite replay retains ordered lower/upper RelationIds and constructs Replay
from their stored context handles (`candidate_context.rs:1938–1952`); its
Function-shaped result remains subject to the nonidentity Value consumer gap.
Extrusion and qualifying parent/copy transfer retain Transport witnesses and
the post-check context (`candidate_extrusion.rs:304–322`,
`candidate_intrusion.rs:570–574`, `candidate_context.rs:2038`). None of these
paths executes the FunctionPort operation.

Scheme capture stores bound relation handles and discovers their post-check
context payloads (`candidate_scheme.rs:605–623`). Freshening uses one shared
context remap per reconstruction (`:939`) and emits FreshUse transport from
each original bound relation (`:1019–1028`). These preserve access to original
provenance, but this trace does not establish a complete renamed FunctionPort
graph or a fresh parent-context owner for every original incidence. In
particular, `context_payloads` rejects BothFromRight because authentic per-use
certificate ownership is unavailable (`candidate_context.rs:939`).

The operation enum has only Swap/Preserve. Inferred-entry evidence is a separate
Lambda-owned Origin handle (`lib.rs:11174–11207`), never an ordinary FunctionPort
authorization for BothFromRight. The original Lambda scope/occurrence/cause
must survive any later authorization bridge; endpoint similarity is insufficient.

The next premise is a source constructor and live consumer that admit a genuine
nonidentity Value parent, apply the operation to that exact processing fiber,
and carry incidence through freshening/replay. Another detached context probe
cannot prove that premise. No second equivalent experiment was launched.

## Verification, independence and coverage

No executable checker, mutation, Python process, Cargo process, build, test,
formatter or Git mutation ran. The permitted Python allowance was unused:
0 of 1 process, 0 of 10 seconds, 0 allocated probe MiB. Static shell reads were
batched, at most four concurrently; aggregate CPU/RAM and task wall time were
not metered. No random seeds/ranges or exhaustive source search apply.

Checks: targeted pinned `git show`/`sed` and `rg`; baseline HEAD read; direct
dependency blob lookup; dependency diff against the pinned baseline (empty);
SHA-256 identities below; leased-note whitespace check. Some combined task and
rule output was truncated; targeted source sections and the governing document
were read separately. No complete all-path reachability induction is claimed.

The algebraic distinction uses the approved operation contract and the pinned
detached evaluator (`candidate_context.rs:1009–1061`), so it is not an independent
semantic oracle. The source producer/consumer trace supplies separate artifact
evidence; it does not validate its own assumed transition semantics by counting
cases. Named shortcut attacked: dropping parent ContextId/RelationId before
ordinary-port operation. Failure conditions include a missing parent/DAG,
projected incidence, changed source identity, stale fresh-use transport, or
incorrect wrapper discharge; executable coverage of those conditions is absent.

Direct frozen dependencies (Git blobs at the baseline):

| Path | Blob |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `1b036291c8c52a5723f070d80ac655f6355e5629` |
| `crates/yu-solver/src/candidate_context.rs` | `3e54c3ca914e7c9d98fd220aa9be9c4b89f18188` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `3e20bcddc9d8f2ee4961287490600c9aee1da262` |
| `crates/yu-solver/src/candidate_effect.rs` | `d1fd99d140c3f3b9d9d4464c85639f0d0e5a2502` |
| `crates/yu-solver/src/candidate_scheme.rs` | `d1a7366bebd2c156cbd9c6d7d0b2b1223af789e9` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `bf8484f4a9bb447f90e2e8faebcfee2fee2ed056` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `d2c444e7d369fb10ec8ba3c2d94a385b219e38ab` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `c99873544ca90aa817c77941514f7868a8023d65` |

Authority SHA-256: `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
Context source SHA-256: `470a5d45b6a7d6d2faf55de388908fc6b724dac7a14af87a3ff67a227b975ac5`.

Recommended next action: assign separately authorized implementation evidence
at Function admission/execution, using the retained parent incidence and a
source-produced nonidentity parent; require fresh-use/replay continuity before
promoting local recoverability to operational conformance.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-10-function-port-context-falsification.md` only.
- Baseline: `3c42971ea6f53604537cf2c66ed3873f94ee248b`.
- Changed dependency hashes: none at freeze; pinned identities above.
- Claim/review: unreviewed research-only conditional information result and
  detached minimized witness. Producer is not an independent reviewer.
- Checks already run: pinned source trace, direct dependency diff/blob/hash
  checks, leased-note whitespace check; no executable verification.
- Proposed message: `research: distinguish retained Function context fibers from endpoint reconstruction`.
- Shared-record deltas left to primary/curator: distinguish retained ordinary
  port recoverability from live operation consumption in `tasks/current.md`
  and `tasks/research-lab.md` if accepted; retain fresh-use operation continuity
  and authentic Both authorization as open evidence. No authority/index/theorem
  status promotion proposed. Writes stop at this frozen artifact before review.
