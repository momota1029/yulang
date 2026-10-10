# Distinct-tail source constructor cut

Status: constructive ordinary-source witness with independent conditional PASS.
Research-only; no production conclusion.
Baseline: `9577b9dd578f2a995b9b9fd1df0d60b081523681`.
Producer: `/root/distinct_tail_constructor_search`.
The witness run used `77c4ac5bb`. The source-construction question for R is
constructively answered; broader restoration/correctness obligations remain open.

## Objective, authority and method

Find a source-owned distinct-tail Allowance escape from an older row reachable
from the actual positive owner copy C, followed by a continuation to original
S that does not return copied tail T' to original T. This is a bounded static
constructor/scope cut, complementary to the constructive proof lane. It does
not repeat execution of the prior local annotation or whole-argument variants.
No grammar-valid new source candidate was established within the assigned
three-minute static budget. No universal impossibility claim follows.

Governing authority is contextual-attachment-admission §§3.1–5 and parent-copy
SCC intrusion, “Selected operation and compiler responsibility.” Attachment
identity grouping, annotation polarity, exact scoped-tail identity and actual
recorded parent/copy equality retain their selected meanings. Rules
research-lab, design-authority, git-concurrency, agent-orchestration and the
yulang-proofs skill were read. No language decision or R status is changed.

Prior inputs: local-annotation-selective-route-probe, source-selective-scc-
impossibility-audit, source-owner-construction-search, hir-owner-scc-return-
path, positive-port-source-route-search and restore-product-rescue-proof.
Aggregate note/task reads truncated; subsequent narrow reads supplied the
constructor facts used here. This was not a complete reread of every prior
artifact or the entire current-task ledger.

## Exact conditional route and its source obligations

Assume a successful retained source prefix with distinct canonical S,C,T,T',R,X;
actual positive parent records (C,S),(T',T); levels S,T,X=d>t and C,T',R<=t;
and these physical edges at the same qualification snapshot:

```text
S -> C                          actual positive extrusion link
S -> Allowance(v[T]) -> T        original formal checking view
T -> T'                         actual positive tail extrusion link
C -> Allowance(v'[T']) -> T'     copied incoming-Allowance view
C -> R                          inherited older direct positive lower
R -> Allowance(w[X]) -> X        required distinct-tail negative bound
X -> ... -> S                   required ordinary source continuation
```

Then S->C->R->X->...->S closes the owner pair. If T' has no path to T in
that SAME physical graph, the tail pair does not qualify. This is elementary
conditional reachability; the last two edges and the negative reachability
condition are source premises, not established output.

The discriminant is a **negative Allowance on R**, not a positive Support
with the same tail. A stored negative Allowance exposes X in the physical SCC
graph but does not, by its presence alone, enqueue X against another upper.
Positive Support expansion does enqueue its tail against the comparison
upper (`candidate_effect.rs:753–776`). Thus substituting Support(w[X]) is a
different source obligation with additional tail-feedback risks. Endpoint or
family coincidence cannot justify that substitution.

| Required edge | Authentic constructor seam | Still required execution fact |
| --- | --- | --- |
| S->C and T->T' | Positive extrusion with actual parent retention | The retained pair IDs, polarity and target belong to this prefix |
| C->R | Extrusion reuses an older direct positive lower | The inherited lower is exact R; canonical identity has not changed |
| R->Allowance(w[X])->X | Root computation checking plus ordinary opposite replay | A real computation carrying R is checked against a view with exact original X, and replay installs that view physically on R |
| X->...->S | Original self-recursive callback invocation/checking | The continuation reaches original S, rather than a negatively extruded checking copy |
| no T'->...->T | Whole physical snapshot at qualification | All current edges and intervening intrusion effects are included |

The first three kinds of owners occur in prior authentic executions, but that
fact does not compose their identities or schedules into one witness.

## Root computation versus Function-result checking

The last failed whole-argument variant supplies a local annotation on a Lambda
value. Its `[E,'x]` sits at a Function result position. Its actual body/result
Value comparison can undergo negative structured extrusion before Effect
comparison, so it is not a direct check of the old R computation against an
original X view. Repeating that Function annotation with another symbolic
argument tail leaves this exact direct-computation premise unresolved.

The direct computation owner is instead
`candidate_annotation_computation_effect` (`candidate_effect.rs:1172–1208`).
For mixed rows it constructs a negative checking port and constrains the actual
component computation against it. For singleton symbolic rows it uses the
scoped tail itself, so that branch creates no new distinct-tail Allowance.
The actual root effect row must therefore be present on the annotation's root
SourceType. Merely finding `[E,'x]` inside a nested Function does not suffice.

A new annotated local binding has its own `AnnotationScope::Local(binding)`
(`candidate_effect.rs:987–994`). It cannot reuse bridge's original X by writing
`'x`. Scoped reuse is keyed by exact `(scope,name)` and preserves the first
allocation's level (`:844–864`). The prior local annotation execution already
shows that mismatch. This rules out that proposed shortcut under the stated
unmerged scopes, without ruling out all local-binding routes.

An expression ascription uses its retained HIR scope and constrains the child's
actual computation (`candidate_source.rs:388–410`). It is therefore a distinct
owning seam that can in principle avoid both the new-local scope and the
Function-result boundary. But the prior `as [E, 'x] int` spelling fails parsing,
and this assignment established no alternate grammar-valid root-effect
ascription in bridge's exact scope. Repeating that rejected spelling would
supply no new evidence. The missing relation is precisely:

```text
An ordinary parsed/lowered action A, in the exact scope that owns X,
admits H <: Check(w[X]) where H contains the already-shared old R,
and its real drain/replay retains R - Allowance(w[X]) before delayed
positive extrusion; the same retained prefix supplies original X -> ... -> S.
```

The source-owned computation action, exact X identity, and scheduling condition
must be obtained together. A supplied transition checker cannot prove them.
This is a reduced constructor requirement, not a proposal for a new source
restriction, carrier, test expectation, or semantic rule.

## Falsifier and evidence boundary

One ordinary-source execution would discriminate this seam by recording:
empty parser recoveries; the lowered ascription's exact scope; root annotation
SourceType.effects; actual component H and old R; admitted computation pair;
post-drain literal `R - Allowance(w[X])`; actual parent pairs; and mutual
reachability at the qualification snapshot. Failure of any identity, physical
key, order, or continuation falsifies this attempted route. A return through
T' that also reaches T falsifies owner-only qualification. Final snapshot
failure alone does not exclude an earlier qualifying snapshot.

No executable oracle was run. The static derivation shares the compiler's
physical-edge contract and assumes a successful source prefix; it is not an
independent semantic oracle. Seeds/ranges: none. Mutations: none. Executable
sources: zero. Omitted cases include parser derivation of alternate effect
syntax, full HIR-scope propagation, scheme restoration, intervening canonical
merges, complete callback schedules, rollback/retry, publication and all-source
reachability. No compiler defect or restoration omission is established.

Commands were bounded `cat`, `sed`, `rg`, `git rev-parse HEAD` (read only), and
`sha256sum`; no build, test, Git mutation, delegation, or generated scratch
artifact. Sequential lightweight shell reads only. CPU/RAM and aggregate wall
time were not measured; no heavyweight processes or performance samples ran.
The intended budget was under three minutes static; an exact elapsed total
was not captured.

One recommended next action: establish the parser/HIR construction of a mixed
root computation ascription in bridge's exact existing scope, then execute
that seam with the listed identity/physical-key observations. Do not repeat
another Function-result or different-local-scope annotation probe.

## Commit packet

Exact leased path:
`notes/progress/2026-10-11-distinct-tail-source-constructor-search.md`.
Baseline SHA: `9577b9dd578f2a995b9b9fd1df0d60b081523681`.
Dependencies edited by this leaf: none. Inspected direct dependency hashes:

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0 crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a crates/yu-solver/src/candidate_extrusion.rs
78e2400a5e69a2718fe17f243f82fa232f59fd199fdaf7b5e27212e11b0a4791 crates/yu-solver/src/lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e notes/design/2026-10-10-parent-copy-scc-intrusion.md
```

Review status: frozen unreviewed research only; no independent certification.
Checks already run: static constructor/consumer inspection and hashes; no
executable artifact. Primary must recheck dependencies at integration.
Proposed commit: `research: isolate distinct-tail computation constructor cut`.
Shared-record deltas intentionally left to primary/curator: preserve R OPEN;
record the exact root-computation/scope/action premise and Allowance-versus-
Support discriminant if adjudicated useful. No shared task, theory, index,
authority, question-board, compiler or test path was edited. Writes stop here.

## Ordinary-source constructive witness (primary diagnostic, 2026-10-11)

This addendum answers the source-construction question affirmatively. It is a
constructive witness to existence of the requested state, not a universal
theorem about every source program, not an implementation defect claim, and
not closure of effect hygiene or restoration correctness.

Exact source:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); bridge }
```

The equal-indentation row entries parse as separate atoms without commas.
The diagnostic run reported no parser structural recoveries and no solver
errors after the ordinary root action schedule completed. Its row levels at
the selected prefix were `S49=1`, `C55=1`, `R43=1`, `X29=1`, `T25=2`, and
`T'66=1`; the witness depends on actual graph reachability and parent records,
not a level inequality. To capture the
transient state, the root action list was stepped in its existing order; the
snapshot was taken at zero-based action 42 (`Lambda(1)`) inside
`candidate_intrusion`, after `graph.components()` and before its parent-merge
loop. This is one actual physical candidate graph, not a reconstructed graph
or an injected transition system.

At that snapshot, the observed nodes and edges were:

```text
S=Effect(49), C=Effect(55), T=Effect(25), T'=Effect(66)
R=Effect(43), X=Effect(29)
actual positive parent records: (C,S), (T',T), both target 1
SCC(C)=S; SCC(T') != T
C -> R                         direct positive lower
R -> Allowance(1) -> X         exact distinct-tail negative bound
X -> ... -> S                  ordinary physical graph path
S -> Allowance(0) -> T         original negative check
T -> T'                        positive tail path
T' -> T                        no path in this snapshot
```

Thus `S -> C -> R -> X -> ... -> S` closes the positive owner/copy SCC,
while `T -> T'` exists without the return path that would qualify the copied
tail with its original. The scope map assigns `'t` to row 25 and `'x` to row
29 in the same `Local(HirLocalId(0))` annotation scope, matching the formal
callback row and expression-ascription row. Parent provenance comes from
actual intrusion records and is not counted as a physical graph edge.

The snapshot is pre-merge: a later action (zero-based action 47, `Local`)
eventually closes the tail SCC too. That later state does not erase the earlier
qualifying state. The hook and test used to observe this were temporary
diagnostic edits and have been restored; no instrumentation or test was
committed. Captured diagnostic material is in `/tmp/yulang_final_snapshot.log`,
`/tmp/yulang_premerge_tail.log`, and `/tmp/yulang_exact_witness_snapshot.log`.
The independent compiler-referee review returned a conditional PASS: the
reported canonical nodes, actual positive parent records and same-invocation
SCC/path facts satisfy the selective owner/tail qualification criterion.
Primary log inspection confirmed the first selected snapshot's distinct
component IDs for the tail pair, direct `C55` lower `R43`, stored
`R43 -> Allowance(1)`, `T25 -> T'66`, and absent `T'66 -> T25`. The reviewer
did not independently execute the source; parser recovery, HIR scope and
action provenance remain primary-produced observations. The run used one bounded `cargo test` process,
one CPU affinity, a 1.5 GiB virtual-memory ceiling, and a 120-second timeout;
it reported one passing temporary probe and no failures. It was diagnostic
verification, not a retained regression test.

The fallback `tools/codex-prover.sh` launched a real nested child with
`agent_type=prover`; requested settings were Sol/high, while effective runtime
settings were not observable. That prover produced only a static parser/scope
route note and did not execute or certify this witness. The source witness is
primary-produced and received an independent conditional review. The global
restoration/certificate issue remains active and unresolved: no later missing
restore fiber or failed rescue path has been demonstrated.
