# Finite native row saturation: construction handoff

Date: 2026-10-26. Producer: generic leaf
`/root/finite_row_solver_construction`; no children.
Requested role instructions: `.codex/agents/lean-prover.toml` and
`.agents/skills/yulang-lean-proofs/SKILL.md`; no separately observed custom-role
or model/effort execution identity is claimed.
Status: **kernel-checked, frozen, writes stopped; independent review and
integration remain primary-owned**.

## Original goal, authority and exact writes

The unchanged parent is `SourceProblem.InferenceSoundness` in
`YulangClosure/Contracts.lean` and `docs/yulang-whole-proof-closure-ja.md`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Its full original source domain, scopes and one shared witness remain intact.
The original whole-source theorem remains **OPEN**, including optional/width
records, methods, complete Call, contextual effects, original publication,
fresh-use/extrusion/intrusion behavior and actual native/output correspondence.
The work constructs a proof-side reference solver; it adds no production pass
and does not assert native `Ok` implies reference `solve` success.

Assigned branch/baseline: `yulang3`,
`218ea864b7284468b6ab1f480f490e93522ea6af`. Primary subsequently reported
integration head `f5b947056f23fb50236463d86738bdea579c1514`. The producer used
no Git command, Rust write, Cargo invocation, shared status edit or root import
edit. No child was spawned.

Exact repository writes, all new:

- `notes/theory/lean/YulangClosure/NativeRowSaturation.lean`.
- `notes/theory/2026-10-26-finite-native-row-saturation.md`.
- `tasks/agent-loop/inbox/20261026-inference-native-row-saturation.md`.

All other writes are under
`/workspace/scratch/f98087c7ac1a/inference-native-row-saturation/`, including
the isolated project and its generated build/cache files. No frozen dependency
was edited. Source and project copies are byte-identical and end in one LF.

Read the AGENTS/pre-sprint operating map, proof skill and its source/execution
references, role instructions, governing design/top-level inference principles,
goal-driven sprint rules, native correspondence progress, accepted row-model
paper/handoff/review, actual original Contracts/Store/history definitions and
the existing Regular expansion and LatticeDecision finite-iteration proofs.
No broader native/source theorem was inferred from a prior acceptance receipt.

## Constructed result

The 557-line executable Lean component accepts the existing arbitrary finite
`NativeRowModel.System` grammar. It enumerates bounded same-kind row/head pairs,
starts with those absent from the original clauses, and emits lower-head
propagation through row→row and row→head clauses plus exact structural children
from head→head clauses. Existing `Regular.expandNodes` supplies every constructor
case, including Function signs `(-,-,+,+)`, both effect ports, full ordered
record/tuple/variant lists, optional bits, tags and payload arities.

Every changed round strictly shortens the pending list. The invariant proves
its initial length is sufficient to reach closure; there is no unproved fuel
cutoff. Pending/retained separation is initialized and preserved, so additions
are new comparisons. The original clauses remain a literal list prefix and
the row/head tables stay definitionally unchanged.

Finite checks detect original bounds, head formation/reference bounds,
incompatible head expansions and generated out-of-universe children. Error
values carry finite offending comparison or kind/head-index lists. These local
checks do not decide `Saturated` directly. The actual propagation proof supplies
its three closure fields, and syntax checks supply the other two.

Success yields the canonical graph and shared interpretation for the ORIGINAL
input clauses. The solver also has least-membership and exact syntactic
completeness theorems. Neither completeness nor model construction is promoted
to the broader native/source semantics.

## Exact principal theorem types

Names have prefix `YulangClosure.SimpleSub.NativeRowSaturation.`. The complete
fully qualified types of every originating declaration, including generated
and private ones, are retained in `check06-all-origin.log` and
`all-origin-records.json`. The following types are reproduced with local
namespace abbreviations only:

```lean
remaining_strict {s prior pending}
  (changed : remaining s prior pending ≠ pending) :
  (remaining s prior pending).length < pending.length

clauses_prefix (s : System) :
  ∃ extra, (completed s).clauses = s.clauses ++ extra

solve_success {s out : System} (success : solve s = .ok out) :
  out = completed s ∧ out.rows = s.rows ∧ out.heads = s.heads ∧
    (∀ p, p ∈ s.clauses → p ∈ out.clauses) ∧ Saturated out

solve_original_model {s out : System} (success : solve s = .ok out) :
  out.graph.Valid ∧ out.graph.Guarded ∧
    (∀ p, p ∈ s.clauses →
      Lattice.RegularSub out.graph (renamePair out.names p)) ∧
    LatticeDecision.decideDemands out.graph
      (s.clauses.map (renamePair out.names)) = true

solve_original_store {s out : System} (success : solve s = .ok out)
  {store : Store}
  (decoded : decodeStore out.graph out.names store =
    some (s.clauses.map (renamePair out.names))) :
  StoreSatisfied out.graph out.names store

solve_original_history {s out : System} (success : solve s = .ok out)
  {ref birth first events}
  (history : ConstraintHistory out.graph ref birth first
    ⟨s.clauses.map (renamePair out.names),events⟩) :
  out.graph.Valid ∧ out.graph.Guarded ∧ Holds out.graph first.obligations

clauses_least {s : System} {target : List Comparison}
  (sat : Saturated (withClauses s target))
  (included : ∀ p, p ∈ s.clauses → p ∈ target) :
  ∀ p, p ∈ clauses s → p ∈ target

solve_exists_iff (s : System) :
  (∃ out, solve s = .ok out) ↔ ∃ target : List Comparison,
    (∀ p, p ∈ s.clauses → p ∈ target) ∧
    Saturated (withClauses s target)
```

`solve_complete` proves the reverse direction from any same-table saturated
extension. That hypothesis is used only in the converse/minimality arguments,
never as an input to the executable solver or successful-output soundness.
Leastness is comparison membership, not list/multiset equality or semantic
least-model existence. The success iff theorem characterizes the exact finite
syntactic problem; it is not arbitrary lattice/model satisfiability completeness.

Computed by `rfl`: successful unsaturated recursive input, original four-clause
Store decoding, alias-cycle success, incompatible atom rejection, malformed
bound rejection and duplicate-label rejection. The recursive input needs the
algorithm to generate its missing head/self comparisons. Generic theorems then
derive the actual original Store and decision results. Function signs and
optional/tuple/variant metadata discriminators use exact expansion computation.
No example assumes `recursive_saturated` from the old component.

## Actual checks, limits and retained failures

Pinned executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Observed Lean: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
Read-only version commands exited 0. The existing locator required authorized
`require_escalated`; no installation or toolchain/configuration change occurred.

Assigned limits: 1,800 seconds, at most 18 focused calls, each 120 seconds,
one thread and 1 GiB per Lean process. Used **six focused calls**. The isolated
runner sets `LEAN_NUM_THREADS=1`, kills the entire process group on timeout,
and preserves each log. Project and direct audit options include `-j1 -M1024`.
No timeout occurred. Focused checker elapsed times total 74.215 seconds.
No further optional proof change/check followed the final origin audit.

| Log | Command/result and repair |
| --- | --- |
| `check01.log` | `lake build +YulangClosure.NativeRowSaturation`, exit 1, 57.118 s. Dependency cone built. Reserved `universe` identifier and unreduced local `let` obstructed elaboration. Renamed to `pairUniverse`; reduced the local `let`. |
| `check02.log` | Same focused target, exit 1, 3.253 s. Two uses of the renamed membership lemma were stale; corrected them. |
| `check03.log` | Same target, exit 1, 3.387 s. `subst` could not find an equality still inside a conjunction; destructured the successful-output theorem. |
| `check04.log` | Same target, exit 0, 3.718 s, 15 jobs. Full construction, converse and examples checked. |
| `check05.log` | Same target, exit 0, 5.075 s, 15 jobs. Final absent-pair initialization and preserved separation checked. This is the frozen source build. |
| `check06-all-origin.log` | `lake env lean -j1 -M1024 AuditNativeRowSaturationAll.lean`, exit 0, 1.664 s. Every originating declaration audited. |

All command lines are preserved in their logs. `source-scan.log` records `rg`
exit 1/no matches for proof holes, project axioms, `native_decide`,
`ofReduceBool`, or kernel bypasses in the copied dependency cone. This scan is
supplemental; complete indirect axiom checks supply the stronger evidence.
No default/integration build is claimed; primary owns that step.

## Complete originating-module audit

The audit selects declarations by actual originating module index, includes
private/generated declarations, rejects project axiom declarations and
duplicate records, requires all 40 authored theorem roots, prints exact types
and axiom dependencies, and rejects any dependency beyond the allowed standard
axioms. Every begin/end record was parsed and matched independently of the
summary count.

There are **142 unique declarations**: 81 theorem constants, 55 definitions,
four constructors, one inductive type and one recursor. Three are private.

| Axiom dependencies | Theorem constants | All declarations |
| --- | ---: | ---: |
| None | 14 | 54 |
| `propext` | 26 | 47 |
| `propext, Quot.sound` | 41 | 41 |

No `Classical.choice`, project axiom, `sorryAx`, unchecked native-evaluation
assumption or bypass appears in any new declaration's audited dependency
closure. Every principal theorem reproduced above uses `propext, Quot.sound`.
The code is executable and contains no noncomputable model selection.

Audit program: `project/AuditNativeRowSaturationAll.lean`.
Complete log: `check06-all-origin.log`.
Complete record extraction: `all-origin-records.json`.
Counts: `audit-summary.json`.
All paths in this section are relative to the owned scratch directory.

## Frozen artifacts and dependencies

| Artifact | SHA256 |
| --- | --- |
| `NativeRowSaturation.lean` | `9f8e2cf43ade40c17a09387d5888833002ee42791eff0d2d608f83d6ca39e974` |
| Theory paper | `c16cabe5a514ef0a99ecbe983961a148a70f54117e7830d923cb580fb89a7577` |
| `check05.log` | `1c6b48ea37ddee4821a39158a165710cb3d7730733ebb4ff1204d959e331221b` |
| `check06-all-origin.log` | `04cd41210b825319e63396f7c881d84a5148b060ab9e256892d216a81ddc6264` |
| `all-origin-records.json` | `24c1bfdfd2e567300b5f41d9839841d8a95548c906d9a3d8ca7f96aaeb1dc763` |
| Audit program | `7cad236eae3997d3f64c9cf274b46c8d005303f8f6cab250c74db56af81059de` |
| `frozen-lean-manifest.json` | `01ecf6cfe27bbc2a2e8b0d0c49e2123044bec00055826ed28e871141311d6a1e` |

The complete source/configuration hashes are in `frozen-lean-manifest.json`;
every entry was compared against the current repository without a mismatch.
All retained log/audit/version/runner hashes are in `evidence-hashes.json`.

The assigned accepted `NativeRowModel.lean` originally had SHA256
`16835744153d05150992175ddb866ccc202e0f31781ed1a5a26c3e55c54a26bb`.
Primary removed exactly three surplus terminal newlines for integration, with
no Lean token change, producing
`30016f40295a803df2ed3d9b46efd256d1427400f55bda1810e22a00f89d7780`.
The isolated dependency was refreshed to that exact current file before the
first build. `input-hashes.json` preserves the historical initial read;
`frozen-lean-manifest.json` records the actual checked dependency. This leaf
never edited either repository version.

## Exact remaining owners and cessation

The native/source owner must establish faithful all-eight-lane finite readback,
successful native execution's relation to this computed reference solver,
actual output/graph/reference/history transport, and the original publication
and source-scoped witness reconstruction. In particular, neither an inventory
fixture, a restricted completed-block replay result, nor a native `Ok` is
promoted to reference-solver success. The exact structural relation still
requires equal record order/labels/optional bits and does not discharge full
optional/width cast plans, method/Call or contextual-effect identities.

The original theorem and its domain stay unchanged. No mathematical obstruction
was found for the precise finite structural `System` construction; no broader
semantic completeness claim is made. The first new bridge is actual successful
native execution → faithfully represented original input plus a successful or
soundly related reference closure, retaining the actual output meaning.

**All producer writes stopped after this handoff.** No checker subprocess is
running. The source, paper and complete evidence are frozen for the fresh
nonauthor reviewer. Primary owns review adjudication, shared status, root
imports, complete integration audit/build, commits and pushes.
