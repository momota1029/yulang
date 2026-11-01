# R217 source annotation equation — frozen handoff

Sprint ID / contract revision: R217 / 1
Contract SHA-256: `b3ba54f58a654b22b65467737e25cff37c884cf64ecd798a6754a3d5d694e138`
Assignment: primary source/model author, Luna; session R217
Baseline: `yulang3` at `ef1873b5e`; original theorem and `supported` domain unchanged
Outcome class: **candidate / reviewed stopping result**

## Frozen outputs

- Model: `notes/theory/2026-11-02-source-annotation-elaboration-r217.md`
  SHA-256 `0462b51e301b0f21d764106f9f1f83a87a8e9f7533be5c14ae1820d813ab395b`
- Lean: `notes/theory/lean/YulangClosure/SourceAnnotationElaborationR217.lean`
  SHA-256 `e10a84fc095af0cd492f1dd8285eb0136f185b64a29a66deaddc35973c6c08d3`
- Contract: `tasks/agent-loop/sprints/source-annotation-elaboration-r217.md`
  SHA-256 `b3ba54f58a654b22b65467737e25cff37c884cf64ecd798a6754a3d5d694e138`
- Outcome: `tasks/agent-loop/history/20261102-source-annotation-elaboration-r217-outcome.md`

## Constructed equations

The candidate fixed signature contains annotation ID, owner, type scope and
the recursive current-carrier tree. `resolve` checks ID/owner/type scope and
does not take a solver assignment. Theorems `lookup_stable` and
`resolved_source_identity` establish that candidate table behavior. They do
not establish that original source annotations contain this table.

The pinned project command
`lake env lean YulangClosure/SourceAnnotationElaborationR217.lean` passed
using the existing `.lake/build`. Four `#print axioms` audits contain only
`propext` and `Quot.sound`. `value_view_ignores_root_effects` formalizes the
local frozen-Oracle equation that an `Effectful` wrapper is ignored in value
bounds and tuple values recurse through that projection.

## Source mismatch and remaining parent premise

The candidate Rust parser retains a row on a tuple child, while
`candidate_formal_value_pair` rejects tuple children with any row. Frozen
Oracle `main` (`a58eefc31e22141574b6f20c6a5748151c6d79f1`) recursively builds
tuple child annotations and `lower_value_bounds` erases an `Effectful` wrapper
in each value child. This is evidence that the candidate rejection lacks an
Oracle correspondence; no source-domain narrowing or new semantic vote was
selected.

A second correspondence mismatch is now explicit. Oracle builder takes
function `arg_eff` from the `TypeRow` under `TypeArrow`, separately from an
Effectful wrapper on the left parameter. The current carrier puts a prefix row
on the Function argument node, and candidate `valueView` treats it as an
argument-effect port. For `([E] int) -> int`, Oracle has
`param = Effectful(E, Int)` and `arg_eff = None`, then strips that wrapper in
value bounds; candidate `valueView` records `Some E` at the argument-effect
port. The theorem about candidate Function view is explicitly only a local
definition equation, not Oracle correspondence.

The original Lean source has `Annotation := Nat`; `sourceRules` forwards that
ID and entry to `sourceFormalRole`. `Kernel.atom` remains parameterized and
there is no annotation signature table. Consequently the candidate table and
value projection do not discharge the Lambda induction premise of the
unchanged `Contracts.SourceProblem.InferenceSoundness`. Parent delta: 0;
roots: 0/4; packages: 0/5. Effect hygiene policy remains unchanged, including
Permission/inflow/residual separation.

## Review and checks

Fresh independent `compiler_referee` `/root/r217_candidate_review`, requested
`gpt-6.1-sol/medium`, observed runtime model/effort `UNKNOWN`, returned delta
**PASS for the corrected incomplete candidate**. Initial review found the
Oracle rule had not been inspected; the delta review checked the frozen Oracle
path and caught the separate arrow-row mismatch. The final artifact limits
the claim to the exact value-bound wrapper erasure and records the Function
mapping gap.

`python3 tools/agent_sprint.py check`: PASS (static workflow validation only).
No tests, Rust edits/builds/Cargo, new environment, dependency changes or
source-coverage theorem. Existing Lean cache creation was explicitly
authorized by the user.

Next related step: construct the exact source annotation equation from the
frozen Oracle AST and the unchanged original `sourceFormalRole`, preserving
the difference between a row under `TypeArrow` and an `Effectful` value
wrapper; then prove how the original source `Annotation` ID selects that
declaration without changing the supported-source domain. Do not promote the
current-carrier `valueView` to that equation.

Worker state: primary stopped at the recorded source correspondence seam;
reviewer writes stopped after PASS. No descendant leases or generated outputs.
