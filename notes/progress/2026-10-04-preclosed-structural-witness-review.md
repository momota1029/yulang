# Two-sided structural witness: proof, implementation model, and review

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Base inspected: `eb7bc50dc519d7751395dbdd17c4b617c498d4b1`
Status: completed conditional research gate; no compiler implementation authority

## Request and classification

The user requested a direct attack on the two main remaining proof gates on
this branch. Earlier permission to use additional source-generated
hypotheses remains in scope. This slice closes a substantial structural
subcase, rather than another restriction of the current literal-only HIR.

Authority: existing research request and source-generated hypothesis
permission. Runtime behavior: unchanged. Surface: internal proof and
standalone research checker. Performance: cold, with no production hot-path
change. Mode: M3; one independent compiler_referee reviews this theorem and
its checker, within the two-reviewer budget across the paired research task.
No new semantic, API, resource-boundary, or compiler decision is selected.

## Result

[Regular witnesses from two-sided constructor bounds](../design/2026-10-04-preclosed-structural-regular-witness.md)
gives a self-contained specialization of Coquery–Fages's pre-closed-system
construction. After finite flat closure, every variable must have a
constructor-bearing lower bound and upper bound. This is a finite directed
source-package check. It allows multiple open recursive anchors and constructs
new graphs rather than selecting an existing anchor.

Within the declared pure mandatory structural signature and permission
condition, contradiction-free closure is equivalent to arbitrary-tree and
regular-tree satisfiability. A pair-of-nonempty-subsets construction gives a
simultaneous witness with at most `(2^n-1)^2` nodes for `n` flattened
variables. Exact recursive descriptor equations, Record width, Function
contravariance, and declared invariant coordinates are covered.

The condition is sufficient and not a new source rejection rule. One-sided
or unbounded roots, optional Records, effects, arbitrary guards, joint
`Phi/K,D`, principal projection and full source adequacy remain outside.
The witness leaves the original residual conjunction intact.

## Independent review and adjudication

The research exploration and standalone checker producer were separate from
the reviewing compiler_referee. Each agent received a fresh task packet
without parent conversation history. Repository role pins were used:
architect and compiler_referee requested `gpt-6.1-sol` / medium; implementer
requested `gpt-6.1-sol` / low. Runtime selection beyond the exposed launch
arguments is not separately certified.

The compiler_referee read both the theorem and checker in full, plus the
governing structural package, prior source-generated theorem and selector
boundary. It found no blocking, major, or minor issue. Its decisive checks
covered finite closure, equation antisymmetry, nonempty successor sets,
Record mask direction, negative and invariant descent, the simultaneous
comparison induction, the global equation invariant, witness size, and the
checker's independent validation of original clauses.

The reviewer did not certify literature attribution, production adequacy,
unrestricted FMP, or a practical resource policy. The primary separately read
the cited manuscript's §3.1 theorem and §3.2 limitation. No broader literature
theorem is claimed.

## Deterministic verification

The primary ran:

```text
python3 tools/check_preclosed_structural_witness.py
python3 -m py_compile tools/check_preclosed_structural_witness.py
git diff --check
```

All passed. The executable checker reports:

| Check | Result |
|---|---:|
| Focused positive, negative, invariant, and unmet-premise systems | 12 passed |
| Rejected existing anchor choices in the recursive example | 4 |
| Constructed graph for that example | 28 states |
| Exhaustively enumerated labeled two-node oracle graphs | 225 |
| Distinct oracle lower/upper compatibility profiles | 16 |
| Two-lower/two-upper one-variable packages | 2,401 |
| Satisfiable packages | 52 |
| Unsatisfiable packages | 2,349 |
| Agreement with the bounded oracle | 2,401 / 2,401 |

Each generated witness is checked against original inequalities by a separate
coinductive finite-pair simulation and against descriptor equations by exact
bisimulation. The oracle uses concrete graphs, not the closure relation;
it shares the direct simulation routine with witness validation. Its graph
bound and `Int`/`Bool`/two-label Record/Function inventory are explicit.
Agreement is finite diagnostic evidence, not the proof of arbitrary-tree
reflection. The full default run took about 0.06 seconds in the primary's
environment. No production benchmark or repeated measurement campaign ran.

No Cargo build, workspace-wide suite, Oracle probe, production inference
execution, or compiler test-contract update was needed or performed. Syntax,
reference, explicit diff, branch, and outbound-range checks accompany
integration. The primary synchronizes `tasks/current.md` and the design index.

## Next exact gate

The remaining unrestricted structural question includes roots lacking one
constructor-bound direction. The paper's nullary-extrema pre-closure theorem
does not apply to Function/Record constructors; recursively introducing fresh
children is not a termination proof. Source-specific coverage of the new
finite predicate is separate from this mathematical theorem.
