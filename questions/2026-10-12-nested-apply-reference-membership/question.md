# Nested Apply Value-reference membership

Question ID: 2026-10-12-nested-apply-reference-membership
Question revision: 1
Predecessor/history: `2026-10-12-apply-result-value-reference-owner`, revision 1
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): `28d4d7b88` (current branch baseline when drafted)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Apply-result source-fragment ownership”; predecessor approved answer, “Proposed decision and authorized scope”

## Requested scoped decision

The predecessor decision selects the equation “each resolved Name in an Apply source fragment contributes an edge from the result Value row to its actual binder Value row,” but does not define recursive membership in that fragment.

For the nested source shape:

```yulang
my use f = f(0)(0)
```

let `A1 = Apply(Name(f), 0)`, `A2 = Apply(A1, 0)`, and let `F`, `R1`, and `R2` be the original formal row and the two distinct Apply result rows. Decide whether `R2 → F` is an owned source-reference edge, in addition to `R1 → F`.

This question selects only nested-Apply membership. It does not authorize implementation, decide Lambda/Block/initializer boundaries, alter the parent/copy operation, or prove transport, SCC qualification, soundness, principality, complete Call, effects, or F5 replacement.

## Background and current premises

The user's approved Apply-result equation is source-computation incidence before and after Call dispatch. It rejects inferring edges from returned providers, Function ports, subtype constraints, bound storage, lexical levels, or extrusion ancestry.

The accepted `odd/even` and `host/outer/g` examples have the same relevant source-owner edges under both completions below. They do not contain a Name nested under one Apply used as an operand of another Apply. The current interpretation draft proposes a recursive source walk, but remains non-authoritative for this membership detail. The source auditor found no per-fragment Apply Name incidence emitted or consumed by the current candidate, so this question precedes any faithful SCC implementation.

The distinguishing graphs are:

| Completion | `A1` result | `A2` result |
|---|---|---|
| Nested Apply is recursively inside the outer fragment | `R1 → F` | `R2 → F` |
| A nested Apply is a fragment-owner boundary | `R1 → F` | no `R2 → F` edge |

Neither completion adds `R2 → R1`: syntactic containment alone is not a Name reference. Existing LocalSource constructors can represent the two-Apply shape conditional on successful checked source formation; parser/HIR admission has not been executed here.

## Options and consequences

### A. Recursively include nested Apply operands

An Apply result owns the resolved Name occurrences in the recursive callee/argument source subtree, including occurrences inside a nested Apply. For `f(0)(0)`, both results point to the original formal row `F`. This preserves direct Name references through chained application but may create SCC paths through inner uses that would not exist under option B.

### B. Stop at nested Apply owners

An Apply result owns the resolved Names of its immediate callee/argument fragment, but traversal stops at an inner Apply result owner. For `f(0)(0)`, only `R1 → F` is contributed; `R2` has no edge to `F`. This keeps each Apply's reference ownership local to its own source node but can separate an outer computation from a Name used to produce its callee.

## Affected work

Blocked scope: proving which resolved Names belong to an Apply fragment across nested Apply; emitting the approved edges; transporting them through extrusion and fresh use; consuming them for SCC qualification.

Independent authorized work: original Simple-sub constraint generation/propagation proofs and the Oracle effect-hygiene source/consumer lane.

Required answer: choose A or B for the stated chained Apply and, if the intended rule differs, give the exact recursive membership rule. Do not infer wrapper, Lambda, Block, or local-initializer rules from this answer unless explicitly stated.

Pending publication: keep this question directory unstaged and uncommitted until the questioning primary validates an explicitly approved local answer and integrates the matching question/draft/answer bundle.
