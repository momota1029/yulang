# Parent-backward plan for Yulang inference guarantees

Date: 2026-11-01
Status: active research direction; no theorem or semantic rule is newly adopted by this note.

## Decision and fixed objective

The active objective remains the original Yulang inference guarantees. The
original source domain, approved Simple-sub operations, and their quantifiers
stay fixed. Mathematical algorithm proofs come before the Rust simulation
relation. Call and contextual effects remain in scope wherever the original
rules put them; a proof model may not remove them to simplify induction.

The governing algorithm decision is
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5.
It fixes generation, accumulation, propagation, level-aware extrusion and
intrusion, and generalization as the algorithmic structure. It does not certify
their combined soundness, principality, termination, or Rust correspondence.

## Four original roots

The four proposition definitions in `Contracts.lean` remain uninstantiated for
the concrete original Yulang problem:

| Root | Exact obligation | State |
| --- | --- | --- |
| `InferenceSoundness` (line 128) | Supported source + generated constraints + a satisfying assignment imply an original source judgment and `sameScoped` under the same scope and assignment. | Open |
| `SourceScopedCoverage` (line 133) | An original source judgment and generated constraints admit a satisfying assignment with the same scoped witness. | Open |
| `PrincipalCoverage` (line 138) | One principal satisfying assignment covers every original source derivation through the original `instanceOf` relation. | Open; `principal` and `instanceOf` are explicit arguments. |
| `InferenceTermination` (line 152) | Every supported initial inference state is accessible under the actual `inferStep`. | Open |

No reviewed result in R184–R194 supplied a concrete `SourceProblem` instance or
removed an original root prerequisite. The current root count is **0/4 closed**.

## Backward dependency packages and counting rule

For progress reports, count these named packages, not Lean declaration counts:

1. A canonical mathematical source/inference model instantiating the original
   syntax, generated constraints, solution relation, scoped witness, and actual
   inference transitions.
2. The forward `InferenceSoundness` implication for that fixed model.
3. The reverse `SourceScopedCoverage` implication for that fixed model.
4. The additional principal object and all-derivations factorization required by
   `PrincipalCoverage`.
5. Well-foundedness of the actual inference-step relation required by
   `InferenceTermination`.

At this revision, **5/5 packages remain open** and **0/4 roots are closed**.
An accepted complete model would remove only package 1; it would not count as a
soundness, principality, or termination theorem. Count a package as removed only
when its stated original dependency is derived and independently reviewed.
Report new local lemmas separately, with the exact package/root edge they
discharge. No finite leaf-premise count is claimed until the fixed model has a
reviewed constructor-by-constructor obligation inventory.

Rust/source-native simulation is a separate later bridge. It is not one of the
five mathematical packages and cannot be used to discharge them.

## Evidence and current critical path

`Contracts.lean` is a parameterized interface, not a source interpretation.
`InferenceConstruction.lean` explicitly says that its imports do not instantiate
the full original `SourceProblem`. Genuine local results exist: lattice store
soundness proves structural store satisfaction under its hypotheses, and
generalization results transport a structural solution under boundedness and
anchor hypotheses. Neither establishes the original source judgment or its
independent admission facts.

`InferenceSoundness` does not mention `Core`, `coreJudgment`, or `elaborates`.
Therefore a CoreSyntax payload conversion is not presumed to be a necessary
soundness dependency. The model should use original source payload domains
directly (including `Nat` float payloads, `List Nat` byte payloads, and source
path strings) unless an authoritative original rule proves a Core carrier is
required. No truncation, modulo mapping, or new supported-source restriction is
permitted.

The open typed-Union question
`questions/2026-11-02-original-typed-union-rule/question.md` remains pending.
This plan does not choose a new Union rule or infer field equations. If a full
model reaches that boundary, preserve the original constructor and report the
exact missing authoritative law; do not silently omit the case or narrow the
source domain. Independent source-inference work may continue where it does not
depend on those equations.

## Ordered work

1. Construct the original-source-level mathematical model and derive the
   forward constraint-to-source judgment, retaining all source constructors,
   Call, all four function/effect ports, and the one shared scope/witness.
2. Prove reverse source coverage as a distinct direction.
3. Prove principality as its own factorization/order theorem, then prove
   termination with a well-founded measure over actual inference transitions.
4. Only after the mathematical contracts are stable, prove and implement the
   Rust-to-model simulation. Reuse established effect-hygiene theorems through
   their actual hypotheses; do not reopen them without a concrete mismatch.

Each checkpoint records before/after package counts, root count, the exact
original premise removed, the proof artifact and independent review. A stopped
or conditional result leaves the package open.
