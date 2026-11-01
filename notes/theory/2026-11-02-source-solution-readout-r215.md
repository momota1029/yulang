# R215 — shared source/solution readout candidate

Status: **MODEL-INCOMPLETE; no theorem packet admitted.** This is a concrete candidate and stopping report for the unchanged original soundness root. It is not a source judgment, a `LocalLaws` instance, or parent-theorem closure.

## Original parent and measured progress

`Contracts.SourceProblem.InferenceSoundness` remains

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The three inputs must have independent meanings. The witness must be constructed from the very same generated constraints and satisfying assignment, preserving source scope, all binders/uses/futures and original contextual effects. R215 closes **0/4 roots and 0/5 packages**; it applies no premise to the parent.

## Candidate representation for one shared readout

The R214 countermodel rejects reading a variable as its arbitrary assigned upper graph node. A stronger candidate is to read a value/effect coordinate as its equivalence class under the actual regular-subtype preorder:

```text
x ≈ y  iff  RegularSub(x,y) ∧ RegularSub(y,x)
read(graph, refs, q) = [the graph node referenced by q]≈
```

This makes graph-node identity irrelevant. A source type readout may use the class rather than select one representative. The candidate still needs a proved `RegularSub` denotation for every actual graph/store solution and a faithful map from original source endpoints to `refs`; neither follows from the definition of `≈`.

For adopted L1, `PaperTypes.literalType` already maps all eight raw payload constructors to the adopted base types. A candidate generator for an intrinsic literal descriptor `q` is the pair

```text
atom(code (literalType l)) ≤ var(q)
var(q) ≤ atom(code (literalType l))
```

in the value sort. Under a regular-subtype readout, these clauses make the same assignment's `q` equivalent to the intrinsic literal base atom, so the R214 `.top` countermodel no longer satisfies the pair. The syntax supplies the exact literal value; this equation only reads its type. It does not yet construct the original `ValueRow`, Return row, event/root/scope witness, surrounding checks, or source subsumption. The effect coordinate equation for pure Return is also not established. The eight-type code must be injective and agree with the existing atom interpretation; no arbitrary direct graph-node equality is allowed.

For annotation hygiene, the selected source policy requires a resolved declaration tree keyed by the **same original annotation ID**, in the same formal owner/scope/event/witness. At each full child path, composed polarity classifies a resolved concrete row member as permission at a negative position or allowance at a positive position; symbolic row dependencies remain connected in the same valuation. Actual inflow is the effect term obtained from ordinary constraints. Residual is a filter of that actual inflow by a selected handler whose occurrence, owner, scope, annotation, path and concrete effect all match. Thus permission alone cannot create inflow, and unmatched `write` survives permission for `signal`.

This gives two concrete target equations under one readout: the literal's bidirectional intrinsic-type bounds, and the annotation declaration/profile plus its ordinary type/effect connections. They remain candidate equations until the full generator and readout are related.

## Exact obstruction in the pinned model

The current Lean surfaces do not define those equations:

- `OriginalSource.Annotation` is `Nat`; `OriginalSource.Source` retains the ID but has no resolved annotation declaration table. The original Lambda generator forwards that same ID into `sourceFormalRole` at the exact formal coordinates.
- `SimpleSub.Term` uses opaque `atom Nat`; `Store` contains only kind/lower/upper. It has no source occurrence, annotation owner, path or event field. `Lattice.StoreSatisfied` supplies structural regular-sub comparisons, not a declaration interpretation or endpoint map.
- `OriginalSourceInterpretation.SourceAssignment` contains arbitrary descriptor/value/root/event functions. `LiteralDeclaration` is supplied independently to `LiteralAtom`; `literalKernel` preserves the other original `Kernel` meanings. Its literal reconstruction theorem consumes this declaration relation and does not derive it from a Simple-sub assignment.
- The untracked R208 `StaticAnnotationConstraintInterpretation.lean` is not adopted. Its `GeneratedAnnotationClause` stores a resolved tree and `Solves` directly assumes the same annotation environment and owner/scope/event/witness. `Store.Satisfied` is only a conjunct; no annotation tree is generated from or denoted by the store, and no original `Kernel.atom` is derived. Its `SourceFormalRole` is a newly defined relation. This repeats the missing bridge in the premise.
- The actual Rust `SourceAnnotationType` contains useful grammar data, but an implementation carrier is not the independent source semantics or a Lean proof. The source typing manuscript expressly separates its source grammar from parser correspondence. No Rust change or receipt can discharge this mathematical equation.

Consequently `read` above cannot yet be instantiated with the original source `Descriptor`, and the annotation ID cannot yet be expanded into an authoritative tree inside the independent source model. Adding those mappings as theorem hypotheses, using `Kernel.atom`, or identifying `Store.Satisfied` with source satisfaction would only move the obligation. No theorem worker is admitted.

## Hygiene invariants retained

At every annotation position keep these separate:

1. **Permission:** resolved concrete members at composed negative positions.
2. **Allowance:** resolved concrete members at composed positive positions.
3. **Actual inflow:** what the same assignment's generated constraints establish.
4. **Residual:** actual inflow after a source-selected, coordinate-matching handler removes exactly what it handles.

Unknown symbolic variables and their connections remain live. A proof must include both Value and Computation entries, all nested Function ports and the original contextual Call effects. Existing residual filter lemmas can prove filter properties for supplied terminals only; they do not instantiate this source equation or Catch obligations.

## Verification and review boundary

Pinned Lean 4.35.0/Lake 5.0.0 was resolved without installation. `lake build YulangClosure.OriginalSourceGeneration YulangClosure.OriginalSourceInterpretation YulangClosure.SimpleSubLatticeInference` passed (18 jobs) using the user-authorized project cache at `notes/theory/lean/.lake/build`. This verifies those existing modules only. No new Lean declaration, theorem type, or axiom audit exists in R215; no Rust, Cargo or tests ran.

The frozen model is offered for independent review only as a candidate/stopping artifact. A reviewer must check (a) the two-sided literal candidate against the exact lattice semantics, (b) the claimed missing source-ID/constraint-denotation bridge against the pinned definitions, and (c) that the R208 draft is not accidentally treated as generation. Passing review will not close a root. The next parent-applying packet must supply the resolved declaration/type/effect equation and derive both L1 and `sourceFormalRole` from the same independently solved source package, or close a narrower original induction premise with a same-assignment application.
