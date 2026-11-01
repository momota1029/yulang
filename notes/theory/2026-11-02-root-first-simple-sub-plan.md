# Root-first Simple-sub proof plan

Status: research-plan revision; not a semantic decision, theorem, or closure
receipt.
Authority: user's 2026-11-02 direction to reconstruct dependencies from the
original parent theorems and separate abstract inference correctness from Rust
correspondence.

## Decision

The research order changes. The fixed target remains the original Yulang source
rules and the Authoritative Simple-sub algorithm. Rust identities, receipts,
owners, source occurrences, and runtime traces may later establish
implementation correspondence; they do not define the abstract algorithm or
its source typing rules.

No source meaning is adopted by this plan. Where the existing authorities do
not determine an equation, the model remains incomplete until the normal
independent-review and user-approval path resolves it. The original parent
statements, source domain, scopes, effects, and witnesses remain unchanged.

## Parent roots and required composition

The four roots remain those in `notes/theory/lean/YulangClosure/Contracts.lean`
and the reconstruction in
`notes/theory/2026-11-01-parent-obligation-reconstruction-r199.md`.

1. **InferenceSoundness**: for the same source `s`, scope `x`, generated
   constraint `d`, and independently satisfying solution `a`, derive an
   original source judgment and `sameScoped` with that same `a`. This is the
   first root. Its proof must consume the actual generation equations and
   show that each independent constraint-satisfaction premise yields the
   corresponding original source premise before calling source reconstruction.
2. **Principality**: separately construct a solution and prove its universal
   factorization under the original instance relation. Soundness does not
   imply this root.
3. **InferenceTermination**: separately prove accessibility for the actual
   inference transition relation. A finite successful-run soundness theorem
   does not imply this root.
4. **SourceScopedCoverage**: keep its original reverse-direction statement.
   It may later follow from a proved `PrincipalCoverage` plus its same-model
   corollary, but it is not closed before that corollary is proved and applied.

The composition boundary is explicit:

```text
fixed abstract types/effects and Simple-sub operations
  -> independent generation and satisfaction equations
  -> actual algorithm/run soundness for those equations
  -> each original source-rule premise under the same assignment and scope
  -> original source reconstruction
  -> unchanged InferenceSoundness
```

An algorithm theorem is useful only when its exact conclusion supplies a
premise in this chain. A conditional preservation lemma, symbolic source
compiler, or successful accepted run is not itself a reduction of an original
root.

## Model freeze gate

Before another proof packet is activated, freeze a constructor-by-constructor
mathematical model with these linked definitions:

- the original syntax, source judgments, scopes, declarations, annotations,
  literals, patterns, statements, Call, and effects;
- the abstract type and effect domains, including the approved Union and
  intersection behavior and all four Function ports;
- independent constraint generation and satisfaction, with source endpoint,
  scope, world, and witness correspondence;
- accumulation, propagation, level-based extrusion, value-reference-SCC
  intrusion, and generalization as operations of one mathematical algorithm;
- the actual initial state and transition relation used by a successful run;
- the readout and scope relation consumed by the original soundness root;
- the original principal order and instance relation, kept separate from
  soundness; and
- the exact existing theorem at every composition edge and each remaining
  premise owner.

Every constructor equation must be classified as either derived from existing
authority or unresolved. No equation may assume the source judgment or
admission fact that the parent theorem is meant to derive. The same model must
be consumed by generation, satisfaction, and readout; a parameter that can be
filled with the conclusion being proved is not an independent model.

The existing source syntax and structural Simple-sub algebra can be reused.
Existing local results can be reused only after their supplied histories,
decodings, guards, and readout premises are constructed from the fixed model
and actual run. Do not wrap those parameters in a new record and count that as
model completion.

### Known boundary classifications

- The user's approved rule for `if true { 1 } else { "str" }` requires both
  branches to contribute `int | str`. Structural Union and intersection
  behavior therefore remain in the abstract core.
- The open typed-Union question concerns selected source branch to dependent
  result-telescope transport for Call/incidence. It does not block the
  structural Union operator. Preserve the question and its source-domain
  obligations; do not make a core theorem depend on an answer it does not use.
- Literal L1 source meaning is fixed by the authoritative
  [adoption addendum](../design/2026-11-02-literal-l1-adoption.md): all raw
  payloads, intrinsic value/type, pure Return, original occurrence/root/event/
  scope/witness, and preservation of contextual effects and other checking
  alternatives. The missing equation is now specifically the independent
  Simple-sub generation and solution readout that reconstruct those facts at
  the same original coordinates. Do not count the adopted rule or the old
  `Build` literal rewrite as that bridge. Annotated literals still retain the
  original synthesis-to-written-target boundary and final-root readout.
- Call and contextual effects stay in the first soundness model wherever the
  approved algorithm makes them core. A source-adapter obligation may be
  staged later only after the abstract algorithm's relevant operation is
  already fixed and proved.

## Proof order

1. Freeze and independently review the abstract mathematical model and its
   source equations. If a required equation is open, report `MODEL-INCOMPLETE`
   with its exact original owner and do not start a theorem that assumes it.
2. Prove whole-run abstract solver soundness for the endogenous algorithm,
   deriving worklists, identities, levels, copy names, and intrusion
   qualifications from the run itself. Do not take arbitrary histories,
   certificates, or successful interpretations as input. State exactly which
   premise of `InferenceSoundness` this theorem supplies; otherwise report
   zero parent delta.
3. Compose the independently solved generated constraints into each original
   source constructor and apply the result to the unchanged
   `InferenceSoundness` root, retaining its same assignment, scope, and shared
   witness.
4. Prove principality and termination as separate roots against the fixed
   model. Do not infer either from soundness.
5. Complete remaining Call/contextual-effect source bridges that are outside
   the fixed core, without narrowing the source domain or weakening the roots.
6. Prove Rust implementation correspondence to the already fixed and proved
   mathematical algorithm. Rust correspondence is downstream of abstract
   correctness.

## Progress accounting and stop rule

The baseline is unchanged: **0/4 roots closed; 0/5 dependency packages
closed**. A root changes only when a reviewed theorem is applied to its
unchanged parent statement and all of that root's quantified cases remain
covered. For each report, record the exact parent premise before and after,
the proof that discharges it, the application site, the remaining premise and
owner, and both counts.

After two materially different proof methods leave the same premise unchanged,
inspect the owning mathematical definition and source rule before assigning
another local lemma. Do not use sprint count, Lean theorem count, Rust trace
count, or tests as a substitute for parent-premise reduction.

This plan supersedes the R209 next-action wording that treated typed Union as
an undifferentiated core model blocker. Literal L1 was adopted separately by
the 2026-11-02 addendum; this plan update records that source decision without
claiming the missing generation/readout bridge, changing other language rules,
or granting Rust production authority.
