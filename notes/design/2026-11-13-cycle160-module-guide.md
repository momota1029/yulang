# Cycle160 module guide and proof boundary

All 19 modules are new. No candidate, Step, Stable or Evidence definition changes.
Full theorem names and quantified Lean types are recorded in
`notes/verification/dots-cycle-160-signatures.txt`; source hashes and public names
are in the adjacent inventory JSON. Public count: 200.

## General semantic transport (conditional soundness assistance)

- ActualSchema (11): every generated schema from actual-mode requests is
  ActualOnly, including terminal root requests. For every declaration, captures,
  old/current reports, schema inclusion, common model, old schema Models and
  Footprint (output equivalence, input Fits inclusion, historical origin cover),
  derive current schema Models. It preserves test existence/universal predicates,
  variable semantics, pair sharing and capture-origin sharing. Fits inclusion,
  not endpoint equivalence, is enough in actual mode. No point bounds assumed.
- ActualSchemaScope (11): prove scoped queries/schemas structurally through
  translation, normalization, app/row/list and generated folding. Declaration.Scoped
  plus singleton input names derives the binder-only hypothesis needed below.
- NonpointCollapse (2), NonpointBranch (3): for every existing depth-two Shape,
  declaration with the tracked binder as input, and model of old propagation,
  old merged Fits implies retained first Fits. Derive private-state Models and
  complete terminal BranchModels from old BranchModels and current source Models.
  Nonterminal request generation is excluded explicitly, not rejected by language.
- CollapseReadiness (5): the same Shape preserves argument locations, metadata,
  Finished and terminal generated requests/readiness. These are auxiliary facts,
  not existence of an operational revision.
- NonpointEvidence (2): transport old Instance/Evidence with explicit old witness,
  checked visible declaration, registry identity check, located root, shape/query,
  terminal/single-binder/scope, common model and current source Models.
- CheckedNonpointEvidence (4): derive scope from the declaration's Checked proof.
  The same old/current assignment is retained, not existentially replaced.
- CertifiedNonpointEvidence (2): Certified.exact plus old journal Models derives
  current source/journal Models; combine with the previous historical Evidence
  transport. Old Evidence remains a premise; universal historical recording for
  arbitrary reachable nodes is NOT proved.

## Renaming origins without requiring identical request IDs

- ActualSchemaOrigin (14): renameOrigin/renameSchema commute with request-generated
  schemas. For every assignment and rename with equivalent assigned source types at
  old/new IDs, derive actual Observes push/pull through nominal and structural
  paths. Full Models replay further needs actual-only variables, output equivalence,
  input Fits inclusion, current-to-historical capture-origin correspondence and
  old Models. These are atomic semantic premises, not assumed current Models.
  The actual allocator establishing those premises is still open.
- ActualSchemaOriginExample (5): two request IDs both map to 10, with nonempty
  schema and common model before/after. Renaming is noninjective; schemas literally
  differ. This is semantic retargeting, not an operational allocation theorem.

## Nonvacuity and restriction regressions

- NonpointExample (22), NonpointOutput (14): positive depth-two nonpoint leaf
  witnesses and nonempty named-output schema in one assignment.
- NonpointStrict (24), NonpointStrictOutput (15), NonpointStrictEvidence (9):
  retained leaf bounds bottom/int, discarded leaf int/int. Old merged Fits is
  strictly smaller. The former endpoint-equivalence premise is false; old/current
  BranchModels, Instance and Evidence still hold with one associated-output schema variable.
- NonpointModeBoundary (4): changing that schema's variable to lower mode yields
  an old valid schema and impossible current schema in this model. This refutes
  mode-blind widening, NOT the language or certified revision's soundness.
- NonpointCertified (18), NonpointCertifiedOutput (24): add initial ordinary
  source1≤source2 and source2≤source1. For ALL models of that source, prove the
  revision exact; derive Certified and Improves, actual Value Step, Reachable,
  SourceFormed and a concrete result journal model. Second module has the
  nonempty associated-output schema. No circular assumed Certified premise.
- NonpointOperationalEvidence (11): check the fixture registry; construct old and
  current Instance/Evidence in the same model. `reachable_nonempty_evidence`
  packages Checked, actual step, reachable, formed, result Models, one schema
  variable, and old/current leaf Evidence. It does NOT claim Stable, selected
  journal recording, output installation, final payload adequacy or universal
  Evidence for every model of every reachable Stable state.

These are soundness transport assistance, auxiliary semantic facts and positive/
negative regressions. No general completeness/principality theorem is closed.
The V5 remaining eight fields are unchanged.

## Next focused obligations

1. Derive origin/Fits premises from actual nonterminal emitted requests and child
   identity allocation, rather than a supplied renaming relation.
2. Generalize depth-two Shape to inspect/inspectMany simulation at arbitrary depth.
3. Derive old BranchModels/Evidence for every current journal model from genuine
   selected-node recording history; then discharge general evidenceNode.
