# R152 implementation-owner handoff

Contract: R152 revision 1, SHA-256
`be08f5522b13b05a321448bd34d39dd6820a4644d843895a9b0612d70e296256`.
The frozen source note and inbox match the supplied hashes:

- `notes/theory/2026-10-20-types-console-initializer-certificate-r152.md`:
  `d8c0c77e136111f7c67ee80348d124fb557b5723fd684d582076671d1b491e9f`
- `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate-r152.md`:
  `cfe5cc416074cd3afc9f24aa6c45eeaffb0cbefe56b5a7f70505ac24d0c26dec`

## Source evidence boundary

The frozen source result is explicitly unreviewed and stops before completing
the declaration-to-name/body/shape/`DefId` joins for the actual ordinary
binding helpers. It also marks full constructor/generated-path coverage,
sample declaration census and composed order, specialization of all required
roots, and initializer-to-Request reachability UNKNOWN. Therefore it does not
establish a concrete end-to-end implementation slice or sample-specific
carrier contract. Preserve `NO_SAFE_CODE_SLICE` until the source result and
predecessor corrections receive CLEAN independent review and the missing
joins are closed.

The R152 correction is material to any carrier design: `connect_body` is not a
publication bit. Source evidence reports `ComputedDef` emission only for a
successful Let target with `BindingFetch::FetchComputation` and captured
publication enabled. The corrected OpDef route does not establish publication
from its literal `connect_body` argument. Projected destructuring can construct
a `Computation` component while the hidden reference is `Value`; those
classifications must not be merged. Header-wrapper classification is expressly
not fully audited. These are source-owner findings pending review, not
implementation authorization or a blanket classification rule.

## Pinned Y3 join re-evaluation

The contract-pinned Y3 owners match the R151 owner blobs already inspected for
the preceding handoff. Their boundary remains local-source oriented:

- `yu-hir` exposes `Binding`, `Expression`, and `Error` HIR items. A binding
  has an artifact-branded `DefinitionRootId`, `DefId`, visibility, parameters,
  value, and optional `EvaluationClass`. `SemanticImports` retains at most
  opaque caller evidence tied to one declaration in that parsed input; it is
  not an imported initializer declaration/classification/order record.
- Candidate source schedules are keyed by local `DefinitionRootId`; root
  actions run against that local schedule. This preserves local source
  ownership, but the pinned schedule has no imported declaration-qualified
  publication or ordered-root carrier.
- `RuntimeProgram::from_hir` traverses local HIR items, requires each binding
  or expression to have local source, emits code, indexes definitions by
  `DefId`, and retains source-order computation definitions and expressions.
  Definition computation is currently classified from emitted instruction
  shape. `ExecutionRoot::Definition` contains a `DefId`, whereas an expression
  root is joined to its authenticated root/code pair. The machine validates
  definition membership and duplicate/order entries against its local index,
  executes scheduled roots, and materializes value definitions on demand.

This establishes what the pinned local consumers can represent and validate;
it does not show that a missing imported root should enter through any
particular interface. Combined with the frozen but unreviewed source result,
the first safe conclusion is conditional: if independently reviewed source
joins identify imported initializer declarations that must be composed into
these consumers, an authenticated declaration identity, source owner/body,
publication classification, and order must survive HIR/candidate composition
and be validated by runtime. The present evidence does not determine that
contract, its constructor coverage, or the affected sample roots. No carrier
edit is authorized by this handoff.

## Gate and remaining dependencies

Keep `NO_SAFE_CODE_SLICE`. The source-to-Y3 boundary remains conditional on
independent review and the exact parsed-declaration joins, successful/error
branch coverage, suppression/publication ownership, generated-root cases, and
sample-to-specialization-to-Request evidence. Do not infer an empty root set,
missing sample reachability, or a universal classification from unresolved
joins. The frozen source inbox's `R152-DECLARATION-JOIN-1`,
`R152-CONSTRUCTOR-COVERAGE-1`, `R152-ROOT-CONSUMER-1`,
`R152-CARRIER-1`, and `R152-CORRECTION-1` TODOs remain prerequisites; they
grant no lease or authority.

This is a read-only implementation-owner handoff, not independent review.
No code, tests, builds, or executions were changed or run. No scratch paths
were created.
