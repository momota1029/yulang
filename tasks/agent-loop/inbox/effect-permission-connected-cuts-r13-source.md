# R13 source handoff — connected cuts and path interpretation

Sprint: `EFFECT-PERMISSION-CONNECTED-CUTS/20261029-r13`

## Frozen source inputs

- `crates/yu-solver/src/candidate_effect.rs`: SHA-256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`.
- `crates/yu-solver/src/lib.rs`: SHA-256 `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- R12 source handoff: SHA-256 `e270f74164f29816f5823687afc431617843b49ae7e28ffb06bc942d5a8e385b`.
- R12 accepted proof artifact: SHA-256 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.
- R11 source instance: SHA-256 `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91`.
- R9 source allocation: SHA-256 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`.

## Path type and stack behavior

`FormalPortStep` in `candidate_effect.rs:413` has exactly `Argument`, `Result`, and `Element(usize)`. `candidate_formal_annotation` (`1877–1920`) creates a new empty mutable `Vec<FormalPortStep>` for each annotation before recursively traversing its `SourceAnnotationType`. Thus the source path is rooted at that annotation; the inspected entry point does not supply an outer mutable path prefix.

Tuple recursion (`1640–1666`) saves `base = path.len()`, pushes `Element(index)`, passes the active stack to the child, then truncates to `base` before propagating a child error or collecting the pair. Function recursion (`1667–1687`) performs the same save/push/call/truncate sequence in order for `Argument`, `Result`, the argument effect port and the result effect port. Effect-port traversal receives the complete active path as a slice (`1694+`). These operations establish stack restoration order. They do not alone prove an adapter to the Lean `Retained.path` interpretation.

For negative concrete rows, `candidate_formal_effect_port` allocates a fresh effect row, copies the entire active stack into `retained_path` with `extend_from_slice` (`1734–1743`), copies concrete members, computes accounting, then pushes one local `FormalPermission` (`1764–1771`). The record retains `parameter`, `occurrence`, `source_owner`, `scope`, copied path, `source_row` and concrete members (`420–431`). The live effect term is created after this branch returns (`1770` in the containing routine). The enclosing formal annotation publishes the local vector later (`1940–1967`); publication is outside the 13 R11 cuts.

The Lean side defines `FormalPermissionCaptureConstruction.Step` as `argument`, `result`, `element Nat` and `Retained.path : List Step`. The constructors admit an evident shape-preserving candidate map, but the source code does not itself establish that every Rust annotation root is the exact Lean shape root or that R12's tree paths are the desired rebased paths. R13 must state and prove the prefix/rebase relation; it cannot infer it from list dropping or normalize from a target endpoint.

## Observed path identity and distinctions

The source regression assertion at `candidate_effect.rs:4269–4284` records distinct paths `[Argument, Argument, Result]` and `[Result, Result, Result]`, both with the same concrete family but different `source_row`; it also checks the same `parameter`, `occurrence`, `owner` and `scope`. This is evidence that equal concrete payloads do not authorize path or row merging. It is a read-only source fixture, not a proof of all executions.

R12 `TreeOperations` gives row-local paths for its retained entries (`FormalPermissionHelperFrames.lean`, `FunctionOperations.resultPort`, `innerTuple`, `rootTuple`). The missing R12 bridge is a complete relation between those relative paths and the full source traversal path. A valid R13 construction must retain the path prefix and use an explicit decomposition/recomposition proof. Sibling distinction must follow from the full path data, not equality of concrete members.

## Connected operation order and allocator boundary

R12 identifies thirteen cuts in source order: first function argument leaf, result leaf, omitted argument port, concrete result port, function completion; inner integer leaf; second function's same five cuts; inner tuple completion; root tuple completion. The four births are effect-row allocations; each `fresh_effect_at_level` (`lib.rs:10470+`) reserves and appends one item in each of `effect_bounds`, `effect_levels`, `effect_metadata`, and `extrusion_effect_marks`. The two negative concrete result ports append designated records to the local permission list only after their allocations/path/concrete copies/accounting; term construction follows each append. The order is described in R12's source handoff and must be preserved by a connected R13 trace.

The model must thread one `HelperState` across the thirteen cuts and make the two permission appends explicit mutations at their actual position. R12's `HelperOp` intentionally excludes those appends. Capacity reservations do not append rows. Four successful allocations, two permission records, all copies and completion behavior still depend on explicit success premises; this source handoff does not prove execution success.

## Unresolved boundary

The source establishes path constructors, annotation-local stack operations, copied full active paths, permission metadata, local append order and selected regression distinctions. It does not establish Rust successful-return linkage for any R12/R13 model program, all primitive/library alias behavior, all capacity/copy/arithmetic successes, native authenticity or graph publication correspondence. Keep those gates OPEN. No Rust files changed; no tests, Cargo, compiler or Lean commands were run in this source lane.
