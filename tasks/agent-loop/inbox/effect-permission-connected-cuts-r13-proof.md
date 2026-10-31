# R13 connected cuts — proof handoff revision 2

Sprint / contract: `EFFECT-PERMISSION-CONNECTED-CUTS/20261029-r13`, SHA-256 `3b723f1a4153af9217717bedcdb5ff1c06da569014219b00feef976057723a19`.
Worker: `/root/effect_permission_connected_cuts_r13_lean`; registered lean_prover leaf, no descendants. Requested/observed model and effort: UNKNOWN. Finite cap 600s. Outcome: constructed-but-unchecked conditional operation-model construction; independent review and kernel acceptance pending.

## Authority and source map

Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, the Lean skill and its source/execution references, compact current state/README, and the R13 contract/source handoff. Original claim: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1–3 (every supported original source program, lawful finite histories, retained extrusion occurrences, original source scopes and one joint witness). Correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Top-level principles remain authoritative. This operation model covers only the fixed R11 tree; it makes no smaller-language claim about the original parent.

Concrete source inspected: `candidate_effect.rs:413–431`, `1620–1790` (FormalPortStep, permission record, tuple/function push/truncate order, effect-port allocation/copy/accounting/append), and `lib.rs:10470+` (four vector row appends). R13 source handoff SHA `99614e24f70946b929bf6ec539244d58e111739e0dbc20ec9e7651fef7d144d7`; R12 source handoff SHA `e270f74164f29816f5823687afc431617843b49ae7e28ffb06bc942d5a8e385b`. Research drafts and source maps are not semantic authority.

Read exact Lean declarations: R12 HelperState/HelperOp/runOps/Call/Cut/FunctionOperations/TreeOperations/exact_tree_r9_from_operations; R11 localEntry/afterOne..afterFour/Reservations/exact_tree_r9_application; R9 Allocator.push; capture Step/Metadata/Retained; authenticated fixed-tree paths/rows/retained. Dependency pins were checked with sha256sum and match the assignment: R12 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`, R11 `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91`, R9 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`; Rust candidate_effect `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`, lib `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`. Input-manifest SHA `911ea88407dc079f56ee19914a2ab3be49654cc2182ee6a2adb0302cc5d8c880`.

## Construction and exact public roots

Module/namespace: `YulangClosure.FormalPermissionConnectedCuts`. Audit every following theorem with its printed type and #print axioms:

- `strip_recompose`: every prefix/relative path strips after recomposition.
- `recompose_strip`: every successful structural strip reconstructs the exact full path.
- `rebase_extend`, `extend_rebase`: full Retained record round trips in both directions.
- `rebase_identity`: the whole Metadata record (parameter, occurrence, owner, scope, source row, concrete operands) and allocatedRow survive path extension.
- `sibling_distinction`: siblings with unequal element indices remain unequal under any common prefix, with identical metadata, concrete operands and allocation identity permitted.
- `local_view_exact`: deterministic total read view agrees with relative records when the proved decomposition holds.
- `connected_allocators`: all thirteen cut allocators and final allocator are derived from one initial state and the same ordered chain.
- `exact_path_factors`: exact full/relative factorizations at all five nonempty local permission roots used by R12.
- `exact_tree_r9_from_connected`: same R12/R11 source derivation/output and R9 allocator application, universally quantified over source State, initial HelperState, level, length alignment, Aligned, Reservations and Calls.

`connect` uses each preceding cut's actual Call output to construct the next cut. Four explicit birth mutations call Allocator.push, each appending one item to all four vectors. The two prepareAppend segments allocate first, copy/account full retained records, append the designated permission, then execute port term calls. No permission append is represented as HelperOp/frame. Path entries are set from source traversal coordinates, independent of desired endpoint equalities. `treeOperations` derives every R12 Cut.initial as a view of this single connected trace; it accepts no independent initial states or desired endpoint equalities. Earlier sibling permissions are omitted only in the local read view; the full connected list retains their exact prefix and order. Exact path factors plus structural strip/extend lemmas justify rebasing; list dropping alone is not offered as the structural map.

Represented: thirteen fixed-tree cuts, Int/Unit leaves, function/tuple term transcripts, four omitted/concrete port allocations, two negative concrete appends, arbitrary preexisting permission prefix and helper fields. R12 opaque term/event/resource payloads remain opaque. Calls/handling are model input, not authenticated source observations. `setPath` records active paths; this is not a proof of successful Rust stack execution/truncation. Root source row is retained in inherited source inventory; no root allocation is invented.

Omitted/unresolved: Rust successful returns, all fallible reservations/copies/arithmetic and callbacks, alias/primitive authenticity, capacities and machine-size overflow, native identity/publication, arbitrary source trees/other constructors, consumer residual/effect hygiene, original soundness/principality/progress/termination and production. Reservations are explicit inherited successful-path premises, never established availability. No whole TreeFrames oracle or endpoint equalities are assumed. The same source output witness is passed to R12; no marginal witness splitting.

## Execution and resources

Read project files: leanprover/lean4:v4.35.0; Lake library YulangClosure, no external packages, project args -j1/-M1024. No Lean, Lake, checker, build, tests or Cargo command was executed by this worker, exactly as the primary-owned two-audit packet requires. Thus actual executable versions/exits/theorem printed types/transitive axiom results are NOT_RUN, not inferred from construction or old receipts. Primary owns all cache/generated outputs and audit scratch. Read-only pinned library lookup consulted `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/BasicAux.lean` and `TakeDrop.lean` / `Nat/TakeDrop.lean` for append cancellation and exact drop lemmas; no executable invoked. No failure log is suppressed; there is no checker receipt yet.

Exact changed paths: `notes/theory/lean/YulangClosure/FormalPermissionConnectedCuts.lean` and this handoff only. Scratch/generated outputs: none. No compiler/test/config/toolchain/manifests/shared status edits, Git mutations or contacts/children. Small bounded read/edit/hash shell processes only; CPU/RAM not measured. No claim of independent review or production authority.

## Parent application and stop receipt

Apply `exact_tree_r9_from_connected` to inherited length/alignment/Reservations and the chosen model Calls: the resulting SAME out satisfies SourcePair, exact output/entries/births/final source State and the inherited afterFour full-prefix result. The first remaining premise is actual Rust successful helper execution corresponding to these Calls, connected mutable state/path operations, reservations and primitive effects; owner Luna/source-to-execution lane. Falsifier: a successful pinned Rust helper execution whose actual order/path copies/row identity/write footprint cannot instantiate this connected trace, or an audit diagnostic invalidating a theorem. No such source-qualified counterexample is claimed.

Revision 2 is frozen for primary audit; worker writes STOPPED after the SHA receipts sent with this handoff. Any repair requires primary acknowledgement and a sequential new revision within the fixed budget. Parent remains OPEN. Independent review and two primary audit releases remain primary-owned.

## Revision 2 repair and retained failure evidence

Primary acknowledged revision 1 and reported Audit 1 build exit 1, with no theorem roots printed: reserved identifier `prefix` caused parser cascades from line 19; `local` was also suspect; connected_allocators had a conjunction proof incompatible with simplification to True. Within the same lease, revision 2 renames binders to `priorPath` and `relativePath`, and uses the simplification result directly with `<;> simp`. This is a diagnostic-driven parser/proof repair; theorem statements retain their quantifiers and meaning. The worker executed no Lean probes. Audit 2 and all printed theorem/axiom evidence remain primary-owned and pending. Previous frozen artifact SHA cc3cb443e6cb5e53c0cbfcdff4c03e71a52db065bb88e3358c872e683e47ee0a; previous handoff SHA 8db895c5f83e100c9229effcabe3ae572faba83278c0205efeb9cceeb7e1ac14. All worker writes STOPPED at revision 2 freeze.
