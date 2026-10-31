# EFFECT-PERMISSION-AUTHENTICATED-SITE-EXPORT-20261028/r1 — proof handoff

Assignment `/root/effect_permission_source_transport_proof`; revision 2, final checked conditional freeze. Revision 1 SHA `0813fea4404eba40b91169f8950b0ba780a7fb47ae0dcefc0ba688748d78a9ca` is preserved at owned scratch `handoff-r1.md`. Contract SHA `4088b7dc1d357f1eb531d76ea01951630e8baf2b092856936c4e0a65f2ed77b9`. Requested role registered `lean_prover`; observed model/effort UNKNOWN. Sole author, no descendants. Exact writes: `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedSiteExport.lean` and this handoff; scratch only `/tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/lean-project/`. No compiler/Cargo/tests/Git/shared-state changes. ACK sent before construction.

## Original parent, source and corrections

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. Preserve every supported original source program, lawful finite Simple-sub history and actual retained extrusion occurrence, actual origin/receiver, polarity-specific pairs, scopes and one shared source-admissible strategy/witness. Typing, required principal coverage, soundness, ordinary progress and termination remain required. The 2026-10-24 immutable Value-birth-level induced-graph qualification replaces only the old cross-level SCC rule; it does not establish the source strategy premise. The effect-hygiene policy/corrections in `2026-10-10-annotation-effect-hygiene-integration.md` §§1–5 retain annotation permission independently from constraint-derived inflow/residual. `SourceProblem.InferenceSoundness` and companion roots in `Contracts.lean` remain proposition definitions, not proved concrete source instances.

Read the Lean skill/source/execution guides, root/base invariants, sprint contract, exact current review defect, original claim/corrections, concrete source constructors and the checked Lean definitions. No research draft supplies additional semantic authority. The prior restored/quarantined inbox was not accessed in this packet.

Concrete source mapping remains the actual `SourceAnnotationType`/`SourceAnnotationValue`/`SourceEffectRow` definitions in `crates/yu-hir/src/module/source_annotation.rs:125–162`. The immutable checked model `FormalPermissionSiteTraversal` contains every scalar/Variable/Hole, Function and ordered Tuple constructor, each node's optional row and full row data. This packet adds an independent source-node traversal that includes the root and every omitted/explicit row. Constructor visitation is exactly that traversal restricted to full paths ending in a Function Argument/Result edge.

Material root distinction: `candidate_formal_annotation` calls `candidate_formal_value_pair(annotation, &annotation.ty, …)` directly (intake lines 1863–1867). It does not call `candidate_formal_effect_port` on the root. Function construction calls the two immediate Effect ports after recursively constructing argument/result; Tuple recurses children; scalar leaves make no Effect-port call. Therefore an explicit root row is source DATA without a root port visit. A bare Tuple-element coordinate likewise does not create an Effect-port call. Nested Function ports below either kind remain included. The theorem states this distinction instead of silently discarding source root rows or fabricating constructor events. Event chronology and actual executing HIR extraction remain external obligations.

## Frozen definitions and exact theorem surface

New source SHA `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84`; namespace `YulangClosure.FormalPermissionAuthenticatedSiteExport`. Imports checked traversal `ac079ecc4c480adb4222723815b3f476469ed13b933c3994d090db0fae909207`, unchanged decoder `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f` and Native module `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1` transitively. Failed `FormalPermissionSourceTransport.lean` remains unaccepted, unchanged at `c737dc721df6c77506dc3176fd3863c5103573124f92dd51636037be8de625a7` and is not imported.

Ten authored theorem roots, universally quantified over their displayed parameters:

- `port_path_nonempty`: Function-port-ending paths exclude `[]`.
- `source_visit_lookup`: every concrete source-node traversal returns that exact optional row under concrete structural lookup.
- `source_visit_unique`: the same tree/full path has one optional row, including concrete operands/variables.
- `constructor_to_source`: every checked constructor visit is a source-node visit with a Function-port-ending path.
- `source_port_to_constructor`: every source-node visit with that path property is a constructor visit.
- `constructor_iff_source_port`: exact equivalence, quantifying the optional row.
- `omitted_port_iff`: specializes the equivalence to `none`, preserving omitted-row visits.
- `root_row_separation`: the actual optional root row is traversed by the source inventory and never a constructor Effect-port visit at `[]`.
- `bare_element_not_port`: `[.element index]` is not a Function-port-ending path.
- `extracted_port_and_export`: source traversal/path plus successful code decode and exact whole-list expected observations yield constructor visitation and accepted unchanged `decodeObserved`. These are supplied extraction equations, not proved native facts. This conjunction does not assert that the supplied tree/code/snapshot originate in one executing Rust input.

All ten theorem roots are now checker accepted under their full printed types, with the complete transitive axiom audit below. No native instance exists at this revision. The full model retains all original source constructors and optional/mixed/symbolic row DATA; semantic acceptance/preflight, nonempty tuple formation and actual encoding of HIR identities remain extraction duties. One model equivalence does not restrict the parent language or supply its shared source typing witness.

## Frozen audit inputs and completed single invocation

Project still pins Lean 4.35.0, `-j1 -M1024`, no external packages. Exact native Lake `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`; actual commands printed Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)` and Lean `4.35.0`, Linux x86_64 Release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; both version commands exited 0. Complete isolated source/config inventory `inputs-1.json` SHA `6fd6b30cbdea6e32afaf092f88dbed9fc4ba7d4552ff0c70e963c51dc5ec0272`. Expanded audit/input inventory `audit-inventory-1.json` SHA `88dc70319eaf149db594b794c35b6da21c1e51756417c792d626c917c0e5e4ed` includes every copied source/config, helper, contract, read-only native dependency hashes, exact argv/audit/runner hashes. No compiler inputs are executed by this check.

Exact argv `argv-1.json` SHA `e68af43613efafb81c05485e296fd2fd077828c34e4f977fc596470dfad28f87`; complete audit source `Audit-1.lean` SHA `b623cc5fe95f9939d36aadc56ff359a52ded49c9ccb9c3a44aa6db9e20e56e01`; runner `run-check-1.py` SHA `2c9c8ebb18d5592bbbe0533f797e21fc4a9c9eef631d9ff11e51a61aef05ed02`. Runner places helper temporary audit output under the contracted scratch via TMPDIR. Exact primary-released/executed command: `/usr/bin/time -v -o /tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/lean-project/check-1.time /usr/bin/timeout 60 /usr/bin/taskset -c 0 /usr/bin/python3 /tmp/yulang-effect-permission-authenticated-site-export-20261028-r1/lean-project/run-check-1.py`. Actual outer argv retained as `outer-argv-1.json`, SHA `68ca04481693d55a069455aad3de74b98e4c7d26a1fc23d0dcd725964cad7cb9`. Inner helper 55s; all ten roots selected. stdout/stderr/status/time separate. One of two permitted invocations spent, sharing 120s. Primary independently rechecked source/inventory/argv/audit/runner/external hashes and reported available memory 22,101,061,632 bytes before release. Exact released execution completed exit 0: nine-job focused build, theorem-declaration kind checks and all ten full type/transitive-axiom audits PASS. Outer elapsed 12.48s, user 6.24s, system 1.78s, max RSS 970236 KiB, swaps 0. No new warnings; one unchanged SourceOrigin unused-simp warning is retained. The helper generated/removed its temporary audit under the contracted scratch TMPDIR; complete planned audit source remains. No second invocation or retry ran; measured shared-wall remainder is 107.52s, requiring fresh primary release before use.

Complete printed types and every transitive axiom block are retained untruncated between YULANG_AUDIT_BEGIN/END markers in `check-1.stdout`. Axiom census for all delivered roots:

| Fully qualified namespace prefix: YulangClosure.FormalPermissionAuthenticatedSiteExport | Complete axioms |
| --- | --- |
| port_path_nonempty | propext |
| source_visit_lookup | propext |
| source_visit_unique | propext |
| constructor_to_source | none |
| source_port_to_constructor | none |
| constructor_iff_source_port | none |
| omitted_port_iff | none |
| root_row_separation | propext |
| bare_element_not_port | none |
| extracted_port_and_export | propext, Quot.sound |

No sorryAx, Classical.choice or project axiom appears. Static new-file scan found no sorry/admit/axiom declaration/checker bypass. The exact audited input inventory was rechecked after execution: zero project/external mismatches. Static scans supplement, rather than replace, the complete transitive audit.

Raw receipt SHA-256: `check-1.stdout` `498ef53c0f6a5fc808deb25b5b762fbd13b2a37918c1698b5c7319d88c52ca58`; empty `check-1.stderr` `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; `check-1.status` `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`; `check-1.time` `b2e08558232f24bae8eb186e80d1454459ece48964e1dcfb4d73d8bc27efc6a9`. No output stream was merged or material failure discarded.

## Parent application and first remaining premises

The checked equivalence removes the model mismatch between an all-node source inventory and Effect-port constructor visits, including explicit root rows and absent optional rows. It does not authenticate a snapshot obtained from the same actual solved HIR/action/constructor. Luna/Rust owns that first native premise, followed by exact source/context/row/occurrence/parameter/path extraction, delegated per-site positive/negative ordering, capture representatives/materialized nodes and owner/export port joins. Successful code decode, whole retained-entry correspondence and snapshot authenticity remain explicit; a supplied `observations` list is not native evidence. No fabricated IDs or identity/unequal instance is introduced.

TODO `AUTHENTICATED-SITE-EXTRACTION`: supply the actual executing constructor snapshot and its row inventory, classify root/non-port rows, preserve optional visits, join each origin/delegated site with exact Context/full path/both coordinates, and authenticate capture/export data. Falsifier: independently reparsed owner, root-row equality mistaken for root port call, shared enclosing position merging sibling sites, or fabricated q from exported output. Whole-source strategy/induction, A/B, native correspondence, hygiene, principality, termination and production remain OPEN.

State STOPPED; all writes stopped. Source/inputs/final handoff frozen. No active process, descendants or unaccounted generated-output lease. Independent review remains primary-owned. Outcome is a kernel-accepted conditional model correspondence; native extraction/authenticity and every original parent/production gate remain OPEN. A later native instance requires a frozen Rust receipt and new primary direction; none was fabricated here.
