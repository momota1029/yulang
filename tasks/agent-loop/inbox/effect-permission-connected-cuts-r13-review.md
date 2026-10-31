# R13 independent review — revision 1

Sprint: `EFFECT-PERMISSION-CONNECTED-CUTS/20261029-r13`.
Reviewer: `/root/effect_permission_connected_cuts_r13_review`, fresh nonauthor compiler_referee leaf; no descendants. Requested/observed model and effort: UNKNOWN. Assignment cap: 250 seconds. Outcome: **PASS for the conditional connected operation model only**. BLOCKING findings: none. Major findings: none. Minor compiler-correctness findings: none.

## Authenticated snapshot and method

Read the artifact and direct declarations before reading the implementer's explanation. The explanation was subsequently checked as a claim, not used as evidence. Applied `yulang-lean-proofs` for proof auditing, with the packet's explicit prohibition on additional execution. Read root operating instructions, design authority, top-level inference principles, original preservation statement §1, birth-level correction §§2–6, and the frozen R13 contract. The original source scope and shared-witness requirements remain unchanged.

Verified actual bytes:

- New Lean artifact: `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`.
- Proof handoff revision 2: `c677e958bb6ef11af36f3a77e1b4f95c6980b9d762eba27a4bf1e1a504d31fb0`.
- Source handoff: `99614e24f70946b929bf6ec539244d58e111739e0dbc20ec9e7651fef7d144d7`.
- R12: `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`; R11: `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91`; R9: `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`.
- Rust `candidate_effect.rs`: `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`; `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- Audit 1 receipt: `aeef6fd5a782aeb05bc7f2d7e7d3c61199ec1996f3535f403b88e6bfe6b87020`. Audit 2 receipt: `19d627ea5de0f89cf3a8f51cb19d2927858283779845ea362e5369c7a563429a`.

Audit directory: `/tmp/yulang-effect-permission-connected-cuts-20261029-r13/`. Independently compared all 16 Audit 2 copied project files both to their recorded SHA-256 and to workspace bytes: all match. Independently checked stdout, stderr, status and resource hashes against Audit 2 receipt: all match. Audit 2 stdout SHA-256 is `be93a61cfcfa490c8f28289fe7f2c7accd172b59f0830380440be7346685c80d`.

Audit 1 is a retained failed build (exit 1, 13.08s, 798084 KiB peak RSS), with parser errors beginning at the former `prefix` binder and a conjunction proof mismatch. It printed no successful theorem inventory. Audit 2 is the successful revised artifact (exit 0, 16.33s, 977212 KiB peak RSS). Its raw output identifies Lean 4.35.0 and Lake 5.0.0-src+eb6cafb, builds the selected module/dependencies, then prints all 19 theorem types and complete transitive axiom inventories. I inspected those types and inventories; no additional Lean/Lake/checker/test/Cargo process was run.

## Cause, ownership and connectedness

The artifact addresses R12's actual model-level gap: independent `Cut.initial` choices. `connect` at lines 149–166 derives every next full HelperState from the previous call's `finish`, with the explicit intervening path/allocation/preparation operations. It does not accept thirteen states or solve for desired endpoints. Although the public `Trace` structure can describe arbitrary states, `treeOperations` only uses the result of `connect`; it accepts no arbitrary Trace. This distinction prevents the exposed structure from becoming an endpoint oracle.

The allocator sequence is exactly `a,a,afterOne,afterTwo,afterTwo,afterTwo,afterTwo,afterTwo,afterThree,afterFour,afterFour,afterFour,afterFour`, followed by `afterFour`. The four `birth` operations delegate to the inspected R9 `Allocator.push`, appending to bounds, levels, metadata and marks. The two permission mutations occur at c4 and c10, after their row births and concrete preparation and before their result-port completion calls. R12 `HelperOp` has no permission append; frames therefore never hide either designated mutation. Capacity writes remain separate from vector-content pushes.

The local views at lines 199–232 are derived from each connected state. They remove the initial permission prefix of length k; views belonging to the second child additionally remove the completed first sibling. This does not mutate the full connected list. Arbitrary existing permissions, including coincident metadata/paths, remain an exact ordered prefix. The two inserted entries retain ordinals n+1 and n+3. Final equality uses the same initial allocator and no chosen native initial ordinal.

## Paths, identity and sibling cases

`stripPath` compares constructors and element indices, not lengths alone. Both list decomposition directions and both full Retained round trips hold with their printed universal quantifiers; the reverse direction requires successful stripping. Record updates preserve all Metadata and allocatedRow fields. `sibling_distinction` needs only unequal indices and permits equal metadata, concrete operands and allocatedRow, so payload equality cannot collapse sibling identity.

`localEntryView` deliberately uses length dropping and is not a general validation function. For example, dropping the length of `[element 0]` from a path beginning `[element 1]` would lose that distinction. This is not a counterexample to the admitted fixed-tree result: all five nonempty retained suffix roots are explicitly factored by `exact_path_factors`, and `local_view_exact` proves dropping agrees with the relative entry on those decompositions. `treeOperations` constructs only these proven fixed cuts, discharging their exact permissions equalities from the chain. No endpoint equation is supplied to normalize the path. Empty suffixes introduce no path obligation; the root's empty path leaves the two full paths intact.

Direct Rust inspection agrees with the described traversal order: tuple child Element push/truncate; function argument/result values followed by argument/result effect ports; concrete allocation, full path/concrete copies, accounting, permission append, then two live effect term calls (`candidate_effect.rs:1640–1789`). `candidate_formal_annotation:1903–1920` creates an annotation-local path. The regression at 4269–4284 distinguishes equal concrete families by path and source row. `lib.rs:10488–10519` reserves four vectors before four pushes. These are source observations, not proof that arbitrary Calls instantiate a successful Rust execution. Arbitrary handling transcripts can change model paths and other fields; their source authenticity and actual stack restoration remain explicit external obligations.

## All 19 audited roots and axiom inventories

Exact full types are retained in authenticated `attempt-2/stdout.raw`; below, H means `YulangClosure.FormalPermissionHelperFrames` and C means `YulangClosure.FormalPermissionConnectedCuts`. Each listed declaration is printed as a theorem, with no omitted axiom inventory.

| Declaration | Quantifiers / essential premise and result | Complete axioms |
| --- | --- | --- |
| H.operation_preserves_allocator | Every op and state preserves entire allocator | none |
| H.operations_preserve_allocator | Every op list and state preserves entire allocator | none |
| H.nonempty_operations_frame | Every first op, rest, prefix and state yields its projected frame | none |
| H.reservation_projection | Every state/lane/capacity updates selected capacity and preserves allocator | propext |
| H.permission_append_delta | Every state/entry preserves bounds and appends exactly entry | none |
| H.concrete_port_prefix_delta | Arbitrary before/after transcripts preserve bounds and append exactly entry | none |
| H.ordered_concrete_port_delta | Every entry/capacities/backing/after/state has the ordered append delta | none |
| H.tree_frames_from_operations | Every State and TreeOperations supplies TreeFrames for that State | propext |
| H.exact_tree_r9_from_operations | Every state/allocator/level, length equality, Aligned, Reservations and operations supplies one out with SourcePair and all stated equalities | propext, Classical.choice, Quot.sound |
| C.strip_recompose | Every priorPath/relative strips their concatenation | propext |
| C.recompose_strip | Every priorPath/full/relative, successful strip implies exact concatenation | propext |
| C.rebase_extend | Every priorPath/entry, extension then rebase returns same full record | propext |
| C.extend_rebase | Every priorPath/full/relative, successful rebase implies extension equals full | propext |
| C.rebase_identity | Every priorPath/entry, extension preserves Metadata and allocatedRow | none |
| C.sibling_distinction | Every common priorPath/tail, unequal i/j and arbitrary shared Metadata/ordinal implies distinct extended entries | none |
| C.local_view_exact | Every priorPath/entry, local view of extension equals entry | propext |
| C.connected_allocators | Every Calls/initial/level has all 13 allocator observations and final equality from connect | propext |
| C.exact_path_factors | Every n has all five stated full-record factorizations | none |
| C.exact_tree_r9_from_connected | Every State/initial/level, length equality, Aligned, Reservations and Calls supplies the same-witness SourcePair/output/entries/births/state and full-prefix allocator conclusion | propext, Classical.choice, Quot.sound |

No sorryAx or nonwhitelisted axiom appears. Focused source inspection/search of R13 and its R12/R11/R9/direct decoder declarations found no admitted hole, project axiom or kernel-check bypass.

## Same-witness application and remaining gates

R13 lines 247–248 apply R12 `exact_tree_r9_from_operations` directly to the constructed TreeOperations. R12 applies R11 `exact_tree_r9_application`; R11 obtains `out, run` from its supplier and passes those exact witnesses to R9 `r5_source_allocation_instance`. R9 uses the decoder equality to identify that out. SourcePair, entries, births, final source state and prefix equality therefore concern one output, without independently selected marginal witnesses. R13's `connected_allocators` additionally identifies the connected final allocator with the same afterFour result; the theorem does not claim native execution.

The result is sufficient to close the admitted R13 conditional construction and structural path-map task. Actual Rust successful execution linkage to Calls and connected path/state transitions, reservation availability and machine arithmetic, primitive/library alias authenticity, native identity/publication, original parent, consumer residual/effect hygiene, soundness, principality, progress, termination and production remain **OPEN**. Minimum evidence for that next bridge is a source-qualified execution-to-model relation at the actual owning helper/callback paths, not another assertion of endpoint equality. This is an acknowledged remaining gate rather than a defect in the stated conditional result.

Only this leased review handoff was written. No source/artifact/audit/current/evidence edits, Git mutations, test execution or descendants. Review writes STOPPED at this revision; primary owns adjudication and integration.
