# R10 proof handoff — revision 2, constructed and unchecked

## Authority, original claim and read scope

Leaf `/root/effect_permission_source_instance_r10_lean`; exact R10 packet; writes only the new module and this handoff. Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, rules/design-authority.md, the Lean skill and its source/execution references, R10 contract and manifest, the primary source handoff, actual R9/R5 definitions, local constructor/event definitions, project README/toolchain/lakefile/manifest, original source-preservation manuscript §§1–3 and the 2026-10-24 birth-level correction, and the authoritative inference top-level principles.

The original parent remains the universal supported-source preservation/principal-coverage/soundness/progress/termination claim in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, corrected by `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. This finite R5 supplier does not close that original claim or change its quantifiers/source domain. Current helper semantics remain conditional candidate transcription.

## Frozen inputs and artifact

- `tasks/agent-loop/sprints/effect-permission-source-instance-20261029-r10.md`: SHA256 `17198cecb75b2ab1500fb9da60c78028bae87e45b28a790d99e2797d9405a2ca`.
- `tasks/agent-loop/sprints/effect-permission-source-instance-20261029-r10-inputs.json`: SHA256 `48c9dacbb54d9be48930bde5656cfd13b8b9b55070719f9662fc043ea1aebadf`.
- `tasks/agent-loop/inbox/effect-permission-source-instance-r10-source.md`: SHA256 `3832ecde2cb0d2812bc74550ca6e0e9ee938a7ed526dd1712d00c69026379c37`.
- `notes/theory/lean/YulangClosure/FormalPermissionSourceAllocation.lean`: SHA256 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`.
- `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedNativeDecode.lean`: SHA256 `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`.

- Final module: `notes/theory/lean/YulangClosure/FormalPermissionSourceInstance.lean`; 14052 bytes; SHA256 `6638d59a39423c78e37052932a5b421932719fdeee939f94c7eec2e528467c8d`.
- Revision 1 was announced at SHA256 `3a239a01a7378c2399a92c7240a62bf841280d40b3cacdf3e8e360e9a3990ef2` (14012 bytes). Before the primary froze or released any audit, revision 2 explicitly unfolded `Annotation.effects` in the two tuple-guard proofs. No checker diagnostic was involved. Revision 1 was never audited.
- No imported/root/config/source/task-state files edited. No scratch/generated/cache outputs created by this leaf.

## Construction and exact premises

The allocator path is `a → afterOne → afterTwo → afterThree → afterFour`. All four operations push to the SAME successive four-vector allocator. `afterTwo` appends the first permission to that allocator; `afterFour` appends the second. `four_allocations_and_prefix` proves alignment at every cut, lengths n+1/n+2/n+3/n+4, and final permissions `a.permissions ++ R5.retained n`, with the arbitrary original prefix quantified in `a`.

`Reservations a level` has four `FreshReady` fields at those actual successive allocator states. These are never manufactured; all four u32/capacity availability conditions remain inputs. The private `freshStep` builds each actual `FreshStep` from its allocator, alignment and ready witness. Arithmetic transports its index to the corresponding source state.

`FunctionFrames` supplies five local frame obligations for each Function: its Int term, Unit term, omitted argument-port completion, concrete result-port completion and the function-term pair completion. `TreeFrames` adds the inner Int and the two tuple completions, for 13 local helper obligations. No `.nil` HelperFrames or default frame is constructed, no SourcePair is an input, and no pair-level frame oracle is introduced. Function/tuple frames are exactly the local premises already present in R9's corresponding constructors.

The port completion frames express only R9's projected equalities. They DO NOT establish actual Rust `try_reserve_exact`, `extend`, backing-byte accounting, graph availability or term-arena successful returns. Source owners are `candidate_effect.rs::candidate_formal_effect_port` (retained path/concrete copies, permission slot/byte checks, live-effect terms), `candidate_formal_value_pair` (atomic/function/tuple terms) and `lib.rs::fresh_effect_at_level`, `reserve_typed_route_lane!`, `reserve_f5b`, `positive_function_term`, `negative_function_term`, `with_term_events`. Supplying concrete successful native helper executions and proving they induce these finite local frame witnesses is the first remaining execution-correspondence bridge. No concrete permission capacities, byte bounds or success predicate has been invented to hide it.

`exact_tree_supplier` builds the exact guarded root Tuple with first Function, inner Tuple(Int, second Function), using argument value → result value → positive omitted argument port → negative concrete result port for each Function. The two result permissions carry source rows, context metadata and full paths. Root/bare tuple annotations remain represented and do not allocate an extra port. The outputs of private Function suppliers are shared directly with their following children; no independent output is selected for the R9 application.

`exact_tree_r9_application` passes that SAME `out` and `run` into `r5_source_allocation_instance`, retaining decoder equality, both local entries, all four births, final state, alignment and prefix. It asserts no actual native initial State or coordinate 21. Represented cases: exact Int/Unit/Function/nonempty-Tuple R5 tree, both tuple guards, all four ports. Other supported source constructors/error paths and enclosing annotation publication are outside this finite supplier and remain in the original parent domain.

## Complete public theorem statements

All four theorem names are in namespace `YulangClosure.FormalPermissionSourceInstance`. The module's public structures/definitions are construction data, not closure claims. Focused audit roots must include all four theorems below; private suppliers remain transitively kernel dependencies.

```lean
theorem push_aligned (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (a.push level)
```

```lean
theorem four_allocations_and_prefix (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (afterOne a level) ∧ Aligned (afterTwo a level) ∧
    Aligned (afterThree a level) ∧ Aligned (afterFour a level) ∧
    (afterOne a level).bounds.length = a.bounds.length + 1 ∧
    (afterTwo a level).bounds.length = a.bounds.length + 2 ∧
    (afterThree a level).bounds.length = a.bounds.length + 3 ∧
    (afterFour a level).bounds.length = a.bounds.length + 4 ∧
    (afterFour a level).permissions = a.permissions ++ FormalPermissionAuthenticatedNativeDecode.retained a.bounds.length
```

```lean
theorem exact_tree_supplier (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out
```

```lean
theorem exact_tree_r9_application (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour a level) ∧
      (afterFour a level).permissions = a.permissions ++ out.entries
```

## Actual commands, checking and resource disposition

This leaf ran read-only `cat`, `sed`, `rg`, `sha256sum`, `wc`, Python file/manifest inspection, and authored the two leased files with shell/Python writes. No Lean, Lake, elan, checker, tests, Cargo, instrumentation, dependency installation, nested CLI, Git or review commands ran. Project files inspected pin `leanprover/lean4:v4.35.0`, project `YulangClosure`, `-j1 -M1024`, zero external packages. Actual executable version was not queried under the packet's prohibition of uncounted Lean/Lake probes.

Therefore kernel acceptance, printed theorem types and complete axiom sets are PENDING, not claimed. There are no actual command exits or diagnostics for Lean in this leaf. The primary owns the isolated copied project, prospective frozen audit release, cache/generated outputs and every actual theorem/axiom receipt. Intended public roots: `push_aligned`, `four_allocations_and_prefix`, `exact_tree_supplier`, `exact_tree_r9_application` in the namespace above. No source holes, project axioms or bypasses were introduced.

Finite 600-second construction envelope observed; no execution allowance spent, no descendants. Final writes stopped after this handoff. The artifact is constructed-but-unchecked and is ready only for the primary's released audit and fresh independent review. Compiler/source-native/permission-copy-helper authenticity, parent effect hygiene, consumer residual, soundness, principality, termination and production gates remain OPEN.


## Revision 3 — amendment 01 continuation

Primary amendment `tasks/agent-loop/sprints/effect-permission-source-instance-20261029-r10-amendment-01.md`, SHA256 `9ebf619ca87730d0cb2b3f02ea947b6a6e7277a2dfe6e43a5ba98a05e407ac11`, grants this bounded repair. Revision 2 and audit 1 remain preserved by the primary; the revision-2 hashes and exact theorem statements above remain historical evidence.

Audit 1 failed: exit 1, 13.51 seconds, maximum RSS 798448 KiB. Raw stdout SHA256 `e5a2afbd2976a470c74d3261f96167959055ea019c2da06f302b07d70c919e8d`; stderr `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60`; status `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`; time `f784a46651ba226ed8c393fbc26d6c35a17e300bdd0541ba2b09917a05d99e48`. These are primary-authenticated amendment receipts, not executions performed by this leaf.

Only three proof conversion sites changed: add `Frame` to `simpa only` at the omitted-port frame transport, concrete-port frame transport, and inner-Int helper conversion (previous lines 98,116,175). All public theorem statements, constructors, indices, assumptions and source scope are byte-unchanged. No substantive dependent-index repair was attempted.

Final revision 3 module: 14073 bytes; SHA256 `4a25b24d251494ca6c05fcc696306cedf3d9cfa36d4a90a2a3437b68a04ff977`. This revision is constructed-but-unchecked pending the primary's second and final released audit. No Lean/Lake probes or audits ran in this continuation. Repair and freeze completed within the 30-second edit bound. All writes stopped after this appended handoff; all remaining execution-correspondence and original-parent premises above remain OPEN.
