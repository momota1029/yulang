# SELECTED-MODULE-ENTRY-AND-FRESHENING/r1 amendment01 — reconstruction handoff

Status: STOPPED / target UNCONSTRUCTED. H_u remains AUTHORITY_BLOCKED; native whole-branch reconstruction, original supplier, source/native, parent and production gates remain OPEN. The precise missing equation is stated below. No synthetic constructor, Phi-as-lookup, LocalLaws, generic supplier, or assumed reconstruction invariant was introduced.

## Assignment and runtime truth

Same registered proof identity `/root/effect_permission_module_materialization_r4_proof`; requested lean_prover / Sol-high; effective model/effort metadata UNKNOWN. Current-session active-work ACK was sent before resumed work. Original contract SHA `1091467e92e7231bc416190eb9c0727d39fadfdcafcbc78a2c1dcd4b26e40fb2`; amendment SHA `0e4c6e266723fc7795f9481fbea4f8466f1237e0a7eefefe8b466adec71310be`; original assignment bytes at this handoff SHA `1484ccc83bdfb0f4d1d70b4a6fd39a025d687575713904f0212b954846178260`. Each matched before its assignment body was used. This file replaces that leased assignment with its result; prior assignment hash retained here.

Original first captured clock `1793164771.8247478`; resume `1793165364.8423834`: minimum 593.018 seconds had elapsed, not 593 seconds remaining. Original 1,000-second grant stayed fully charged/reserved with no reset or refund. Nominal remainder at resume was at most406.982 seconds before startup uncertainty; I selected <=350 seconds continuation, with no new grant. Pause involved no writes or Lean/Lake invocation; only `elan which lake` read-only lookup. After amendment the sole verifier owned `.lake/build` and exact task scratch; no parallel build/cache writer was used. CPU/RSS not measured.

## Exact target and source distinction

Target: returned freshening lower equals independently reconstructed Phi_u of the captured Graph root under the same actual retained FreshUse maps, including all dependent fields/scopes/shared witnesses. The separate graph↔original whole branch allocation equation remains OPEN. The selected mathematical occurrence remains u_id in `my id x = x; my answer = id 0`; no session HIR identifier was reconstructed.

Source Generalize manuscript §5.2 requires one whole component frame, original fixed/Shared binders, actual event routing, dependent ViewLogic/EventProof scopes and one joint strategy. It explicitly says allocation is not a Pack/Decode or alpha-transport theorem. Original-generation §7.2(2) distinguishes transported final root mu_id(r_id) from registered ModuleContractRoot*, and marks that constructor unadopted. The amendment preserves H_u as authority-blocked; no source-owner conclusion was taken from provider coordinates or a successful native route.

## Exact native reduction — established by source inspection only

Pinned `crates/yu-solver/src/candidate_scheme.rs` SHA `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`:

- Graph, L188 onward: nodes, tuple/record/variant slices, rows, role/field-tail obligations, bounds/evidence, attachment/context data, root/live_root/boundary and region fields are separate operands.
- FreshUse, L593 onward: scope_remap, scoped_relations, context_use, rows, obligation-row indices, terms, effect_operands, bundle/context/evidence remaps are retained independently. `FreshUse::into_retained_parts` moves the exact terms and dependent maps without recomputing them.
- `freshen_candidate_graph_retained`, L4242–4258: returns the core's `(root,fresh)` unchanged on success, adding fallible scratch accounting. No Phi is constructed there.
- `freshen_candidate_graph_core`, L4260–4285: obtains fresh from preparation, restores every bound using borrowed fresh, then sets `root = fresh.terms[graph.root].ok_or_else(exhausted)?` and returns `(root,fresh)`.
- `prepare_candidate_fresh_use`, L4286–4669: computes row images using canonical-row memoization and the local/level/non_generic guard; copies scope/input identities; remaps effect operands and context views; reconstructs structural nodes by a worklist; constructs scoped relation and evidence maps.

Therefore successful source control flow reduces returnedLower to the retained `terms[graph.root]` read. This is a native readout equation, not a Lean theorem or an independent graph reconstruction. Defining Phi_u(g.root) to mean that same read would assume the requested theorem's content.

The actual structural reconstruction cases include Leaf (all native atoms), Row (Value/Effect with polarity), Function (four ordered ports), Tuple, Record with complete fields, and Variant with tags/payload lists. EffectOperand nodes are deliberately skipped in the terms vector and reconstructed in the separate effect_operands map; Allowance/Support/AnnotationMember tails use mapped Effect rows, Contribution is rebuilt from its effect/origin through the actual constructor. Scoped relations separately remap transformer/input/output scope and negative-formal demand roots; evidence snapshots and contexts have their own maps. A term-vector theorem cannot silently discard these fields.

## First unsupported mathematical/native equation

For the prepared captured graph G and actual retained maps M, the missing relation is:

`for every represented graph node i, independently interpret/reconstruct G.nodes[i] using M's row/effect/scope/context/evidence maps and the actual interner, and relate its native term result to M.terms[i] (or M.effect_operands[i] for EffectOperand), with consistent shared/dependent operands`.

Its root instance must then prove `independentPhi_u(G.root,M) = returnedLower`. No inspected Lean declaration states the complete Rust Graph/FreshUse relation, the successful worklist invariant that establishes every node image, or its preservation through bound restoration. A bare successful Option lookup supplies no such invariant. Structural DAG validity, child/slice alignment, interner readback and the separate effect operand/scoped/evidence image laws must be grounded at their actual constructors, not assumed as a generic interface.

Owner: native graph capture/preparation/FreshUse reconstruction and term interner correspondence, coordinated by primary. The next discriminating proof needs an admitted complete native Graph/Node/FreshUse representation and successful prepare-loop simulation, or a source-grounded existing theorem at exactly that type. It cannot be replaced by the smaller capture Shape model or a postulated Phi equation. No global nonexistence claim about every project file is made; this is the boundary of the inspected dependency cone.

## Existing Lean results checked; applicability limits

`FormalPermissionCaptureConstruction.Shape` has atom/function/tuple only; its `Node` has function/tuple/row/other, with opaque effects mapped to other. Its header explicitly leaves actual source/live capture coverage OPEN. `FormalPermissionLiveCapture.constructed_export_renamed` states a port-number correspondence and explicitly leaves the Rust live stored-node/walk simulation OPEN. These definitions cannot supply this target's Record/Variant/effect-operand/context/evidence reconstruction by restricting the language.

`NativeFreshScopeTransport` formalizes the successful overwrite-or-identity ID projection of native scope/input copying. Rust `candidate_source.rs` ScopeRemap L189–215 and ScopeInventory::fresh L296–342 show the corresponding distinct maps, append counters and per-key inserts. The two freshly checked existing theorems below are legitimate local reuse evidence, not newly constructed theorem bodies or concrete native/source instances.

Exact printed types:

```lean
YulangClosure.NativeFreshScopeTransport.fresh_evaluate :
  ∀ (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
    (transformer : YulangClosure.NativeScopeTransformer.Transformer)
    (state : YulangClosure.NativeScopeTransformer.State),
    YulangClosure.NativeFreshScopeTransport.TransformerValid scopeCount tagCount transformer →
    YulangClosure.NativeFreshScopeTransport.StateValid scopeCount tagCount state →
    let scopes := (YulangClosure.NativeFreshScopeTransport.fresh scopeCount scopeKeys).remap;
    let tags := (YulangClosure.NativeFreshScopeTransport.fresh tagCount tagKeys).remap;
    YulangClosure.NativeScopeTransformer.Equivalent
      ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
      ((transformer.evaluate state).rename scopes tags)

YulangClosure.NativeFreshScopeTransport.fresh_untouched :
  ∀ (count : Nat) (keys : List Nat) (old : Nat),
    ¬old ∈ keys → (YulangClosure.NativeFreshScopeTransport.fresh count keys).remap old = old
```

Complete transitive axiom results: fresh_evaluate `[propext, Quot.sound]`; fresh_untouched `[propext]`. Checker confirmed each is a theorem declaration, printed each complete type and every axiom list, and accepted only its standard whitelist. No project axiom, sorryAx or native-evaluation axiom appears in those audited cones.

Applied to the parent: fresh_evaluate can handle the scope-transformer evaluation subprojection once the actual old native state and transformer satisfy its explicit bounded-inventory predicates; fresh_untouched preserves a shared old ID absent from copied keys. Neither identifies the actual Rust inventory with a source telescope, proves absence of a source Shared witness from copied keys, relates a Graph Node to retained terms, or proves whole Phi_u. Those are explicit remaining premises, not hidden in the audit's axiom lists. No wrapper theorem was added merely to repackage these existing statements.

## Actual commands, versions and checker receipt

Installed-native lookup from project: `elan which lake`, exit0, path `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.

Native `lake --version` and `lake env lean --version`, both exit0: Lake `5.0.0-src+eb6cafb` (Lean4.35.0); Lean `4.35.0`, x86_64-unknown-linux-gnu, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Project toolchain/manifest/lakefile were read; no packages or toolchain changes.

Exact bounded checker command from repository root:

```sh
TMPDIR=/home/momota1029/rust/yulang/notes/theory/lean/.task-tmp-selected-module-freshening-r1 python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.NativeFreshScopeTransport --theorem YulangClosure.NativeFreshScopeTransport.fresh_evaluate --theorem YulangClosure.NativeFreshScopeTransport.fresh_untouched --timeout 60 > notes/theory/lean/.task-tmp-selected-module-freshening-r1/scope-audit.log 2>&1
```

Exit0. Helper ran native Lake `--version`, `--no-cache env lean --version`, `--no-cache build +YulangClosure.NativeFreshScopeTransport` (3 jobs, NativeScopeTransformer4.2s and NativeFreshScopeTransport506ms), and a temporary audit with `--no-cache env lean -j1 -M1024 --root=<leased scratch>/yulang-lean-audit-7x9fgju9 <same>/YulangProofAudit.lean`; every exit0. Complete raw log preserved in exact scratch. Helper removed its disposable temporary audit directory on completion. No build/test retry or full default build was run.

Material inspection limitation: broad initial declaration searches and one multi-file static capture were truncated. They were not used as complete semantic evidence; decisive scoped-map/capture definitions, full native preparation region and source §5.2/§7.2 were reread directly. No failed Lean build/audit occurred; no failure log was replaced.

## Dependency snapshot

The following includes focused inspected source/Lean files and tool/config inputs. Earlier typed-entry static inspection files are retained in the census as inspected inputs, but their generic/conditional source judgments were not used to construct the superseded H_u target. Search-only locator matches are not semantic dependencies.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/selected-module-entry-freshening-20261028-r1.md` | `1091467e92e7231bc416190eb9c0727d39fadfdcafcbc78a2c1dcd4b26e40fb2` |
| `tasks/agent-loop/sprints/selected-module-entry-freshening-20261028-r1-amendment-01.md` | `0e4c6e266723fc7795f9481fbea4f8466f1237e0a7eefefe8b466adec71310be` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-17-ordinary-call-original-generation.md` | `bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab` |
| `notes/theory/2026-10-17-module-source-handle-introduction.md` | `df0e684bad2da05741e39db12bd06bb400ad8b5b15af4116abab4df6c9df06c3` |
| `crates/yu-solver/src/candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean` | `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c` |
| `notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean` | `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e` |
| `notes/theory/lean/YulangClosure/FormalPermissionDefinitionCallBridge.lean` | `cb582e65901d81429a0856e10b8b9223c736bcb148783393e1da270b5f597f4c` |
| `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean` | `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `notes/theory/lean/YulangClosure/OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/README.md` | `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3` |
| `.agents/skills/yulang-lean-proofs/SKILL.md` | `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7` |
| `.agents/skills/yulang-lean-proofs/references/sources.md` | `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` |
| `.agents/skills/yulang-lean-proofs/references/execution.md` | `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b` |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` |
| `notes/theory/lean/.task-tmp-selected-module-freshening-r1/scope-audit.log` | `5068a14e84bb1e9a6a820d4eaa98f24eeacaa8bdd0cefa87018f175b89066c95` |

## Output and closure boundary

No new `FormalPermissionFresheningReconstruction.lean` file or theorem was created: the exact missing native Node/FreshUse semantics would otherwise have been invented. The old SelectedModuleEntry/FresheningImage/handoff leases received no writes and remain untouched. This fresh handoff is the only durable research result; audit log/dependency census are in the exact leased scratch, and Lake generated only its sole leased build cache.

No Rust edits, quarantined runtime reads, Cargo/tests, Git/central-state edits, extra descendants, source-domain changes, new axioms, sorry/admit or checker bypass. Represented in the actual native inspection: all Graph structural cases and separate remap fields above. Kernel-checked evidence: only the two existing scope-ID theorems under their printed hypotheses. Independent review/source-native correspondence/production authority are not inferred from that acceptance.

First parent remainder: independently establish complete native reconstruction relation at prepare_candidate_fresh_use, then identify the captured graph with the original whole branch allocation under its actual source map; H_u remains AUTHORITY_BLOCKED. Both original supplier obligations and all all-source A/B, complete Call/effect-hygiene, shared-witness and production gates remain OPEN. Writes stop after this handoff freeze.

Final write clock `1793165646.9950364`; continuation measured lower bound `282.1526529788971` seconds, original-assignment lower bound `875.1702885627747` seconds, each plus uninstrumented initial startup. Exact total UNKNOWN. No grant reset/refund; 1,000 seconds charged.
