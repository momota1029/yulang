# R90 proof handoff — original App and static registration

Assignment `/root/r90_registration_proof`; revision 2; **constructed; primary call 1 failed in flattened dependency assembly; call 2 pending fresh primary authorization**. Admission commit supplied by primary: `5db8a53f5`; source baseline `f16ed566d66f5574998ac9c3d2d62b5f46bc0fe5`. Contract revision 1 SHA-256 `6d02d47f3f3f09313ddf1ce12b92212aba968bfe502494c97e8414ba23fb2c6d`; 48-entry input manifest revision 1 SHA-256 `486f9825b4bb00ce4bc8931112be725dd11b17d701c4ebb4806fbfea8b8c3aa3`. Read-only byte/hash validation matched **48/48** entries. No dependency changed by this leaf.

## Frozen source and declarations

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, 7, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. Qualification correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`. The parent ranges over every supported original program, lawful finite history and retained qualified occurrence, preserving original typing/principal coverage, all source scopes, fixed providers/captures/whole arguments, one joint strategy, recursive monomorphic sharing, lawful independent-use allocation and complete Call/effects. Current qualification uses the immutable-birth induced graph, not cross-level paths. A local generic inversion does not prove A/B.

Selected semantic sources: `notes/design/2026-10-08-source-generalize-definition.md` §§2–3 selects construction §§3–5; `notes/design/2026-10-08-call-source-interface-definition.md` §§2–4 selects IF-Insert/IF-Use and complete static Call construction §§3–6; `notes/design/2026-10-07-complete-call-contribution-definition.md` §§2–3 retains authentic complete SpecCall and independent complete C0. In `notes/theory/2026-10-08-call-source-interface-construction.md` §2 a printed Gen-Call-0 tuple explicitly does not replace its actual children/formation; §§3.2 and 6 construct contextual slots at actual registered declarations/references. `notes/theory/2026-10-08-source-signature-incidence-construction.md` §§3–4 distinguishes typed support from original licenses. Research drafts add no semantic authority.

Exact existing Lean definitions inspected: `OriginalSource.Mark` (both site and annotation), `sourceRules` App equation, `singletonFormalCall`, `Environment.extend`, `Kernel`, `Judgment`, `Local`, `SourceJudgment`; `SourceSignatureConstruction.Node`, `Catalogue`, `Introduction`, `Graph`, `PortProv`, `Occurrence`, `contextual`, `insert`, `routeAction`, `LeafLicensedField`, `insertField`, `StaticCallIncidence`, `CallRegions`, `installCall`, `installed_call_node`, `raw_call_static_incidence`. All are under `YulangClosure`. No definition is changed and no concrete Kernel instance is asserted.

The leased artifact is `notes/theory/lean/YulangClosure/SourceRegistrationAppBridgeR90.lean`, **11,964 bytes**, SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`. All four R89 theorem statement texts through `:= by` are byte-identical under the new namespace/helper resolution; read-only Python comparison returned True four times. Their fully qualified names are:

- `YulangClosure.SourceRegistrationAppBridgeR90.app_rule`: every Mark/context/raw callee/argument; original App builder equals its complete existential core, wrapped in exactly the original annotation premises when written.
- `YulangClosure.SourceRegistrationAppBridgeR90.app_witness_scope_fields`: every Value/environment/site/witness; ViewLogic extension preserves every original field and appends exactly the original incoming-event frame.
- `YulangClosure.SourceRegistrationAppBridgeR90.app_core_iff`: every local Kernel/environment/site/context/operand pair; one admitted witness simultaneously supplies all original local clauses and both original child derivations in its same extension.
- `YulangClosure.SourceRegistrationAppBridgeR90.app_derivation_iff`: every local Kernel/environment/Mark/context/operand pair; original annotation obligations in the incoming environment plus that single complete witness package iff the original App derivation.

Repair: `app_rule` first uses `rcases mark with ⟨site, annotation⟩`, then eliminates that annotation, simplifies the actual `sourceRules` equation, and reduces by reflexivity. The whole original record is eliminated before annotation cases; no projection-only split remains in this proof. `app_derivation_iff` retains its already elaborating structure after applying `app_rule`.

Two additional applications have no whole-interface adequacy premise:

- `YulangClosure.SourceRegistrationAppBridgeR90.installed_call_app_atom`: for arbitrary Joint/graph/context/Mark/operands, all original CallRegions/local introductions/result catalogue, the exact sourceCallIncidence atom is in the unchanged App premise list and actual installCall constructs its static incidence. It does not assert Kernel.atom for that atom or its adjacent completeCallCertificate.
- `YulangClosure.SourceRegistrationAppBridgeR90.reference_insertion_whole_action`: given an actual reference-node lookup and a constructor-derived original Occurrence, IF-Use then IF-Insert preserves that introduction/owner, sets the receiver to its original registration, retains inherited classification, and applies that reference's original whole substitution exactly once before the remaining route. The same arbitrary Joint is used throughout; no provider/evidence coordinate is reselected.

All six theorem declarations request `#check @...` and complete `#print axioms ...`; all three helpers request `#print`. These directives are requests for evidence, not receipts.

## Coverage and first remaining parent premise

Represented: arbitrary original raw operands (all nested source forms), original contexts/environments, none/some annotations, both singleton-formal outcomes, all five base App atoms plus the conditional formal atom, both Value/Computation checks, both source children under one ViewLogic witness; every environment field; six Call regions and arbitrary complete arm lists; arbitrary dependent catalogue/packet/License types; cyclic finite registered graphs, actual reference routes and whole substitutions. No original source constructor is rejected or removed. Static graph arguments are not execution observations or a finite enumeration of semantic providers.

Omitted proofs: concrete independent primitive/operator licenses, original full App Kernel instance, complete Call C0/SpecCall/Gen-Call-0, native-source incidence, authentic providers/receipt/current/future/world coordinates, effect-hygiene transport, publication/lawful-use strategy transport and joint equality lift. These remain original obligations, not restrictions on the parent domain. A LeafLicensedField parameter would assume an existing license; this artifact deliberately does not promote one to composite applicability.

Application to parent §5: `app_derivation_iff` can invert an actual original App derivation without splitting its witness, and `app_witness_scope_fields` fixes its Shared/publication/event context. `installed_call_app_atom` identifies only its exact static sourceCallIncidence clause at those same raw source operands. `reference_insertion_whole_action` supplies the actual static origin/action equation under an authentic reference lookup. None constructs the semantic local premises needed to invoke the reverse direction of app_derivation_iff.

**First remaining premise:** construct the original whole registered formal/interface and actual complete Gen-Call-0/Call formation at the same App/environment/witness, then establish the native-demand/pair equation there. R89's frozen source result (`tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-source.md`, SHA-256 `74d5815c3d502ed2da2b1b50bf7edb6378f6d773fe2e6190efc6e2e335db5539`) lacks that supplier. Owner: primary's R90 source/implementation lane at `candidate_source` registration/initialization, `candidate_call` authentication and `candidate_scheme::install_candidate_local_term` / `route_candidate_local`. Actual descriptor/body/output/future/complete alternative and original effect/receipt evidence must be retained together; endpoint identity or typed static support cannot create them. Source result remains independently owned; this proof handoff does not invent its conclusion. Once that supplier exists, the original source-scoped simultaneous strategy/equality lift and lawful allocation remain next, owned by the parent proof lane. A/B, full source/native correspondence and production remain OPEN.

## Call-1 primary verification input (historical failed assembly)

Pinned configuration reread: `leanprover/lean4:v4.35.0`; library YulangClosure; `-j1 -M1024`; no external packages. Execution/cache/generated ownership remains with `/root`. Primary confirmed that the two direct calls are primary-owned. This leaf invokes no Lean/Lake/elan, builds or tests. The skill checker is inapplicable to this narrower contract because it builds and writes audit scratch; the approved substitute is in-memory flattened direct input, unchanged kernel checking and explicit complete axiom queries.

Dependency-first paths and hashes:

| Path under `notes/theory/lean/YulangClosure/` | Bytes | SHA-256 |
| --- | ---: | --- |
| OriginalSourceSyntax.lean | 22040 | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration.lean | 66485 | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| SourceSignatureConstruction.lean | 37437 | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |
| SourceRegistrationAppBridgeR90.lean | 11964 | `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a` |

Exact assembly: for each file in table order, read bytes; form `b''.join(line for line in data.splitlines(keepends=True) if not line.startswith(b'import YulangClosure.'))`; concatenate the four resulting byte strings with `b'\n'.join(parts)`. Retain `import Std`. No intermediate file is written. Result: **137,750 bytes**, SHA-256 **`c43394385c4bec30c0ca35077d2ae7f0308ece6a7a26305ed2665d9f3a46fe1b`**.

Primary command after exact review/authorization: pinned native `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, complete in-memory bytes on stdin, hard timeout 120 seconds; capture complete stdout/stderr, exit, actual version/executable hash and resources in the primary-owned verification receipt. No Lake/build/cache/scratch/test/environment output. This leaf has run **0 Lean calls**. The primary subsequently executed call 1; its actual receipt and repair follow below. The first assembly is retained as failure evidence and is not the proposed call-2 input.

Material prior failure evidence remains in `tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-review.md`: call 1 failed at the old map helper and annotation equation; call 2 (helper fixed) failed only app_rule's projection reduction. Both exited 1; app_rule and app_derivation_iff had error-recovery sorryAx, hence were unaccepted. app_witness_scope_fields printed `[propext]`; app_core_iff printed `[propext, Classical.choice, Quot.sound]`. These are R89 observations, not R90 results. No failed artifact is imported.

Actual leaf checks: bounded cat/sed/rg source/definition reads; Python 48/48 manifest hashes; four unchanged statement comparisons; six-declaration census; comment-stripped lexical scan found no sorry/admit/project-axiom/unsafe/native_decide/kernel-bypass token. All returned exit 0, no timeout. Lexical absence is not a transitive axiom audit. No compiler or source experiment, external/network call, installation, Git mutation, child, scratch/cache/build, /tmp or other output occurred.

Only writes: the leased Lean artifact and this handoff. Resource bound: 1,400 seconds; one reasoning lane, lightweight reads and in-memory checks only; no measured CPU/RSS receipt. No self-review/certification. Lean bytes are frozen pending primary execution; handoff may receive actual diagnostics and one sequential repair within the same two-call cap. Writes to the Lean file are currently stopped.


## Actual primary call-1 failure and assembly-only repair

The primary supplied the following exact receipt by message and the primary-owned review file, read at SHA-256 `51b2c15f1aae548687d86d132582ae8c7abe9d60fd49cf4b46dce32afd7c1951`. The copied receipt is preserved verbatim below. Complete 39,307-byte stdout was emitted in the primary's execution transcript; it is **not stored in the review file or available as bytes to this leaf**. Its digest, failed locations, complete per-declaration axiom lists and absent final declaration are preserved; no fabricated complete log is substituted.

## Primary Lean audit receipt — call 1 of at most 2

- Input: 137,750 bytes; SHA-256 `c43394385c4bec30c0ca35077d2ae7f0308ece6a7a26305ed2665d9f3a46fe1b`; executable SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Args: `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Result: exit **1**, timeout **false**, elapsed **11.336706s**.
- Stdout: **39,307 bytes**, SHA-256 `0a951e21fa2f9150084c8e5e09496c6ae0f22b449f50a6da89a925ff5e511075`.
- Stderr: **0 bytes**, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### Failure classification

The concatenated source did not preserve module privacy for `OriginalSourceGeneration.private def node`. In the single stdin module, this private helper collided with auto-implicit `node` binders in `SourceSignatureConstruction`. The first diagnostics occur at `<stdin>:1922`–`1939`: `PortProv`/`Developed` constructor arguments resolve to the private `node` function, then `node.introductions` and the graph-local node fields fail. This cascades into unknown `Occurrence`, `PortProv`, `Developed`, `SupportPath`, `BuiltPath`, `PortProv`, and other source-signature declarations, and prevents the final `reference_insertion_whole_action` declaration from being available.

The candidate's printed prefix includes `app_rule` (`propext, Classical.choice, Quot.sound`), `app_witness_scope_fields` (`propext`), `app_core_iff` (`propext, Classical.choice, Quot.sound`), `app_derivation_iff` (`propext, Classical.choice, Quot.sound`), and `installed_call_app_atom` (`propext, Quot.sound`). Those reports came after source-file errors and therefore do **not** constitute accepted theorem results. The final theorem was unknown; the candidate as a whole was not accepted. No conclusion about A/B or the original source obligation follows.

The exact stdout was emitted in the primary execution receipt above; this file retains its byte length and digest plus the full failure classification, but not a second byte-for-byte copy. No Lean/build/test/cache/scratch/worktree/project-copy/environment output was created.

Call 1 is consumed. The proof author is preparing a deterministic, semantics-preserving flattening repair for review. No second invocation is authorized by this receipt.

### Proposed call-2 exact assembly

No Lean artifact or dependency file changes. Inspection found eight Generation private helpers: premises, node, endpoint, check, annotated, suffix, patternContext, statementContext. The private node helper is visible after opening OriginalSource in the concatenated module; Signature's PortProv/Developed/SupportPath/BuiltPath constructor arguments use unbound node identifiers intended for auto-implicit generalization. The collision makes the private function win name resolution. Signature's only private declaration is zipIdx_membership. Syntax has no private declaration. Neither Generation nor R90 contains any zipIdx_membership token. R90 has no auto-implicit use of any Generation helper name; its node accesses are qualified by graph objects.

Both Signature and Generation depend only on Syntax. A semantics-preserving topological order therefore avoids exposing Generation's private node to Signature:

1. `OriginalSourceSyntax.lean`
2. `SourceSignatureConstruction.lean`
3. `OriginalSourceGeneration.lean`
4. `SourceRegistrationAppBridgeR90.lean`

Use exactly the previous import removal and byte joining, merely with this order: for each exact frozen file read bytes and retain lines with `not line.startswith(b'import YulangClosure.')` via splitlines(keepends=True); join retained lines with b''.join and the four bodies with b'\n'.join. The direct pinned Std import stays present. No alpha-renaming, rewriting, declaration editing, omitted theorem or checker bypass is used. Only independent input order changes. This is not a source/model counterexample.

New exact stdin: **137,750 bytes**, SHA-256 **`3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`**. Independently matched by primary. Candidate remains **11,964 bytes**, SHA-256 **`cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`**. All original table source hashes remain unchanged.

Command remains native `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, cwd notes/theory/lean, LEAN_NUM_THREADS=1, timeout 120 seconds, exact new bytes on stdin. Actual call-1 executable is Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, SHA-256 bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38. Remaining budget is exactly **one call (2/2)**, primary-owned, requiring its fresh exact-input review/authorization. No invocation is made by this handoff or leaf.

All six theorem audit requests remain present. Call-1's first five standard-axiom reports do not establish accepted file/module results because earlier dependency declarations failed. The sixth is unknown. Parent semantic boundary is unchanged. Both leased outputs are now **writes-stopped** pending primary diagnostics; only this handoff changed in revision 2. No scratch, cache, build, source dependency, environment, Git, compiler or other path was written.
