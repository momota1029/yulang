# R10 amendment 01 — bounded repair and final audit

Selector: `/root/r21_closeout_selector`, consulted after R10 audit 1 failed. Luna grants this amendment under the standing goal and R10 authority.

## Authenticated basis

- Original contract SHA256: `17198cecb75b2ab1500fb9da60c78028bae87e45b28a790d99e2797d9405a2ca`.
- Original audit plan SHA256: `4a14c7674159c1de85f62159e87779b79343303a6dcad4e8650632b82440a4e2`.
- Audit 1: exit 1; 13.51 seconds; maximum RSS 798448 KiB. Raw stdout SHA256 `e5a2afbd2976a470c74d3261f96167959055ea019c2da06f302b07d70c919e8d`; stderr `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60`; status `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`; time `f784a46651ba226ed8c393fbc26d6c35a17e300bdd0541ba2b09917a05d99e48`.
- Frozen artifact revision 2 SHA256 `6638d59a39423c78e37052932a5b421932719fdeee939f94c7eec2e528467c8d`; proof handoff SHA256 `1226596076500f32e82433340dd5e60dc8d736476d613d95552ef315a0ac5ff8`.

## Exact continuation authority

Reallocate 90 seconds from the original 150-second primary allocation: 60 seconds remain for primary preparation, adjudication and closeout. The same registered `lean_prover` receives a 90-second continuation lease on only:

- `notes/theory/lean/YulangClosure/FormalPermissionSourceInstance.lean`
- `tasks/agent-loop/inbox/effect-permission-source-instance-r10-proof.md`

The continuation permits at most 30 seconds for repair and freeze, then stops. Its only edit is to explicitly unfold the existing `Frame` abbreviation at the three audit-1 conversion sites (artifact lines 98, 116 and 175), preserving all theorem statements, constructors and assumptions. If `exact_tree_supplier` remains unsolved or a substantive dependent-index/construction issue appears, stop without broadening scope.

Preserve revision 2 and audit 1 unchanged. No Lean/Lake probe is permitted during repair. The separate audit-2 project, copy receipt and generated outputs are primary-owned under `/tmp/yulang-effect-permission-source-instance-20261029-r10/attempt-2/`; it must begin without `.lake` or shared cache and use exact frozen dependencies and all four theorem roots.

After the artifact and handoff revision are frozen, Luna may release the **second and final** focused audit with a 60-second timeout. Freeze the complete plan, project inventory, tool hashes, argv/environment and raw receipt paths before release. Audit 1 consumed 13.51 seconds; the combined audit limit remains 120 seconds. No third audit or automatic extension is authorized.

The independent review allocation remains 250 seconds and starts only after successful audit 2. If the repair cannot freeze in 30 seconds, the primary cannot retain its 60 seconds, or audit 2 fails, close R10 `CLOSED_INCOMPLETE`; preserve both revisions and all receipts. No compiler edits, tests, Cargo, instrumentation or Git operations are authorized.
