# SOURCE-OWNER-TRACE-REALIZATION-20261027/r1 — implementation handoff

Assignment: `SOURCE-OWNER-TRACE-REALIZATION-20261027/r1`, handoff revision 1
Contract SHA-256: `71ecc354bcd354396ed9b12ce15b9bb8a0070763b1492b08993fb40a92e44bbe`
Parent gate: original complete Yulang inference/executor objective; remains OPEN.
Worker: `/root/source_owner_trace_impl`; session UUID unavailable. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN.

## Baseline and revalidated pins

The contract's `ba58eb4dcaa9d99280e9398b25a9f0d4f3030ac6` is the pre-admission code/dependency tree. Assignment metadata was admitted by commit `f45fa90d273335b6dea52e9c83e4750418d58664` (the observed HEAD at launch). Luna confirmed these identities have distinct purposes; no contract bytes were changed.

The contract and all listed direct pins were rehashed before consumption and again before this handoff. They matched:

- Previous contract/review/outcome: r5 `6c6b0de7d4d8f5259308d3aae6abd8aa1574b162ff06ed3e5b2375b32a260c0c`; review `52ec11907e6879c99a8e4604e630490b7a741815339c44aed26396a6a654dc17`; outcome `c0ea8a2e1d1d0233c406ae139db17de87cea952912d7ba4ed2d1d44845f846de`.
- Schema and prior algebra module `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean`: full file `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`; accepted schema prefix, bytes `[0,13698)` / lines 1–292: `266e169aaef8e79c41103fecdc7edae939d9059f49edde2e52ac39ffba4a769e`. Schema audit: `4e8b039e4baca4ce71381cbc959603e96ab07acf291efb6a4e52a321ca334e0d`.
- Prior reviewed finite fixture/consumer: trace `73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3`; consumer `ed25ec65c5760e4a523fabe75f392c67476a710d3af60e345c07e5bf5eaeeb09`.
- Original source/Identity modules: `OriginalSourceSyntax.lean` `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`; `OriginalSourceGeneration.lean` `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`; `OriginalSourceEnvironment.lean` `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`; `OriginalSourceEvents.lean` `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`; `OriginalFormalShared.lean` `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7`; `OriginalIdentityRealization.lean` `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42`; `OriginalIdentityEntryOrigin.lean` `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e`.
- Source definition: design `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`; Lean companion `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Authenticity owners: `full_parse.rs` `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`; `yu-hir/src/module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; `module/local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `source_identity.rs` `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23`; `shadow.rs` `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e`.
- Isolated runner pins: `Cargo.toml` `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; `Cargo.lock` `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`; `src/main.rs` `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`; Lean toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.

## Result and owner/source evidence

The adapter was repaired only at its leased path. It now requires the exact absolute output argument, verifies the actual cwd against the repository root, and performs owner and foreign identity rejection before the write. It emits only `originTable` and raw status fields; it contains no generated theorem/proof, `native_decide`, coordinate witness, or successful Identity/Context allocation claim.

Frozen adapter SHA-256: `4921d14f813e931cb064ecc87d8120734b69d1eedaf48fe0bd36deb014e862e9`.
Frozen emitted trace path: `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean`.
Trace SHA-256: `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a`.

Executed fixture: `my value = \\x -> { (\\x -> x) x; x }`. The output records nine physical rows, two formals with distinct parameter ordinals and exact binder-token ranges, three name-resolution rows, the raw Apply callee Group and its projected Lambda, and both ordered body entries (statement expression then final expression). Before emission, checks joined selected-parse source keys and ranges to LocalSource indices and HIR occurrences; authenticated the definition root and inline binder origin; checked argument/inner-body/sibling parameter identities; and rejected a second same-byte `ParsedFile` plus an occurrence from its separately lowered foreign `HirModule`. The successful stdout records `foreign_parse=REJECTED`, `foreign_hir=REJECTED`, `cwd=/home/momota1029/rust/yulang`, and the exact absolute leased output target.

This is executed Rust owner evidence, not a Lean proof or a source/native theorem. It does not establish original `OriginalSource.Context`, declaration allocation, caller root route, ambient scope/event telescope or runtime Frame provenance. `callerContext := none` means unobserved, not empty. No Identity allocation, native correspondence, universal frontend refinement, Simple-sub A/B, soundness, Effect hygiene, principality, termination, full Call, or production gate is claimed closed.

## Cargo execution receipts and budget

Exact command for each invocation (run from the repository root):

```text
CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-source-owner-trace-realization-20261027/impl/target cargo run --offline --locked --manifest-path /home/momota1029/rust/yulang/tools/inline-authentic-extraction/Cargo.toml --bin original_owner_reify -- /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean
```

1. Call 1: 23.051757s, exit 1. Compilation succeeded, then the adapter's incorrect `../../..` root derivation expected `/home/momota1029/rust` although actual cwd was the repository root. It rejected before foreign checks and before publication; no trace existed. `stdout.log` SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; `stderr.log` SHA-256 `1bf7c19c14fa26069de21deee623b64fcb2735b5e0cab921a8e339fa65c34de2`; receipt SHA-256 `7ecb5cdb591234e3e6aaeb5d4137871b5c1587c2b94d2971c40434f45d677998`.
2. Call 2: 0.272383s, exit 0, after the bounded root-derivation repair to `../..`. All parse/HIR/owner checks passed, including both foreign checks before the output write. stdout SHA-256 `e3c7ad4a044534f8e23b01dd1e51e6ab958aa5507986a3e06635bd0cbfd726bf`; stderr SHA-256 `c6f1a58445df324aeae1a716e9643c7e2dfdf6f6ad4164cdd156e6837d3e1f99`; receipt SHA-256 `d168474903bfa32d99df10002c0e472340e8277c1e0475e8ed04a2ef1324888c`.

Shared command record SHA-256: `c2be37e00d5347b290af7ecf8b6ba1622a454a800de11942d39abdd22031dc89`. Cargo budget spent: 2/2 calls and 23.324s/240s; both calls were offline/locked, one build job, isolated under the assigned scratch root, and within the per-process bound. No third execution, tests, Lean, or Lake process was run. No dependency, manifest, lockfile, compiler owner, source domain, diagnostic, or semantic expectation was changed.

## Reused evidence, open TODOs, and cessation

Reused the accepted r5 schema/algebra, reviewed R2 finite fixture, pinned source owner APIs, and prior review's exact successor requirements (absolute cwd/target, pre-write foreign rejection, and proof construction outside the generated trace). Rejected the prior adapter's cwd-relative output, post-write foreign-parse check, missing foreign-HIR exercise, and generated `native_decide`/coordinate witnesses. The prior lock-hash transcription error was not reused; the pinned lock hash above was recomputed and matches.

Proof owner TODO, only after Luna acknowledges this trace hash: consume this immutable trace in the separately leased instance file; construct and kernel-check concrete coordinates, `CoordinateLaws`, `TableToSource` and `TableToDeclaration`; apply Identity/application/owner-walk results with genuine root inputs explicit; audit theorem types and transitive axioms. Source owner TODO: supply authentic caller Context, root route/declaration, ambient telescope and Frame/event provenance. These remain OPEN and block only dependent proof/production.

Scratch path: `/tmp/yulang-source-owner-trace-realization-20261027/impl/`, including isolated `target/`, command, logs, and receipts. All Cargo processes exited. No proof/Lean process was launched. Implementation writer STOPPED after this frozen handoff; no further writes or verification runs are pending. This is a worker cessation receipt, not independent review or theorem certification.
