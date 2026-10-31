# R76 Lean handoff — both permitted audits FAILED; no R76 theorem accepted

Worker: `/root/r76_proof`. Contract SHA-256 `87325ab223af0e98a6ca8c78162ead6ba1d72403b318342d155ee5dd55069936`; input manifest R2 SHA-256 `6c386e096fea70fa22a3b73fa237d08ee57f263aff994ac35eb54106575a909d` (R1 omitted transitive inputs; corrected by primary amendment before this execution). Claim class: finite source-inventory constructor and successful native-order scan agreement, not native extraction or parent closure.

Owned paths: `notes/theory/lean/YulangClosure/SourceInternalChoiceR76.lean` and this handoff only. No scratch/generated/cache/build paths. Audit 1 failed before reaching R76; audit 2 ran once under primary authorization and failed on R76 declarations. Both permitted invocations are consumed; no theorem is accepted.

## Original claim and correspondence

Original A/B quantifiers remain those of `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, corrected by Authoritative `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. This packet addresses only the first source/Internal-incidence choice premises; it does not prove original source preservation, full Call/effect hygiene or whole-language soundness. Research drafts are not semantic authority.

Native anchor: `InferenceSession::internal_formal_permission_incidence`, `lib.rs:18281–18413`. R55 complete primitive formals/recipes/constructions/plans/receipts/parameterRecipes supply the model. The ordered scan visits complete origins without Function/entry prefilter, checks eligible registration recipes before component comparison, retains the first match and stops at a second match. R66 `ownerSelection` instead mapM-collects before singleton testing; successful results agree, diagnostic trace equality is not claimed. `construct` receives only source inventories, exact use, receiving owner and target owner; it computes the unique plan and global origin and checks exact indexed formal/recipe/parameter equality. `formal.nativeRoot` is never substituted for the registered Lambda-root component.

The proof-carrying constructor remains partial: malformed or absent evidence returns none. `construction_certifies` states its result match explicitly, without assuming a supplied plan, selected registration, R66 success, Root, readRoot or policy result. Actual Rust inventory authentication, full source fact incidence, source Lambda permission, current physical/root joins and genuine R66 Root remain OPEN under their source/native owners.

## Audit 1 frozen proposal

Command: exact pinned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, Python subprocess timeout 120 seconds, `LEAN_NUM_THREADS=1`, cwd `notes/theory/lean`. Binary SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Installed toolchain pin is Lean 4.35.0. Lake commands prohibited by packet; bundled checker cannot run without generating import artifacts and is not used.

Exact stdin reconstruction: depth-first postorder import traversal starting at `YulangClosure.SourceInternalChoiceR76`; visit each module once, following import lines in source order and only `YulangClosure.*`. For each UTF-8 source, remove precisely lines matching `^import YulangClosure\.[A-Za-z0-9_.]+\n` (multiline), append remaining bytes plus one newline. Preserve `import Std`. Append `\nset_option pp.universes true\nset_option pp.width 140\n`, then for each top-level `^theorem ([A-Za-z0-9_]+)` in R76 source order append `#check @YulangClosure.SourceInternalChoiceR76.NAME\n#print axioms YulangClosure.SourceInternalChoiceR76.NAME\n`.

Input lives only in Python memory and stdin. stdout/stderr captured only in memory then preserved verbatim in this leased handoff; no output artifacts/destinations, .olean/.ilean/cache/target/scratch/build directory, environment or worktree. Do not execute until primary freezes authorization in current state.

```json
{
  "inputs": [
    {
      "path": "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean",
      "sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e"
    },
    {
      "path": "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean",
      "sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f"
    },
    {
      "path": "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean",
      "sha256": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c"
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean",
      "sha256": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575"
    },
    {
      "path": "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean",
      "sha256": "4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2"
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalContextR55.lean",
      "sha256": "7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123"
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63"
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b"
    },
    {
      "path": "notes/theory/lean/YulangClosure/ReachedSlotSearchR58.lean",
      "sha256": "431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079"
    },
    {
      "path": "notes/theory/lean/YulangClosure/ReachedSlotCompletenessR59.lean",
      "sha256": "d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab"
    },
    {
      "path": "notes/theory/lean/YulangClosure/NativeLocalDecodeR60.lean",
      "sha256": "3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20"
    },
    {
      "path": "notes/theory/lean/YulangClosure/BoundedAncestryR61.lean",
      "sha256": "9e1c783016bc14487dd0a4ebc2839dfab0dc3daf911ee88fa02f3624e2ad60a4"
    },
    {
      "path": "notes/theory/lean/YulangClosure/InternalRootPolicyR62.lean",
      "sha256": "e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e"
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedConsumerR66.lean",
      "sha256": "5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1"
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR76.lean",
      "sha256": "5233c0784281ba4483db402a7f732b1bb71b766579cc16a77987bf53ebb45ac8"
    }
  ],
  "stdin_bytes": 444759,
  "stdin_sha256": "378bda8a94ad50d74f5e1a576813d80d98192f4aa69747e5948e7e14f8ebbf5d",
  "theorems": [
    "visit_agrees",
    "walk_accounts_for_all",
    "ordered_selection_agrees",
    "malformed_recipe_first",
    "second_origin_first",
    "choice_three_premises",
    "choice_applies_r66",
    "exact_use_unique",
    "construction_certifies",
    "finite_constructs_choice",
    "finite_bad_inventories_reject"
  ]
}
```

Historical pre-audit-1 status above was CONSTRUCTED/UNCHECKED. Actual audit 1 failure and frozen audit 2 proposal follow below.

## Audit 1 actual execution

{
  "authorization_commit": "a398a8415",
  "manifest_R2_sha256": "6c386e096fea70fa22a3b73fa237d08ee57f263aff994ac35eb54106575a909d",
  "stdin_sha256": "378bda8a94ad50d74f5e1a576813d80d98192f4aa69747e5948e7e14f8ebbf5d",
  "exit": 1,
  "elapsed_seconds": 17.518,
  "stdout_bytes": 61639,
  "stdout_sha256": "e7030cc3d9b801fa2d7f7e0f3be6693523243c402da6cd9d5319b8596a831fe3",
  "stderr_bytes": 0,
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}

Verbatim stdout:
```text
<stdin>:5131:8: error: (kernel) excessive memory consumption detected
<stdin>:5151:8: error: (kernel) excessive memory consumption detected
<stdin>:5171:8: error: (kernel) excessive memory consumption detected
<stdin>:5183:8: error: (kernel) excessive memory consumption detected
<stdin>:5279:8: error: (kernel) excessive memory consumption detected
<stdin>:5288:8: error: (kernel) excessive memory consumption detected
<stdin>:5299:8: error: (kernel) excessive memory consumption detected
<stdin>:5310:8: error: (kernel) excessive memory consumption detected
<stdin>:5318:8: error: (kernel) excessive memory consumption detected
<stdin>:5329:8: error: (kernel) excessive memory consumption detected
<stdin>:5340:8: error: (kernel) excessive memory consumption detected
<stdin>:5349:8: error: (kernel) excessive memory consumption detected
<stdin>:5357:8: error: (kernel) excessive memory consumption detected
<stdin>:5369:8: error: (kernel) excessive memory consumption detected
<stdin>:5387:8: error: (kernel) excessive memory consumption detected
<stdin>:5399:8: error: (kernel) excessive memory consumption detected
<stdin>:5415:8: error: (kernel) excessive memory consumption detected
<stdin>:5433:4: error: (kernel) excessive memory consumption detected
<stdin>:5435:4: error: (kernel) excessive memory consumption detected
<stdin>:5441:4: error: failed to compile definition, compiler IR check failed at `YulangClosure.ReachedSlotCompletenessR59.mixedSupport._closed_0`. Error: unknown join point 'block_0'
PANIC at _private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType Lean.Compiler.LCNF.ExplicitBoxing:301:45: unreachable code has been reached
backtrace:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) [0x75b2f3c21e05]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) [0x75b2f3c18987]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) [0x75b2f3c18a6b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(panic spec at Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType+0x65c) [0x75b2eee4db8c]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType [private]+0x6f2) [0x75b2eee4e6c2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitBoxing.visitLet [private]+0x75) [0x75b2eee510e5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitBoxing [private]+0x96) [0x75b2eee54636]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.foldlMUnsafe.fold [private] spec at Lean.Compiler.LCNF.run+0x249) [0x75b2eee58a39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.run [private]+0x3e) [0x75b2eee5927e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.run [boxed, private]+0x1d) [0x75b2eee5936d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x1ac) [0x75b2f3c2dbdc]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [λ, private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0xc4) [0x75b2eea3fe44]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0x35f) [0x75b2eea420ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [λ, private]+0x2e) [0x75b2eea43b6e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [boxed, λ, private]+0x6e) [0x75b2eea43fee]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xf09) [0x75b2f3c25dd9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [λ, arity↓]+0xb) [0x75b2ee27c71b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_profileit+0x83) [0x75b2f3bf6133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [arity↓]+0x82) [0x75b2ee27c892]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d9) [0x75b2eea4b6e9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run+0x1f11) [0x75b2eea4e2b1]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run [boxed]+0x1d) [0x75b2eea4eaad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x87a) [0x75b2f3c2ca2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.CompilerM.run [arity↓]+0xb2) [0x75b2ee9a4be2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.main [boxed]+0xf) [0x75b2eea515ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x189) [0x75b2f3c2c339]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [λ, private]+0xd8) [0x75b2ee38cf18]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [boxed, λ, private]+0x15) [0x75b2ee38d265]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x8ff) [0x75b2f3c2945f]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [λ]+0x44) [0x75b2ee38fcb4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [boxed, λ]+0x24) [0x75b2ee390034]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x115e) [0x75b2f3c2b8be]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x409) [0x75b2ee3857a9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386562]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee3868db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386e92]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee38720b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdin [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386a42]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.FS.withIsolatedStreams [arity↓] spec at Lean.Core.wrapAsyncAsSnapshot+0x106) [0x75b2ee387376]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x81) [0x75b2ee387841]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x1194) [0x75b2f3c2b8f4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x34) [0x75b2ee37a654]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.withCurrHeartbeats [arity↓] spec at Lean.Core.wrapAsync+0x8) [0x75b2ee37a418]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [λ, arity↓]+0x481) [0x75b2ee37ab11]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x6a) [0x75b2ee37ae7a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x305) [0x75b2f3c26ea5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x1b) [0x75b2ee3878bb]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x9) [0x75b2ee387c39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x1293) [0x75b2f3c27e33]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x964562b) [0x75b2f3c4562b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x120b) [0x75b2f3c260db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x11a6) [0x75b2f3c26076]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962386e) [0x75b2f3c2386e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962493d) [0x75b2f3c2493d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) [0x75b2f3c169da]
/lib/x86_64-linux-gnu/libc.so.6(+0x9cb84) [0x75b2ea29cb84]
/lib/x86_64-linux-gnu/libc.so.6(+0x129ecc) [0x75b2ea329ecc]
PANIC at _private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.visitLet Lean.Compiler.LCNF.ExplicitBoxing:336:45: unreachable code has been reached
backtrace:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) [0x75b2f3c21e05]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) [0x75b2f3c18987]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) [0x75b2f3c18a6b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(panic spec at Lean.Compiler.LCNF.Code.explicitBoxing.visitLet+0x668) [0x75b2eee4f6c8]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitBoxing.visitLet [private]+0x443) [0x75b2eee514b3]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitBoxing [private]+0x96) [0x75b2eee54636]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.foldlMUnsafe.fold [private] spec at Lean.Compiler.LCNF.run+0x249) [0x75b2eee58a39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.run [private]+0x3e) [0x75b2eee5927e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.run [boxed, private]+0x1d) [0x75b2eee5936d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x1ac) [0x75b2f3c2dbdc]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [λ, private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0xc4) [0x75b2eea3fe44]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0x35f) [0x75b2eea420ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [λ, private]+0x2e) [0x75b2eea43b6e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [boxed, λ, private]+0x6e) [0x75b2eea43fee]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xf09) [0x75b2f3c25dd9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [λ, arity↓]+0xb) [0x75b2ee27c71b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_profileit+0x83) [0x75b2f3bf6133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [arity↓]+0x82) [0x75b2ee27c892]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d9) [0x75b2eea4b6e9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run+0x1f11) [0x75b2eea4e2b1]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run [boxed]+0x1d) [0x75b2eea4eaad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x87a) [0x75b2f3c2ca2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.CompilerM.run [arity↓]+0xb2) [0x75b2ee9a4be2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.main [boxed]+0xf) [0x75b2eea515ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x189) [0x75b2f3c2c339]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [λ, private]+0xd8) [0x75b2ee38cf18]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [boxed, λ, private]+0x15) [0x75b2ee38d265]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x8ff) [0x75b2f3c2945f]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [λ]+0x44) [0x75b2ee38fcb4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [boxed, λ]+0x24) [0x75b2ee390034]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x115e) [0x75b2f3c2b8be]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x409) [0x75b2ee3857a9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386562]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee3868db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386e92]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee38720b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdin [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386a42]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.FS.withIsolatedStreams [arity↓] spec at Lean.Core.wrapAsyncAsSnapshot+0x106) [0x75b2ee387376]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x81) [0x75b2ee387841]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x1194) [0x75b2f3c2b8f4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x34) [0x75b2ee37a654]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.withCurrHeartbeats [arity↓] spec at Lean.Core.wrapAsync+0x8) [0x75b2ee37a418]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [λ, arity↓]+0x481) [0x75b2ee37ab11]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x6a) [0x75b2ee37ae7a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x305) [0x75b2f3c26ea5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x1b) [0x75b2ee3878bb]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x9) [0x75b2ee387c39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x1293) [0x75b2f3c27e33]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x964562b) [0x75b2f3c4562b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x120b) [0x75b2f3c260db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x11a6) [0x75b2f3c26076]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962386e) [0x75b2f3c2386e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962493d) [0x75b2f3c2493d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) [0x75b2f3c169da]
/lib/x86_64-linux-gnu/libc.so.6(+0x9cb84) [0x75b2ea29cb84]
/lib/x86_64-linux-gnu/libc.so.6(+0x129ecc) [0x75b2ea329ecc]
PANIC at Std.DTreeMap.Internal.Impl.Const.get! Std.Data.DTreeMap.Internal.Queries:227:13: Key is not present in map
backtrace:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) [0x75b2f3c21e05]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) [0x75b2f3c18987]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) [0x75b2f3c18a6b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitRc [private]+0x4ee) [0x75b2eee7c16e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc.go [private]+0xc9) [0x75b2eee80519]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [λ, private]+0x1d6) [0x75b2eee80f46]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [boxed, λ, private]+0x28) [0x75b2eee812e8]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x68a) [0x75b2f3c2e0ba]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.DeclValue.mapCodeM [arity↓] spec at Lean.Compiler.LCNF.Decl.explicitRc+0x105) [0x75b2eee809c5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [private]+0xb8) [0x75b2eee814a8]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [boxed, private]+0x19) [0x75b2eee816b9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x1ac) [0x75b2f3c2dbdc]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.mapMUnsafe.map [private] spec at Lean.Compiler.LCNF.Pass.mkPerDeclaration+0x1b1) [0x75b2eea90811]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Pass.mkPerDeclaration [boxed, λ]+0x2c) [0x75b2eea90d1c]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x903) [0x75b2f3c2e333]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [λ, private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0xc4) [0x75b2eea3fe44]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0x35f) [0x75b2eea420ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [λ, private]+0x2e) [0x75b2eea43b6e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [boxed, λ, private]+0x6e) [0x75b2eea43fee]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xf09) [0x75b2f3c25dd9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [λ, arity↓]+0xb) [0x75b2ee27c71b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_profileit+0x83) [0x75b2f3bf6133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [arity↓]+0x82) [0x75b2ee27c892]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d9) [0x75b2eea4b6e9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run+0x1f11) [0x75b2eea4e2b1]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run [boxed]+0x1d) [0x75b2eea4eaad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x87a) [0x75b2f3c2ca2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.CompilerM.run [arity↓]+0xb2) [0x75b2ee9a4be2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.main [boxed]+0xf) [0x75b2eea515ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x189) [0x75b2f3c2c339]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [λ, private]+0xd8) [0x75b2ee38cf18]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [boxed, λ, private]+0x15) [0x75b2ee38d265]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x8ff) [0x75b2f3c2945f]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [λ]+0x44) [0x75b2ee38fcb4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [boxed, λ]+0x24) [0x75b2ee390034]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x115e) [0x75b2f3c2b8be]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x409) [0x75b2ee3857a9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386562]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee3868db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386e92]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee38720b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdin [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386a42]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.FS.withIsolatedStreams [arity↓] spec at Lean.Core.wrapAsyncAsSnapshot+0x106) [0x75b2ee387376]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x81) [0x75b2ee387841]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x1194) [0x75b2f3c2b8f4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x34) [0x75b2ee37a654]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.withCurrHeartbeats [arity↓] spec at Lean.Core.wrapAsync+0x8) [0x75b2ee37a418]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [λ, arity↓]+0x481) [0x75b2ee37ab11]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x6a) [0x75b2ee37ae7a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x305) [0x75b2f3c26ea5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x1b) [0x75b2ee3878bb]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x9) [0x75b2ee387c39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x1293) [0x75b2f3c27e33]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x964562b) [0x75b2f3c4562b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x120b) [0x75b2f3c260db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x11a6) [0x75b2f3c26076]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962386e) [0x75b2f3c2386e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962493d) [0x75b2f3c2493d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) [0x75b2f3c169da]
/lib/x86_64-linux-gnu/libc.so.6(+0x9cb84) [0x75b2ea29cb84]
/lib/x86_64-linux-gnu/libc.so.6(+0x129ecc) [0x75b2ea329ecc]
PANIC at Option.get! Init.Data.Option.BasicAux:22:14: value is none
backtrace:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) [0x75b2f3c21e05]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) [0x75b2f3c18987]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) [0x75b2f3c18a6b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Code.explicitRc [private]+0x14b3) [0x75b2eee7d133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc.go [private]+0xc9) [0x75b2eee80519]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [λ, private]+0x1d6) [0x75b2eee80f46]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [boxed, λ, private]+0x28) [0x75b2eee812e8]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x68a) [0x75b2f3c2e0ba]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.DeclValue.mapCodeM [arity↓] spec at Lean.Compiler.LCNF.Decl.explicitRc+0x105) [0x75b2eee809c5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [private]+0xb8) [0x75b2eee814a8]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Decl.explicitRc [boxed, private]+0x19) [0x75b2eee816b9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x1ac) [0x75b2f3c2dbdc]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.mapMUnsafe.map [private] spec at Lean.Compiler.LCNF.Pass.mkPerDeclaration+0x1b1) [0x75b2eea90811]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.Pass.mkPerDeclaration [boxed, λ]+0x2c) [0x75b2eea90d1c]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/6>+0x903) [0x75b2f3c2e333]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [λ, private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0xc4) [0x75b2eea3fe44]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run.runPassManagerPart+0x35f) [0x75b2eea420ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [λ, private]+0x2e) [0x75b2eea43b6e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run.runPassManagerPart [boxed, λ, private]+0x6e) [0x75b2eea43fee]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xf09) [0x75b2f3c25dd9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [λ, arity↓]+0xb) [0x75b2ee27c71b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_profileit+0x83) [0x75b2f3bf6133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [arity↓]+0x82) [0x75b2ee27c892]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d9) [0x75b2eea4b6e9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run+0x1f11) [0x75b2eea4e2b1]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run [boxed]+0x1d) [0x75b2eea4eaad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x87a) [0x75b2f3c2ca2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.CompilerM.run [arity↓]+0xb2) [0x75b2ee9a4be2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.main [boxed]+0xf) [0x75b2eea515ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x189) [0x75b2f3c2c339]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [λ, private]+0xd8) [0x75b2ee38cf18]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [boxed, λ, private]+0x15) [0x75b2ee38d265]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x8ff) [0x75b2f3c2945f]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [λ]+0x44) [0x75b2ee38fcb4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [boxed, λ]+0x24) [0x75b2ee390034]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x115e) [0x75b2f3c2b8be]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x409) [0x75b2ee3857a9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386562]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee3868db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386e92]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee38720b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdin [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386a42]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.FS.withIsolatedStreams [arity↓] spec at Lean.Core.wrapAsyncAsSnapshot+0x106) [0x75b2ee387376]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x81) [0x75b2ee387841]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x1194) [0x75b2f3c2b8f4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x34) [0x75b2ee37a654]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.withCurrHeartbeats [arity↓] spec at Lean.Core.wrapAsync+0x8) [0x75b2ee37a418]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [λ, arity↓]+0x481) [0x75b2ee37ab11]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x6a) [0x75b2ee37ae7a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x305) [0x75b2f3c26ea5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x1b) [0x75b2ee3878bb]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x9) [0x75b2ee387c39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x1293) [0x75b2f3c27e33]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x964562b) [0x75b2f3c4562b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x120b) [0x75b2f3c260db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x11a6) [0x75b2f3c26076]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962386e) [0x75b2f3c2386e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962493d) [0x75b2f3c2493d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) [0x75b2f3c169da]
/lib/x86_64-linux-gnu/libc.so.6(+0x9cb84) [0x75b2ea29cb84]
/lib/x86_64-linux-gnu/libc.so.6(+0x129ecc) [0x75b2ea329ecc]
PANIC at Std.DHashMap.Internal.AssocList.get! Std.Data.DHashMap.Internal.AssocList.Basic:163:11: key is not present in hash table
backtrace:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) [0x75b2f3c21e05]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) [0x75b2f3c18987]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) [0x75b2f3c18a6b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.IR.ToIR.getJoinPointValue [arity↓]+0x33) [0x75b2ee96a6b3]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.IR.ToIR.lowerCode+0xb47) [0x75b2ee96fb27]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.IR.ToIR.lowerDecl+0x278) [0x75b2ee976748]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.IR.ToIR.lowerDecl [boxed]+0x13) [0x75b2ee976d23]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0xbc7) [0x75b2f3c2b327]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.IR.ToIR.M.run [arity↓]+0x7f) [0x75b2ee969aef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.IR.toIR+0xb0) [0x75b2ee976e50]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [λ, private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d) [0x75b2eea4a7ad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [boxed, λ, private] spec at Lean.Compiler.LCNF.PassManager.run+0x1d) [0x75b2eea4aa0d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xe2e) [0x75b2f3c25cfe]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [λ, arity↓]+0xb) [0x75b2ee27c71b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0xb5a) [0x75b2f3c25a2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_profileit+0x83) [0x75b2f3bf6133]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.profileitIOUnsafe [arity↓]+0x82) [0x75b2ee27c892]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Array.forIn'Unsafe.loop [private] spec at Lean.Compiler.LCNF.PassManager.run+0x45b) [0x75b2eea4b96b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run+0x1f11) [0x75b2eea4e2b1]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.PassManager.run [boxed]+0x1d) [0x75b2eea4eaad]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x87a) [0x75b2f3c2ca2a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.CompilerM.run [arity↓]+0xb2) [0x75b2ee9a4be2]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Compiler.LCNF.main [boxed]+0xf) [0x75b2eea515ef]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/5>+0x189) [0x75b2f3c2c339]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [λ, private]+0xd8) [0x75b2ee38cf18]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls.doCompile [boxed, λ, private]+0x15) [0x75b2ee38d265]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x8ff) [0x75b2f3c2945f]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [λ]+0x44) [0x75b2ee38fcb4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.compileDecls [boxed, λ]+0x24) [0x75b2ee390034]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x115e) [0x75b2f3c2b8be]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x409) [0x75b2ee3857a9]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386562]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStderr [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee3868db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386e92]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdout [boxed] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x1b) [0x75b2ee38720b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.withStdin [arity↓] spec at IO.FS.withIsolatedStreams spec at Lean.Core.wrapAsyncAsSnapshot+0x52) [0x75b2ee386a42]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(IO.FS.withIsolatedStreams [arity↓] spec at Lean.Core.wrapAsyncAsSnapshot+0x106) [0x75b2ee387376]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x81) [0x75b2ee387841]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/4>+0x1194) [0x75b2f3c2b8f4]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x34) [0x75b2ee37a654]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) [0x75b2f3c294d0]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.withCurrHeartbeats [arity↓] spec at Lean.Core.wrapAsync+0x8) [0x75b2ee37a418]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [λ, arity↓]+0x481) [0x75b2ee37ab11]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsync [boxed, λ, arity↓]+0x6a) [0x75b2ee37ae7a]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x305) [0x75b2f3c26ea5]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [λ, arity↓]+0x1b) [0x75b2ee3878bb]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(Lean.Core.wrapAsyncAsSnapshot [boxed, λ, arity↓]+0x9) [0x75b2ee387c39]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/2>+0x1293) [0x75b2f3c27e33]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x964562b) [0x75b2f3c4562b]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x120b) [0x75b2f3c260db]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/1>+0x11a6) [0x75b2f3c26076]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962386e) [0x75b2f3c2386e]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x962493d) [0x75b2f3c2493d]
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) [0x75b2f3c169da]
/lib/x86_64-linux-gnu/libc.so.6(+0x9cb84) [0x75b2ea29cb84]
/lib/x86_64-linux-gnu/libc.so.6(+0x129ecc) [0x75b2ea329ecc]
<stdin>:5442:4: error: (kernel) excessive memory consumption detected
<stdin>:5445:8: error: (kernel) excessive memory consumption detected
<stdin>:5458:8: error: (kernel) excessive memory consumption detected
<stdin>:5475:8: error: (kernel) excessive memory consumption detected
<stdin>:5492:4: error: (kernel) excessive memory consumption detected
<stdin>:5495:4: error: (kernel) excessive memory consumption detected
<stdin>:5498:4: error: Failed to find LCNF signature for YulangClosure.NativeLocalDecodeR60.fromOption
<stdin>:5501:4: error: Failed to find LCNF signature for YulangClosure.NativeLocalDecodeR60.fromOption
<stdin>:5504:8: error: (kernel) excessive memory consumption detected
<stdin>:5514:8: error: (kernel) excessive memory consumption detected
<stdin>:5519:8: error: (kernel) excessive memory consumption detected
<stdin>:5525:8: error: (kernel) excessive memory consumption detected
<stdin>:5530:8: error: (kernel) excessive memory consumption detected
<stdin>:5542:21: error: (kernel) excessive memory consumption detected
<stdin>:5545:4: error: (kernel) excessive memory consumption detected
<stdin>:5557:8: error: (kernel) excessive memory consumption detected
<stdin>:5557:63: error: (kernel) declaration type mismatch, '_private._stdin.0.YulangClosure.NativeLocalDecodeR60.rawSlot.match_1.eq_1' has type
  ∀ (motive : LowerLane → Sort u_1) (h_1 : Unit → motive LowerLane.row) (h_2 : Unit → motive LowerLane.atom),
    (match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()) =
      match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()
but it is expected to have type
  ∀ (motive : LowerLane → Sort u_1) (h_1 : Unit → motive LowerLane.row) (h_2 : Unit → motive LowerLane.atom),
    (match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()) =
      h_1 ()
<stdin>:5557:63: error: (kernel) excessive memory consumption detected
<stdin>:5557:63: error: (kernel) declaration type mismatch, 'YulangClosure.NativeLocalDecodeR60.rawSlot.eq_2' has type
  ∀ (rowIndex index : Nat), rawSlot rowIndex LowerLane.atom index = rawSlot rowIndex LowerLane.atom index
but it is expected to have type
  ∀ (rowIndex index : Nat),
    rawSlot rowIndex LowerLane.atom index = Slot.mk (Row.effect rowIndex) Lane.effectLowerAtom index
<stdin>:5557:71: error: (kernel) excessive memory consumption detected
<stdin>:5557:76: error: (kernel) excessive memory consumption detected
<stdin>:5557:76: error: (kernel) excessive memory consumption detected
<stdin>:5557:80: error: (kernel) excessive memory consumption detected
<stdin>:5557:80: error: (kernel) excessive memory consumption detected
<stdin>:5557:80: error: (kernel) excessive memory consumption detected
<stdin>:5558:32: error: (kernel) excessive memory consumption detected
<stdin>:5558:53: error: (kernel) excessive memory consumption detected
<stdin>:5549:8: error: (kernel) excessive memory consumption detected
<stdin>:5569:27: error: (kernel) excessive memory consumption detected
<stdin>:5569:27: error: (kernel) excessive memory consumption detected
<stdin>:5569:27: error: (kernel) excessive memory consumption detected
<stdin>:5569:42: error: (kernel) excessive memory consumption detected
<stdin>:5570:18: error: (kernel) declaration type mismatch, '_private._stdin.0.YulangClosure.NativeLocalDecodeR60.rawSlot.match_1.eq_1' has type
  ∀ (motive : LowerLane → Sort u_1) (h_1 : Unit → motive LowerLane.row) (h_2 : Unit → motive LowerLane.atom),
    (match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()) =
      match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()
but it is expected to have type
  ∀ (motive : LowerLane → Sort u_1) (h_1 : Unit → motive LowerLane.row) (h_2 : Unit → motive LowerLane.atom),
    (match LowerLane.row with
      | LowerLane.row => h_1 ()
      | LowerLane.atom => h_2 ()) =
      h_1 ()
<stdin>:5570:18: error: (kernel) excessive memory consumption detected
<stdin>:5570:18: error: (kernel) declaration type mismatch, 'YulangClosure.NativeLocalDecodeR60.rawSlot.eq_2' has type
  ∀ (rowIndex index : Nat), rawSlot rowIndex LowerLane.atom index = rawSlot rowIndex LowerLane.atom index
but it is expected to have type
  ∀ (rowIndex index : Nat),
    rawSlot rowIndex LowerLane.atom index = Slot.mk (Row.effect rowIndex) Lane.effectLowerAtom index
<stdin>:5570:26: error: (kernel) excessive memory consumption detected
<stdin>:5570:31: error: (kernel) excessive memory consumption detected
<stdin>:5570:35: error: (kernel) excessive memory consumption detected
<stdin>:5570:53: error: (kernel) excessive memory consumption detected
<stdin>:5570:74: error: (kernel) excessive memory consumption detected
<stdin>:5560:8: error: (kernel) excessive memory consumption detected
<stdin>:5572:0: error: (kernel) excessive memory consumption detected
<stdin>:5582:14: error: (kernel) excessive memory consumption detected
<stdin>:5579:2: error: (kernel) excessive memory consumption detected
<stdin>:5577:4: warning: declaration uses `sorry`
<stdin>:5577:4: error: (kernel) excessive memory consumption detected
<stdin>:5610:18: error: (kernel) excessive memory consumption detected
<stdin>:5610:4: error: (kernel) excessive memory consumption detected
<stdin>:5591:8: error: (kernel) excessive memory consumption detected
<stdin>:5614:4: error: (kernel) excessive memory consumption detected
<stdin>:5617:8: error: (kernel) excessive memory consumption detected
<stdin>:5626:8: error: (kernel) excessive memory consumption detected
<stdin>:5638:16: error: (kernel) excessive memory consumption detected
<stdin>:5631:8: error: (kernel) excessive memory consumption detected
<stdin>:5642:0: warning: declaration uses `sorry`
<stdin>:5642:0: error: (kernel) excessive memory consumption detected
<stdin>:5661:4: warning: declaration uses `sorry`
<stdin>:5661:4: error: (kernel) excessive memory consumption detected
<stdin>:5681:29: error: (kernel) excessive memory consumption detected
<stdin>:5676:8: error: (kernel) excessive memory consumption detected
<stdin>:5670:4: error: (kernel) excessive memory consumption detected
<stdin>:5667:2: warning: declaration uses `sorry`
<stdin>:5667:2: error: (kernel) excessive memory consumption detected
<stdin>:5666:4: warning: declaration uses `sorry`
<stdin>:5666:4: error: (kernel) excessive memory consumption detected
<stdin>:5695:35: error: don't know how to synthesize implicit argument `c`
  @PhysicalRead.value (?m.17 readPhysical n rowIndex c) T (?m.18 readPhysical n rowIndex c)
    (?m.19 readPhysical n rowIndex c) (?m.20 readPhysical n rowIndex c)
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
rowIndex : Nat
c : Cell
⊢ Cell
<stdin>:5695:35: error: don't know how to synthesize implicit argument `rowIndex`
  @PhysicalRead.value (?m.17 readPhysical n rowIndex c) T (?m.18 readPhysical n rowIndex c)
    (?m.19 readPhysical n rowIndex c) (?m.20 readPhysical n rowIndex c)
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
rowIndex : Nat
c : Cell
⊢ Nat
<stdin>:5695:35: error: don't know how to synthesize implicit argument `n`
  @PhysicalRead.value (?m.17 readPhysical n rowIndex c) T (?m.18 readPhysical n rowIndex c)
    (?m.19 readPhysical n rowIndex c) (?m.20 readPhysical n rowIndex c)
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
rowIndex : Nat
c : Cell
⊢ Native (?m.17 readPhysical n rowIndex c) T
<stdin>:5695:35: error: don't know how to synthesize implicit argument `S`
  @PhysicalRead.value (?m.17 readPhysical n rowIndex c) T (?m.18 readPhysical n rowIndex c)
    (?m.19 readPhysical n rowIndex c) (?m.20 readPhysical n rowIndex c)
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
rowIndex : Nat
c : Cell
⊢ Type
<stdin>:5694:4: error: (kernel) excessive memory consumption detected
<stdin>:5697:8: error: (kernel) excessive memory consumption detected
<stdin>:5708:80: error: don't know how to synthesize implicit argument `T`
  @endpoint S (?m.28 n search rowIndex c r) n.state (Endpoint.effect c.target)
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
search : Search S T
rowIndex : Nat
c : Cell
r : sorry
⊢ Type

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
<stdin>:5708:107: error: don't know how to synthesize implicit argument `Term`
  @Endpoint.effect (?m.28 n search rowIndex c r) c.target
context:
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
search : Search S T
rowIndex : Nat
c : Cell
r : sorry
⊢ Type

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
<stdin>:5708:128: error: unsolved goals
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
n : Native S T
search : Search S T
rowIndex : Nat
c : Cell
r : sorry
⊢ AuthenticatedResidualConsumerR49.StepReads (inputs n search)
      (endpoint n.state (Endpoint.effect (EffectEndpoint.row rowIndex))) (step (Step.physical sorry)) ∧
    AuthenticatedResidualConsumerR49.next (step (Step.physical sorry)) = endpoint n.state (Endpoint.effect c.target)
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5753:0: error: (kernel) excessive memory consumption detected
<stdin>:5757:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'rows', which is 'noncomputable'
<stdin>:5760:8: warning: declaration uses `sorry`
<stdin>:5760:8: error: (kernel) excessive memory consumption detected
<stdin>:5777:8: error: (kernel) excessive memory consumption detected
<stdin>:5795:8: error: maximum number of errors (100; from option `maxErrors`) reached, exiting
```

Verbatim stderr:
```text
```

## Audit 1 failure disposition

Audit 1 FAILED with upstream whole-flattened closure memory exhaustion at the fixed 1024 MiB per-process limit, before R76 declarations. No R76 theorem was accepted and no axiom report was obtained. Upstream Lean recovery generated `sorry`-dependent failed declarations and compiler panics; those diagnostics are preserved verbatim above and are not accepted evidence. No source `sorry`/axiom/bypass was introduced. No second invocation has run.

## Audit 2 frozen declaration-slice input — executed once; failed

The previous full closure elaborated unrelated R58–R62 proofs and exhausted memory. This input instead contains exact necessary primitive declaration bodies from pinned R39/R45/R55/R57/R65/R66, full R76 source, and all R76 #check/#print axioms commands. It omits upstream theorems, physical ownership/policy/search definitions and unused source declarations; none is replaced by a stub or axiom. This verifies the exact choice declaration dependency slice only, not the original project import closure.

Extraction rule: UTF-8 lines with original LF endings; concatenate the inclusive source ranges below in listed order. Prefix `import Std\n`. After each R39/R45/R55/R57/R65 group append `end YulangClosure.NAMESPACE\n`. Before R66's `variable` slice append `namespace YulangClosure.OccurrenceQualifiedConsumerR66\nopen ProviderNativeContextR57\n`; after it append `end YulangClosure.OccurrenceQualifiedConsumerR66\n`. This retains actual namespace/name resolution while omitting unused `open ReachedSlotSearchR58`. R76 slice begins at its module comment, omitting only its import line. Append the exact same audit options/query construction as audit 1, now including the additional source-order theorems listed below.

Required dependency completeness: R39 registration/source/permission/input types; R45 use/kind/construction/plan/receipt/query/probe/input types; R55 all primitive inventory types and projections through `internalInputs`; R57 complete branded Key/Fact/Endpoint types and exact source fixture fields; R65 FactRow/Edge/Inventory/Read plus candidates/resolve/readAt/routeFact/lambdaFact/internalInputs and fixtureSource; R66 exact Source alias and ownerSelection body; full R76. R65 internalInputs is preserved literally, including both qualified route and Lambda-fact substitutions.

Proposed command/environment/destination: unchanged exact pinned Lean binary `-j1 -M1024 --stdin`, `LEAN_NUM_THREADS=1`, timeout 120 seconds, cwd `notes/theory/lean`; input/output only in memory and stdout/stderr verbatim in this handoff, no file outputs/generated/cache/scratch/build/targets. Await fresh primary authorization before execution.

```json
{
  "stdin_bytes": 35050,
  "stdin_sha256": "bbe5b3a4f36dfc81c9ac40d696b447cbdb4c4b7170af4a00f92258baf3ecd033",
  "segments": [
    {
      "path": "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean",
      "source_sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
      "first_line": 12,
      "last_line": 75,
      "slice_sha256": "62f6622e56aee18a37b9ae8c0772de82154b5a2db5d6808cc7743b6545671b98",
      "slice_bytes": 1444
    },
    {
      "path": "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean",
      "source_sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
      "first_line": 12,
      "last_line": 88,
      "slice_sha256": "9c82d93bc87236e7aa9bea822fd75cbe4f296ee02d81c5ac83e4ae0f11f65eeb",
      "slice_bytes": 2298
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalContextR55.lean",
      "source_sha256": "7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123",
      "first_line": 10,
      "last_line": 154,
      "slice_sha256": "cdbc3c9afbe6bc9fadd5543bdb400343440c6582fbf108e9b2f92c3bf2aa0c82",
      "slice_bytes": 6344
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 6,
      "last_line": 34,
      "slice_sha256": "8af4d69ded66f267115ae7622e7fe663b2ef33cd6e0cee5d5cbdc0cfe331db05",
      "slice_bytes": 1356
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 785,
      "last_line": 801,
      "slice_sha256": "8d268cf72a44da0ca6c28ea413986883a2c5a618fcb071c4e588da36dff14c34",
      "slice_bytes": 1417
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 10,
      "last_line": 41,
      "slice_sha256": "3fd09684a169ff331579d7e0faf4ba045e590e3c62ecc3c1c9a0dd96c94d717d",
      "slice_bytes": 669
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 43,
      "last_line": 45,
      "slice_sha256": "73a909efee11b7b5ed8c763a3d4ac22bff169f24a081eaf7946d3e291a9b527b",
      "slice_bytes": 175
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 52,
      "last_line": 66,
      "slice_sha256": "342ca11b82022512e1af286984dd3e34b5b5f640e60032a981080224bd22f0b8",
      "slice_bytes": 648
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 215,
      "last_line": 226,
      "slice_sha256": "c6ba0292d1900c6d344014640f60c76015327025e70c1a1cafc0cb0aed5874a0",
      "slice_bytes": 539
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 246,
      "last_line": 251,
      "slice_sha256": "cd6b69b54ba338acfeaff738f60ab81ce7d118ea3d2b8d9910c83d1a0e1c19da",
      "slice_bytes": 330
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 417,
      "last_line": 419,
      "slice_sha256": "d03134598123298a949bc59da11760329d19b9582160f3581ccec39099f77945",
      "slice_bytes": 230
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedConsumerR66.lean",
      "source_sha256": "5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1",
      "first_line": 14,
      "last_line": 33,
      "slice_sha256": "c13495d0114d9499fc076b956dce9b5d9cdf6489123387f98b5886d4f0c0c106",
      "slice_bytes": 1047
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR76.lean",
      "source_sha256": "28f5c2fc3679e3af4ef2f14bb984307fe036b4c979a3cb91f39ba0c9ebf565c3",
      "first_line": 3,
      "last_line": 300,
      "slice_sha256": "cc8b96ad0f5cb0a2f7342605a18d371a608fdbd970aa545c9e80abbfa0722250",
      "slice_bytes": 16087
    }
  ],
  "theorems": [
    "visit_agrees",
    "walk_accounts_for_all",
    "ordered_selection_agrees",
    "malformed_recipe_first",
    "second_origin_first",
    "choice_three_premises",
    "choice_applies_r66",
    "exact_use_unique",
    "construction_certifies",
    "finite_constructs_choice",
    "finite_bad_inventories_reject",
    "finite_foreign_shared_images_rejected",
    "finite_native_failure_order",
    "duplicate_plans_rejected"
  ]
}
```

Status: audit 1 FAILED before R76; audit 2 FAILED on R76 declarations; no theorem accepted; both permitted invocations consumed. Primary has frozen this handoff; no third audit is permitted under R76.

## Exact audit 2 byte assembly (authoritative joining code)

The source slices include original blank lines. There are no implicit separator newlines. `SourceInternalChoiceR76` already includes its closing namespace, so do not append another closing namespace after the final segment. The following code reconstructs 35050 bytes with SHA-256 `bbe5b3a4f36dfc81c9ac40d696b447cbdb4c4b7170af4a00f92258baf3ecd033`; it does not invoke Lean. `m` is precisely the JSON object in the audit 2 proposal above.

```python
from pathlib import Path
import hashlib
parts = ['import Std\n']
previous = None
for d in m['segments']:
    namespace = Path(d['path']).stem
    if namespace != previous and previous is not None:
        parts.append('end YulangClosure.' + previous + '\n')
    if namespace == 'OccurrenceQualifiedConsumerR66' and namespace != previous:
        parts.append('namespace YulangClosure.OccurrenceQualifiedConsumerR66\nopen ProviderNativeContextR57\n')
    lines = Path(d['path']).read_text().splitlines(keepends=True)
    piece = ''.join(lines[d['first_line'] - 1:d['last_line']])
    assert hashlib.sha256(piece.encode()).hexdigest() == d['slice_sha256']
    parts.append(piece)
    previous = namespace
parts.append('\nset_option pp.universes true\nset_option pp.width 140\n')
for name in m['theorems']:
    parts.append(f'#check @YulangClosure.SourceInternalChoiceR76.{name}\n#print axioms YulangClosure.SourceInternalChoiceR76.{name}\n')
audit_stdin = ''.join(parts).encode()
assert len(audit_stdin) == 35050
assert hashlib.sha256(audit_stdin).hexdigest() == 'bbe5b3a4f36dfc81c9ac40d696b447cbdb4c4b7170af4a00f92258baf3ecd033'
```


## Audit 2 receipt — primary authorized final invocation

- Input: 35050 bytes, SHA-256 `bbe5b3a4f36dfc81c9ac40d696b447cbdb4c4b7170af4a00f92258baf3ecd033`.
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; command `-j1 -M1024 --stdin`; `LEAN_NUM_THREADS=1`; cwd `notes/theory/lean`; timeout 120s.
- Exit: `1`; timed out: `False`; elapsed seconds: `7.905`.
- stdout bytes: `31308`; SHA-256 `d0f9f8126f850cb373488abd6a49c0fc590f66c42c9d4350fff63a9fa50d32aa`.
- stderr bytes: `0`; SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### stdout (verbatim)

```text
<stdin>:502:4: error: unsolved goals
case neg
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c : Origin S T
f : Formal (Key S T) T
hf : s.formals[c.registration]? = some f
eligible : ¬(f.role = NativeRole.computation ∧ f.owner = target)
⊢ (Except.ok none).toOption = some none
<stdin>:500:27: warning: This simp argument is unused:
  ite_true

Hint: Omit it from the simp argument list.
  [apply] simp only [eligible]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:517:16: error: unsolved goals
case cons.error
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
out : List (Origin S T)
c : Origin S T
rest : List (Origin S T)
ih :
  ∀ (selected : List (Origin S T)),
    walk s target component rest selected = Except.ok out →
      ∃ rows,
        List.mapM (fun c => (visit s target component c).toOption) rest = some rows ∧
          selected ++ List.filterMap id rows = out
selected : List (Origin S T)
err : Failure
hv : visit s target component c = Except.error err
accepted :
  (do
      let found ← Except.error err
      match found with
        | none => walk s target component rest selected
        | some chosen =>
          match selected with
          | [] => walk s target component rest [chosen]
          | head :: tail => Except.error (Failure.secondOrigin c.registration)) =
    Except.ok out
⊢ ∃ rows,
    List.mapM (fun c => (visit s target component c).toOption) (c :: rest) = some rows ∧
      selected ++ List.filterMap id rows = out
<stdin>:522:10: error: Type mismatch: After simplification, term
  accepted
 has type
  @Eq (Except Failure (List (Origin S T)))
    (do
      let found ← Except.ok none
      match found with
        | none => walk s target component rest selected
        | some chosen =>
          match selected with
          | [] => walk s target component rest [chosen]
          | head :: tail => Except.error (Failure.secondOrigin c.registration))
    (Except.ok out)
but is expected to have type
  @Eq (Except Failure (List (Origin S T))) (walk s target component rest selected) (Except.ok out)
<stdin>:525:8: error: unsolved goals
case cons.ok.none.refine_1
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
out : List (Origin S T)
c : Origin S T
rest : List (Origin S T)
ih :
  ∀ (selected : List (Origin S T)),
    walk s target component rest selected = Except.ok out →
      ∃ rows,
        List.mapM (fun c => (visit s target component c).toOption) rest = some rows ∧
          selected ++ List.filterMap id rows = out
selected : List (Origin S T)
accepted : walk s target component (c :: rest) selected = Except.ok out
hv : visit s target component c = Except.ok none
tail : walk s target component rest selected = Except.ok out
rows : List (Option (Origin S T))
read : List.mapM (fun c => (visit s target component c).toOption) rest = some rows
equal : selected ++ List.filterMap id rows = out
⊢ ((Except.ok none).toOption.bind fun __do_lift => some (__do_lift :: rows)) = some (none :: rows)
<stdin>:531:12: error: Type mismatch: After simplification, term
  accepted
 has type
  @Eq (Except Failure (List (Origin S T)))
    (do
      let found ← Except.ok (some chosen)
      match found with
        | none => walk s target component rest []
        | some chosen => walk s target component rest [chosen])
    (Except.ok out)
but is expected to have type
  @Eq (Except Failure (List (Origin S T))) (walk s target component rest [chosen]) (Except.ok out)
<stdin>:534:10: error: unsolved goals
case cons.ok.some.nil.refine_1
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
out : List (Origin S T)
c : Origin S T
rest : List (Origin S T)
ih :
  ∀ (selected : List (Origin S T)),
    walk s target component rest selected = Except.ok out →
      ∃ rows,
        List.mapM (fun c => (visit s target component c).toOption) rest = some rows ∧
          selected ++ List.filterMap id rows = out
chosen : Origin S T
hv : visit s target component c = Except.ok (some chosen)
accepted : walk s target component (c :: rest) [] = Except.ok out
tail : walk s target component rest [chosen] = Except.ok out
rows : List (Option (Origin S T))
read : List.mapM (fun c => (visit s target component c).toOption) rest = some rows
equal : [chosen] ++ List.filterMap id rows = out
⊢ ((Except.ok (some chosen)).toOption.bind fun __do_lift => some (__do_lift :: rows)) = some (some chosen :: rows)
<stdin>:536:31: error: unsolved goals
case cons.ok.some.cons
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
out : List (Origin S T)
c : Origin S T
rest : List (Origin S T)
ih :
  ∀ (selected : List (Origin S T)),
    walk s target component rest selected = Except.ok out →
      ∃ rows,
        List.mapM (fun c => (visit s target component c).toOption) rest = some rows ∧
          selected ++ List.filterMap id rows = out
chosen : Origin S T
hv : visit s target component c = Except.ok (some chosen)
previous : Origin S T
others : List (Origin S T)
accepted :
  (do
      let found ← Except.ok (some chosen)
      match found with
        | none => walk s target component rest (previous :: others)
        | some chosen => Except.error (Failure.secondOrigin c.registration)) =
    Except.ok out
⊢ ∃ rows,
    List.mapM (fun c => (visit s target component c).toOption) (c :: rest) = some rows ∧
      previous :: others ++ List.filterMap id rows = out
<stdin>:556:13: error: unexpected token 'matches'; expected '(', ':=', '|' or term
<stdin>:545:14: error: unsolved goals
case error
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c : Origin S T
err : Failure
hw : walk s target component s.constructions [] = Except.error err
accepted :
  (do
      let choices ← Except.error err
      match choices with
        | [c] => Except.ok c
        | x => Except.error Failure.noOrigin) =
    Except.ok c
⊢ OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c
<stdin>:548:10: error: unsolved goals
case ok.nil
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c : Origin S T
hw : walk s target component s.constructions [] = Except.ok []
accepted :
  (do
      let choices ← Except.ok []
      match choices with
        | [c] => Except.ok c
        | x => Except.error Failure.noOrigin) =
    Except.ok c
⊢ OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c
<stdin>:551:26: error: unsolved goals
case ok.cons.cons
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c chosen extra : Origin S T
others : List (Origin S T)
hw : walk s target component s.constructions [] = Except.ok (chosen :: extra :: others)
accepted :
  (do
      let choices ← Except.ok (chosen :: extra :: others)
      match choices with
        | [c] => Except.ok c
        | x => Except.error Failure.noOrigin) =
    Except.ok c
⊢ OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c
<stdin>:553:37: error: Type mismatch: After simplification, term
  accepted
 has type
  (do
      let choices ← Except.ok [chosen]
      match choices with
        | [c] => Except.ok c
        | x => Except.error Failure.noOrigin) =
    Except.ok c
but is expected to have type
  chosen = c
<stdin>:556:13: error: Missing cases:
<stdin>:572:86: error: unsolved goals
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c : Origin S T
rest selected : List (Origin S T)
malformed : visit s target component c = Except.error (Failure.recipe c.registration)
⊢ (do
      let found ← Except.error (Failure.recipe c.registration)
      match found with
        | none => walk s target component rest selected
        | some chosen =>
          match selected with
          | [] => walk s target component rest [chosen]
          | head :: tail => Except.error (Failure.secondOrigin c.registration)) =
    Except.error (Failure.recipe c.registration)
<stdin>:578:104: error: unsolved goals
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
target : Key S T
component : Nat
c chosen previous : Origin S T
rest others : List (Origin S T)
matched : visit s target component c = Except.ok (some chosen)
⊢ (do
      let found ← Except.ok (some chosen)
      match found with
        | none => walk s target component rest (previous :: others)
        | some chosen => Except.error (Failure.secondOrigin c.registration)) =
    Except.error (Failure.secondOrigin c.registration)
<stdin>:709:75: error: failed to synthesize
  Decidable
    (foreignOrigin.function = fixtureConstruction.function ∧
      foreignOrigin.entryEffect = fixtureConstruction.entryEffect ∧
        orderedSelection foreignSource (Key.source 1) 20 = Except.error Failure.noOrigin)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
<stdin>:714:88: error: unexpected identifier; expected '}'
<stdin>:721:54: error: failed to synthesize
  Decidable
    (orderedSelection earlierBadSource (Key.source 1) 20 = Except.error (Failure.recipe 1) ∧
      orderedSelection
          (let __src := earlierBadSource;
          { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
            schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
            occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
            constructions := [fixtureConstruction, fixtureConstruction, foreignOrigin],
            permissions := __src.permissions, receipts := __src.receipts, plans := __src.plans,
            recipes := __src.recipes, admittedFacts := __src.admittedFacts, componentTerms := __src.componentTerms,
            termViews := __src.termViews })
          (Key.source 1) 20 =
        Except.error (Failure.secondOrigin 0))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
<stdin>:733:0: error: Unknown option `pp.width`
@YulangClosure.SourceInternalChoiceR76.visit_agrees : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (target : YulangClosure.ProviderNativeContextR57.Key S T) (component : Nat)
  (c : YulangClosure.SourceInternalChoiceR76.Origin S T),
  Eq.{1} (Except.toOption.{0, 0} (YulangClosure.SourceInternalChoiceR76.visit s target component c))
    (match getElem?.{0, 0, 0} s.formals c.registration with
    | none.{0} => some.{0} none.{0}
    | some.{0} f =>
      ite.{1} (Eq.{1} f.role YulangClosure.SourceInternalContextR55.NativeRole.computation ∧ Eq.{1} f.owner target)
        (do
          let recipe ←
            YulangClosure.SourceInternalContextR55.unique
                (fun r => decide (Eq.{1} r.formalRegistration (some.{0} c.registration))) s.recipes
          some.{0} (ite.{1} (Eq.{1} recipe.rootComponent component) (some.{0} c) none.{0}))
        (some.{0} none.{0}))
'YulangClosure.SourceInternalChoiceR76.visit_agrees' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.walk_accounts_for_all : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (target : YulangClosure.ProviderNativeContextR57.Key S T) (component : Nat)
  (origins selected out : List.{0} (YulangClosure.SourceInternalChoiceR76.Origin S T)),
  Eq.{1} (YulangClosure.SourceInternalChoiceR76.walk s target component origins selected) (Except.ok.{0, 0} out) →
    Exists.{1} fun rows =>
      Eq.{1}
          (List.mapM.{0, 0, 0}
            (fun c => Except.toOption.{0, 0} (YulangClosure.SourceInternalChoiceR76.visit s target component c))
            origins)
          (some.{0} rows) ∧
        Eq.{1} (HAppend.hAppend.{0, 0, 0} selected (List.filterMap.{0, 0} id.{1} rows)) out
'YulangClosure.SourceInternalChoiceR76.walk_accounts_for_all' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.ordered_selection_agrees : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (target : YulangClosure.ProviderNativeContextR57.Key S T) (component : Nat)
  (c : YulangClosure.SourceInternalChoiceR76.Origin S T),
  Eq.{1} (YulangClosure.SourceInternalChoiceR76.orderedSelection s target component) (Except.ok.{0, 0} c) →
    Eq.{1} (YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection s target component) (some.{0} c)
'YulangClosure.SourceInternalChoiceR76.ordered_selection_agrees' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.malformed_recipe_first : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (target : YulangClosure.ProviderNativeContextR57.Key S T) (component : Nat)
  (c : YulangClosure.SourceInternalChoiceR76.Origin S T)
  (rest selected : List.{0} (YulangClosure.SourceInternalChoiceR76.Origin S T)),
  Eq.{1} (YulangClosure.SourceInternalChoiceR76.visit s target component c)
      (Except.error.{0, 0} (YulangClosure.SourceInternalChoiceR76.Failure.recipe c.registration)) →
    Eq.{1} (YulangClosure.SourceInternalChoiceR76.walk s target component (List.cons.{0} c rest) selected)
      (Except.error.{0, 0} (YulangClosure.SourceInternalChoiceR76.Failure.recipe c.registration))
'YulangClosure.SourceInternalChoiceR76.malformed_recipe_first' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.second_origin_first : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (target : YulangClosure.ProviderNativeContextR57.Key S T) (component : Nat)
  (c chosen previous : YulangClosure.SourceInternalChoiceR76.Origin S T)
  (rest others : List.{0} (YulangClosure.SourceInternalChoiceR76.Origin S T)),
  Eq.{1} (YulangClosure.SourceInternalChoiceR76.visit s target component c) (Except.ok.{0, 0} (some.{0} chosen)) →
    Eq.{1}
      (YulangClosure.SourceInternalChoiceR76.walk s target component (List.cons.{0} c rest)
        (List.cons.{0} previous others))
      (Except.error.{0, 0} (YulangClosure.SourceInternalChoiceR76.Failure.secondOrigin c.registration))
'YulangClosure.SourceInternalChoiceR76.second_origin_first' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.choice_three_premises : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (u : YulangClosure.SourceInternalContextR55.Use Nat (YulangClosure.ProviderNativeContextR57.Key S T))
  (receiving target : YulangClosure.ProviderNativeContextR57.Key S T)
  (c : YulangClosure.SourceInternalChoiceR76.Choice s u receiving target),
  Eq.{1} ((YulangClosure.SourceInternalContextR55.internalInputs s).plan (YulangClosure.SourceInternalContextR55.use u))
      (some.{0} (YulangClosure.SourceInternalContextR55.plan c.plan)) ∧
    Eq.{1} (YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent)
        (some.{0} c.origin) ∧
      Eq.{1} (getElem?.{0, 0, 0} s.parameterRecipes c.formal.recipePosition) (some.{0} c.formal.parameter)
'YulangClosure.SourceInternalChoiceR76.choice_three_premises' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
@YulangClosure.SourceInternalChoiceR76.choice_applies_r66 : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (inventory : YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory S T)
  (u : YulangClosure.SourceInternalContextR55.Use Nat (YulangClosure.ProviderNativeContextR57.Key S T))
  (receiving target : YulangClosure.ProviderNativeContextR57.Key S T)
  (c : YulangClosure.SourceInternalChoiceR76.Choice s u receiving target),
  Eq.{1}
      ((YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan
        (YulangClosure.SourceInternalContextR55.use u))
      (some.{0} (YulangClosure.SourceInternalContextR55.plan c.plan)) ∧
    Eq.{1} (YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent)
        (some.{0} c.origin) ∧
      Eq.{1} (getElem?.{0, 0, 0} s.parameterRecipes (YulangClosure.SourceInternalContextR55.formal c.formal).recipe)
        (some.{0} (YulangClosure.SourceInternalContextR55.formal c.formal).parameter)
'YulangClosure.SourceInternalChoiceR76.choice_applies_r66' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
@YulangClosure.SourceInternalChoiceR76.exact_use_unique : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (u : YulangClosure.SourceInternalContextR55.Use Nat (YulangClosure.ProviderNativeContextR57.Key S T))
  (receiving target : YulangClosure.ProviderNativeContextR57.Key S T)
  (c : YulangClosure.SourceInternalChoiceR76.Choice s u receiving target)
  (p : YulangClosure.SourceInternalContextR55.Plan Nat (YulangClosure.ProviderNativeContextR57.Key S T) T),
  Membership.mem.{0, 0} s.plans p →
    Eq.{1} (YulangClosure.SourceInternalContextR55.use p.use) (YulangClosure.SourceInternalContextR55.use u) →
      Eq.{1} p c.plan
'YulangClosure.SourceInternalChoiceR76.exact_use_unique' depends on axioms: [propext]
@YulangClosure.SourceInternalChoiceR76.construction_certifies : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (inventory : YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory S T)
  (u : YulangClosure.SourceInternalContextR55.Use Nat (YulangClosure.ProviderNativeContextR57.Key S T))
  (receiving target : YulangClosure.ProviderNativeContextR57.Key S T),
  match YulangClosure.SourceInternalChoiceR76.construct s u receiving target with
  | none.{0} => True
  | some.{0} c =>
    Eq.{1}
        ((YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan
          (YulangClosure.SourceInternalContextR55.use u))
        (some.{0} (YulangClosure.SourceInternalContextR55.plan c.plan)) ∧
      Eq.{1} (YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent)
          (some.{0} c.origin) ∧
        Eq.{1} (getElem?.{0, 0, 0} s.parameterRecipes (YulangClosure.SourceInternalContextR55.formal c.formal).recipe)
          (some.{0} (YulangClosure.SourceInternalContextR55.formal c.formal).parameter)
'YulangClosure.SourceInternalChoiceR76.construction_certifies' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
YulangClosure.SourceInternalChoiceR76.finite_constructs_choice : Eq.{1}
  (Option.isSome.{0} YulangClosure.SourceInternalChoiceR76.fixtureChoice) true
'YulangClosure.SourceInternalChoiceR76.finite_constructs_choice' depends on axioms: [propext]
YulangClosure.SourceInternalChoiceR76.finite_bad_inventories_reject : Eq.{1}
    (Option.isSome.{0}
      (YulangClosure.SourceInternalChoiceR76.construct
        (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
        { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
          schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
          occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
          constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
          plans :=
            HAppend.hAppend.{0, 0, 0} YulangClosure.SourceInternalChoiceR76.fixture.plans
              YulangClosure.SourceInternalChoiceR76.fixture.plans,
          recipes := __src.recipes, admittedFacts := __src.admittedFacts, componentTerms := __src.componentTerms,
          termViews := __src.termViews })
        YulangClosure.SourceInternalChoiceR76.fixtureUse (YulangClosure.ProviderNativeContextR57.Key.source 10)
        (YulangClosure.ProviderNativeContextR57.Key.source 1)))
    false ∧
  Eq.{1}
      (Option.isSome.{0}
        (YulangClosure.SourceInternalChoiceR76.construct
          (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
          { artifact := __src.artifact, formals := __src.formals, parameterRecipes := List.nil.{0},
            schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
            occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
            constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
            plans := __src.plans, recipes := __src.recipes, admittedFacts := __src.admittedFacts,
            componentTerms := __src.componentTerms, termViews := __src.termViews })
          YulangClosure.SourceInternalChoiceR76.fixtureUse (YulangClosure.ProviderNativeContextR57.Key.source 10)
          (YulangClosure.ProviderNativeContextR57.Key.source 1)))
      false ∧
    Eq.{1}
        (Option.isSome.{0}
          (YulangClosure.SourceInternalChoiceR76.construct
            (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
            { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
              schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
              occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
              constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
              plans := __src.plans, recipes := List.nil.{0}, admittedFacts := __src.admittedFacts,
              componentTerms := __src.componentTerms, termViews := __src.termViews })
            YulangClosure.SourceInternalChoiceR76.fixtureUse (YulangClosure.ProviderNativeContextR57.Key.source 10)
            (YulangClosure.ProviderNativeContextR57.Key.source 1)))
        false ∧
      Eq.{1}
          (Option.isSome.{0}
            (YulangClosure.SourceInternalChoiceR76.construct
              (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
              { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
                schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
                occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
                constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
                plans := __src.plans,
                recipes :=
                  HAppend.hAppend.{0, 0, 0} YulangClosure.SourceInternalChoiceR76.fixture.recipes
                    YulangClosure.SourceInternalChoiceR76.fixture.recipes,
                admittedFacts := __src.admittedFacts, componentTerms := __src.componentTerms,
                termViews := __src.termViews })
              YulangClosure.SourceInternalChoiceR76.fixtureUse (YulangClosure.ProviderNativeContextR57.Key.source 10)
              (YulangClosure.ProviderNativeContextR57.Key.source 1)))
          false ∧
        Eq.{1}
            (Option.isSome.{0}
              (YulangClosure.SourceInternalChoiceR76.construct
                (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
                { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
                  schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
                  occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
                  constructions :=
                    HAppend.hAppend.{0, 0, 0} YulangClosure.SourceInternalChoiceR76.fixture.constructions
                      YulangClosure.SourceInternalChoiceR76.fixture.constructions,
                  permissions := __src.permissions, receipts := __src.receipts, plans := __src.plans,
                  recipes := __src.recipes, admittedFacts := __src.admittedFacts,
                  componentTerms := __src.componentTerms, termViews := __src.termViews })
                YulangClosure.SourceInternalChoiceR76.fixtureUse (YulangClosure.ProviderNativeContextR57.Key.source 10)
                (YulangClosure.ProviderNativeContextR57.Key.source 1)))
            false ∧
          Eq.{1}
              (Option.isSome.{0}
                (YulangClosure.SourceInternalChoiceR76.construct
                  (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
                  { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
                    schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
                    occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
                    constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
                    plans :=
                      List.map.{0, 0}
                        (fun p =>
                          { use := p.use, sourceOwner := p.sourceOwner, targetOwner := p.targetOwner,
                            targetRootComponent := 900, useValueComponent := p.useValueComponent,
                            targetRoot := p.targetRoot, useValue := p.useValue })
                        YulangClosure.SourceInternalChoiceR76.fixture.plans,
                    recipes := __src.recipes, admittedFacts := __src.admittedFacts,
                    componentTerms := __src.componentTerms, termViews := __src.termViews })
                  YulangClosure.SourceInternalChoiceR76.fixtureUse
                  (YulangClosure.ProviderNativeContextR57.Key.source 10)
                  (YulangClosure.ProviderNativeContextR57.Key.source 1)))
              false ∧
            Eq.{1}
              (Option.isSome.{0}
                (YulangClosure.SourceInternalChoiceR76.construct
                  (have __src := YulangClosure.SourceInternalChoiceR76.fixture;
                  { artifact := __src.artifact, formals := __src.formals,
                    parameterRecipes :=
                      List.cons.{0} (YulangClosure.ProviderNativeContextR57.Key.source 999) List.nil.{0},
                    schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
                    occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
                    constructions := __src.constructions, permissions := __src.permissions, receipts := __src.receipts,
                    plans := __src.plans, recipes := __src.recipes, admittedFacts := __src.admittedFacts,
                    componentTerms := __src.componentTerms, termViews := __src.termViews })
                  YulangClosure.SourceInternalChoiceR76.fixtureUse
                  (YulangClosure.ProviderNativeContextR57.Key.source 10)
                  (YulangClosure.ProviderNativeContextR57.Key.source 1)))
              false
'YulangClosure.SourceInternalChoiceR76.finite_bad_inventories_reject' depends on axioms: [propext]
YulangClosure.SourceInternalChoiceR76.finite_foreign_shared_images_rejected : Eq.{1}
    YulangClosure.SourceInternalChoiceR76.foreignOrigin.function
    YulangClosure.ProviderNativeContextR57.fixtureConstruction.function ∧
  Eq.{1} YulangClosure.SourceInternalChoiceR76.foreignOrigin.entryEffect
      YulangClosure.ProviderNativeContextR57.fixtureConstruction.entryEffect ∧
    Eq.{1}
      (YulangClosure.SourceInternalChoiceR76.orderedSelection YulangClosure.SourceInternalChoiceR76.foreignSource
        (YulangClosure.ProviderNativeContextR57.Key.source 1) 20)
      (Except.error.{0, 0} YulangClosure.SourceInternalChoiceR76.Failure.noOrigin)
'YulangClosure.SourceInternalChoiceR76.finite_foreign_shared_images_rejected' depends on axioms: [propext, sorryAx.{u}]
YulangClosure.SourceInternalChoiceR76.finite_native_failure_order : Eq.{1}
    (YulangClosure.SourceInternalChoiceR76.orderedSelection YulangClosure.SourceInternalChoiceR76.earlierBadSource
      (YulangClosure.ProviderNativeContextR57.Key.source 1) 20)
    (Except.error.{0, 0} (YulangClosure.SourceInternalChoiceR76.Failure.recipe 1)) ∧
  Eq.{1}
    (YulangClosure.SourceInternalChoiceR76.orderedSelection
      (have __src := YulangClosure.SourceInternalChoiceR76.earlierBadSource;
      { artifact := __src.artifact, formals := __src.formals, parameterRecipes := __src.parameterRecipes,
        schedules := __src.schedules, sources := __src.sources, sourceOwners := __src.sourceOwners,
        occupiedDomains := __src.occupiedDomains, retainedRegistrations := __src.retainedRegistrations,
        constructions :=
          List.cons.{0} YulangClosure.ProviderNativeContextR57.fixtureConstruction
            (List.cons.{0} YulangClosure.ProviderNativeContextR57.fixtureConstruction
              (List.cons.{0} YulangClosure.SourceInternalChoiceR76.foreignOrigin List.nil.{0})),
        permissions := __src.permissions, receipts := __src.receipts, plans := __src.plans, recipes := __src.recipes,
        admittedFacts := __src.admittedFacts, componentTerms := __src.componentTerms, termViews := __src.termViews })
      (YulangClosure.ProviderNativeContextR57.Key.source 1) 20)
    (Except.error.{0, 0} (YulangClosure.SourceInternalChoiceR76.Failure.secondOrigin 0))
'YulangClosure.SourceInternalChoiceR76.finite_native_failure_order' depends on axioms: [propext, sorryAx.{u}]
@YulangClosure.SourceInternalChoiceR76.duplicate_plans_rejected : ∀ {S T : Type} [inst : DecidableEq.{1} S]
  [inst_1 : DecidableEq.{1} T] (s : YulangClosure.SourceInternalChoiceR76.Source S T)
  (u : YulangClosure.SourceInternalContextR55.Use Nat (YulangClosure.ProviderNativeContextR57.Key S T))
  (receiving target : YulangClosure.ProviderNativeContextR57.Key S T)
  (first second : YulangClosure.SourceInternalContextR55.Plan Nat (YulangClosure.ProviderNativeContextR57.Key S T) T)
  (rest :
    List.{0} (YulangClosure.SourceInternalContextR55.Plan Nat (YulangClosure.ProviderNativeContextR57.Key S T) T)),
  Eq.{1}
      (List.filter.{0}
        (fun p =>
          decide
            (Eq.{1} (YulangClosure.SourceInternalContextR55.use p.use) (YulangClosure.SourceInternalContextR55.use u)))
        s.plans)
      (List.cons.{0} first (List.cons.{0} second rest)) →
    Eq.{1} (YulangClosure.SourceInternalChoiceR76.construct s u receiving target) none.{0}
'YulangClosure.SourceInternalChoiceR76.duplicate_plans_rejected' depends on axioms: [propext, Quot.sound.{u}]
```

### stderr (verbatim)

```text
```
