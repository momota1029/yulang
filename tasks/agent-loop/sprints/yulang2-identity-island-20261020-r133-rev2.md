# Sprint Yulang2 identity island — R133 rev2

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**; rev1 is preserved as BLOCKING history; no R133 code lease is active.
Branch: `research/simple-sub-intrusion`; repository HEAD remains
`9fab033a27390ac12f7553a9d6af11a82ad66e1b` with the reviewed, uncommitted R132
candidate and failure receipts in the worktree.

Original user goal remains proof-backed Yulang inference/evaluator
implementation and the broadest practical execution of the unchanged Yulang2
Web demo sample. R133 is a new, smaller exact source projection after R132's
four-result contract failed at the unsupported braced countdown syntax. It does
not close or redefine the larger goal.

## Fixed source and oracle

Yulang2 sample:
`/home/momota1029/rust/yulang2-web-case/examples/web-playground.yu`, SHA-256
`be076ab26780de6a5f6b75b75a11abec351114ec5fa3b6edfcbacd15e02fb284`.

The 210-byte fixture is the exact block from
`// one generalized function used at three types` through its three bare
observations `int_identity`, `bool_identity`, and `string_identity`, preserving
the source block's trailing whitespace. Expected selected-definition values
come from the unchanged Yulang2 Web oracle `runs_web_playground_example`:
`int_identity -> 7`, `bool_identity -> true`, and
`string_identity -> "ok"`. The fixture projection SHA-256 is
`b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f`.

This projection deliberately leaves the following original sample code out of
R133: brace-form countdown, factorial, variants, lists, records/methods,
standard modules, ranges and nondeterminism. R132 rev3 and its 388-byte
combined fixture remain the record of the countdown syntax failure. R133 must
not translate the countdown to colon syntax, claim four results, or claim full
sample compatibility.

## Rev2 acceptance-matrix clarification

R133 explicitly supersedes only the live four-definition smoke case that R132
added for the combined fixture. Its four source/value pair remains preserved
as historical, non-executable evidence in the frozen R132 source/oracle,
implementation handoff, BLOCKING/CLEAN review history and closeout. The
countdown's authoritative expected value remains 8, but its executable
assertion is removed from the R133 smoke because Yulang3 rejects the exact
brace-form source. R133 replaces that live case with a separate exact
identity-only fixture and the three reviewed identity expectations above. This
is a new prospective acceptance matrix; it neither changes the Yulang2 oracle
nor claims R132 succeeded.

The implementation lease explicitly authorizes removing R132's added
yulang2Definitions loop/object from web/playground/smoke-test.mjs and replacing
it with the three identity-only selected-definition cases. It does not
authorize changing any pre-existing smoke source or expected value, or
deleting/rewriting the failed combined fixture. The failure stays discoverable
through its frozen hash and R132 closeout.

## Authority and fixed outcome

Keep the existing selected-definition API and provisional evaluator. Add no
language syntax/semantics, module-results API, WASM API, CLI behavior or
production authority. All original A/B, R64/R65 and other theorem, adoption,
source/native and production gates remain OPEN.

Outcome: make the exact generalized-identity block runnable as a Web example
and freeze smoke evidence for its three named values through the existing WASM
`run(source, definition, budget)` interface. The browser defaults to
`int_identity`; switching to old examples selects `main`; the input stays
editable. Existing examples and prior smoke expectations remain intact.

The broken R132 combined example option must be removed from the selector and
source map, but its file `web/playground/examples/yulang2-ordinary-islands.yu`
must remain byte-frozen as explicit unsupported-source evidence. Add a separate
`web/playground/examples/yulang2-identity-island.yu` fixture with the pinned
210-byte source. Do not delete the countdown expectation merely to turn the
old smoke green: R133 uses its own identity-only source and a distinct,
prospectively reviewed three-value acceptance matrix.

Success requires:

1. New fixture byte length and hash exactly match the source projection above.
2. Smoke reads the same fixture and obtains exactly `7\n`, `true\n`, and
   `"ok"\n` through the unchanged selected-definition API.
3. The Web selector exposes the identity-only example, starts on
   `int_identity`, and synchronizes the Run definition for the identity option
   and each prior example without breaking manual editing.
4. Existing example options, source strings, smoke oracles, and the R132
   unsupported countdown fixture remain intact.
5. A constructive source-to-consumer handoff states exact constructor, scheme,
   candidate-admission and evaluator premises. It does not prove arbitrary
   polymorphic soundness or theorem closure.
6. Both fresh final reviewers are CLEAN and the exact one-time Web/WASM command
   passes.

## Exact inputs and owner pins

R132 reviewed worktree candidate before R133 edits:

| Path | SHA-256 |
|---|---|
| `web/playground/index.html` | `638410726a7bb212dcd53e81fecee424a48b31455c0581a0955a6e975ea72eeb` |
| `web/playground/src/main.ts` | `2a9089a95b9b0a6a98ce74b2fb56dd05bd04fa6a6817e94e95a4a57151d90577` |
| `web/playground/smoke-test.mjs` | `2ab8ef396a33223601b606ac4c014c1bdb2d831fceddf2ad1ad571c2d8b2d599` |
| `web/playground/examples/yulang2-ordinary-islands.yu` | `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487` |
| `web/playground/package.json` | `ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf` |
| `web/playground/vite.config.ts` | `4f5df146b7d97875ab25521346845634a9fed911345355d3e6f2d77cbff58d69` |
| `tools/inference-playground/src/lib.rs` | `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` |
| `apps/yulang-wasm/Cargo.toml` | `c00101fa1b063622a9826a7971add7396e0f73b614d408f2e962a006799966f6` |
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-hir/src/shadow.rs` | `ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654` |
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850` |

Any mismatch, newly required owner or change to the frozen countdown evidence
stops before implementation. `web/playground/src/wasm` is generated by the
contracted build; no source edit there is authorized.

## Lanes and exact leases

**Constructive proof, `prover` (Sol/high), maximum 300 seconds:** write only
`notes/theory/2026-10-20-r133-identity-island.md` and
`tasks/agent-loop/inbox/20261020-r133-proof.md`. Trace the exact three uses
through retained local source, candidate constraints, scheme/FreshUse and
selected runtime values. Apply R132's useful identity evidence only where exact
premises match. Keep all parent gates OPEN. No commands or implementation edits.

**Implementation, `implementer` (Luna/high), maximum 180 seconds, after
prospective spec review is CLEAN:** write only
`web/playground/examples/yulang2-identity-island.yu`,
`web/playground/index.html`, `web/playground/src/main.ts`,
`web/playground/smoke-test.mjs`, and
`tasks/agent-loop/inbox/20261020-r133-implementation.md`. Retire only the
broken selector/map entry, preserve its old fixture file, add the exact
identity-only option and three selected-value smoke cases. Preserve every
existing option and prior oracle. No tests/builds/formatters/compiler/CLI/Git
during implementation.

Two fresh final reviews maximum (M2): independent compiler/source and
regression reviewers; maximum 180 seconds combined. Review all new and changed
hashes plus exact unchanged owner pins. No producer self-review.

After every handoff is frozen, both final reviews are CLEAN and Luna confirms
the exact changed-path inventory, run exactly once:

```sh
timeout 240s npm --prefix web/playground run check
```

Stop on any failure; no retry in R133. This one check builds WASM/browser and
runs the selected-value smoke. It does not execute the full demo or prove
general inference correctness.

## Resources and stop conditions

Fresh R133 envelope: **1,200 seconds**: inventory 120, prospective review 120,
proof 300, implementation 180, final reviews 180, verification 240, closeout
60. One heavy process maximum; zero Astra. Preserve R132's UNKNOWN 360-second
implementation reservation and R114's separate unreconciled 360 seconds; none
is transferred or reset. R132's two execution attempts and failed outcome stay
in its closeout and are not reclassified as R133 checks.

Stop on changed owner pin, source extraction mismatch, non-CLEAN pre-review,
candidate inference/source-form mismatch, any need to rewrite the exact source,
semantic/API expansion, failed command, or exhausted stage. No separate syntax
work is bundled. Luna alone owns exact leases, fresh reviewer assignment,
closeout, staging, commit and non-forced push.
