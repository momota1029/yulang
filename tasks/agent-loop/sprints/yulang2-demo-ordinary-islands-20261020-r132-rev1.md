# Sprint Yulang2 demo ordinary islands — R132 rev1

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**; no implementation lease is active.
Branch: `research/simple-sub-intrusion`; baseline
`9fab033a27390ac12f7553a9d6af11a82ad66e1b`.
Original user goal: proof-backed Yulang inference/evaluator implementation and
the broadest practical execution of the unchanged Yulang2 Web demo sample.
This sprint covers the exact generalized-identity and countdown blocks through
the existing selected-definition API. It adds no language meaning, runtime
behavior, CLI/WASM API, or production authority.

## Fixed sample and oracle

Read-only Yulang2 sample:
`/home/momota1029/rust/yulang2-web-case/examples/web-playground.yu`, SHA-256
`be076ab26780de6a5f6b75b75a11abec351114ec5fa3b6edfcbacd15e02fb284`.
The separate Yulang2 checkout is read-only and outside all leases.

The frozen 388-byte fixture is the unchanged pair of blocks for the generalized
identity at three types and recursive countdown, joined by a blank line:

`// one generalized function used at three types` through `string_identity`,
then `// recursive function with inferred argument and result types` through
`countdown_result`. Fixture SHA-256:
`f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`.
Its output oracle is confirmed by the Yulang2 Web test
`crates/yulang-wasm/src/lib.rs::runs_web_playground_example`, source hash
`41ac039cb915effac5985456ef9c9875d5ad6ee1afec69c91587cd5633cc5b82`:
`int_identity -> 7`, `bool_identity -> true`, `string_identity -> "ok"`,
`countdown_result -> 8`.

The complete 19-result sample is not claimed by this sprint. Arithmetic,
lists, records/methods, tagged values, standard modules, ranges and
nondeterminism have separate source/consumer and authority gaps. Do not rewrite
or annotate the two selected blocks to conceal those gaps.

## Existing authority and gate

- User's current broad implementation goal and
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` govern
  ordinary inference and proof direction.
- `notes/design/2026-10-04-inference-research-playgrounds.md` permits bounded
  experimental source/evaluator work, never production promotion.
- `tools/inference-playground/README.md` describes the current provisional
  selected-definition evaluator and its limits.
- `notes/design/2026-10-16-module-expression-source-owner.md` remains
  authoritative: top-level expression results are discarded, `--run` remains
  selected-definition, and this sprint adds no module-result rule/API.
- Preserve all Simple-sub/evaluator A/B, R85 adoption, six effect-hygiene,
  source-law, R99 and production gates as OPEN.

## Original outcome and success evidence

Outcome: make the exact two existing Yulang2 source islands easy to load in the
Yulang3 browser playground, and freeze executable evidence that candidate
inference plus the current evaluator produce the four corresponding values.
The browser keeps its existing Run-definition control; the example explains
the four valid definition names and starts on `int_identity`.

Success requires all of the following:

1. The shared `.yu` fixture bytes match the pinned 388-byte source fragment.
2. Existing WASM `run(source, definition, budget)` returns exactly `7\n`,
   `true\n`, `"ok"\n`, and `8\n` for the four definitions, in no alternate
   or fabricated `main` source.
3. The Web example loads that same fixture and makes the four selectors
   discoverable while preserving all existing examples and selected-definition
   behavior.
4. A constructive source-to-consumer handoff traces the exact binding/use,
   scheme/generalization, runtime schedule and result consumers, states its
   premises, and applies any useful lemma to its original open parent. The
   handoff must not claim general soundness, principality, or full demo support.
5. One authorized Web/WASM smoke command passes after independent review.

Current baseline evidence: the Web source has no exact Yulang2 identity/countdown
example; `execute` and WASM `run` already expose selected definitions. No exact
combined-fragment execution receipt exists.

## Two lanes and exact leases

**Constructive proof, `prover` (Sol/high), maximum 420 seconds:** inspect the
exact fixture and the actual constructor-to-consumer path. Trace three distinct
uses of `identity` at integer, Boolean and string values, plus countdown's
recursive conditional, through retained local source, candidate constraints,
scheme/FreshUse owners, runtime code/schedule and selected result. State the
exact source lemma and hypotheses. Apply it to R65/R64 only where the owner
premise actually matches; leave both gates OPEN otherwise. No compiler/tests,
source edits, Git, or production claims. Write only
`notes/theory/2026-10-20-r132-demo-ordinary-islands.md` and
`tasks/agent-loop/inbox/20261020-r132-proof.md`.

**Complementary source/falsifier lane, `researcher` (Sol/high), maximum 240
seconds:** independently inspect the exact syntax and relevant inference/runtime
owner routes; seek cross-use contamination, recursion/caching misrouting, or a
source-shape mismatch that could invalidate the proposed success claim. No
tests/builds/CLI, writes to implementation or proof paths, or Git. Write only
`tasks/agent-loop/inbox/20261020-r132-source-audit.md`.

**Implementation, `implementer` (Luna/high), maximum 360 seconds, only after
prospective spec review is CLEAN:** add the byte-exact sample fixture and wire it
into the existing browser example selector; document the four selected names;
extend the existing WASM smoke test to exercise all four values using the same
fixture and unchanged `run` API. Preserve every existing example and existing
Run-definition behavior. No compiler/HIR/solver/runtime/CLI/WASM API change,
no expectation rewrite, no other sample fragment, and no test/build/formatter/
compiler/CLI/Git command during implementation. Write only:

- `web/playground/examples/yulang2-ordinary-islands.yu`
- `web/playground/index.html`
- `web/playground/src/main.ts`
- `web/playground/smoke-test.mjs`
- `tasks/agent-loop/inbox/20261020-r132-implementation.md`

Fresh final review uses two reviewers maximum (M2): one compiler/source
reviewer for fixture/API/inference/evaluator correspondence and one regression
reviewer for the browser and existing example set. The producer cannot review.
Both inspect frozen hashes and exact dependency pins; both must be CLEAN before
the single verification command.

## Frozen owner pins

| Path | SHA-256 |
|---|---|
| `web/playground/index.html` | `a1e098252dfae29635180fb8c3ce611c0a9e29436e177f76f408d5e4d8dbc9e3` |
| `web/playground/src/main.ts` | `b6b33cb75aa76a701c6373335f1cd823a4d807f0a23fbbaf97b878adcfaaed55` |
| `web/playground/smoke-test.mjs` | `6071129b561c8cae9ab1b147aaf8dd87eb2a802b51f92b187076c34c2cf5fea2` |
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

Any changed pin or newly required owner stops before implementation. `web/playground`
paths previously leased to `/root/r114_web_example_impl` are released only by
its recorded STOPPED receipt; Luna is the sole successor lease owner.

## Verification, resources, stop and integration

After all handoffs are frozen, both final reviews are CLEAN, and Luna confirms
the exact path inventory, run once:

```sh
timeout 240s npm --prefix web/playground run check
```

One heavy build/smoke process maximum; no retry after failure. This smoke covers
the browser bundle and WASM execution, not the 19-result full Yulang2 sample,
all language semantics, or any proof parent. Tests are authorized only through
this command.

New envelope: 1,800 seconds maximum: inventory 120, prospective review 120,
proof 420, complementary source audit 240, implementation 360, final review
240, verification 240, closeout 60. Zero Astra. Preserve R114's 360 seconds as
unreconciled/unavailable; no budget reset or transfer. At most three current
workers plus Luna; existing UNKNOWN identities and quarantined leases remain
untouched. Stop on any changed owner, non-CLEAN prospective review, source-shape
mismatch, failed command, required API/semantic expansion, or exhausted stage.

Luna owns exact lease issuance, reviewer assignment/adjudication, current-state
and progress synchronization, explicit-path staging, full outbound-range
inspection, commit, and non-forced push. Pending question bundles remain
unstaged. Closeout records before/after sample coverage, exact hashes, proof
limitations, check, unverified remaining sample sections, resource remainder,
commit and push. Dispatcher returns at sprint end or any material blocker,
authority, dependency, lease, budget, or goal change.
