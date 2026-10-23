# R347 — K0 generated constraints and actual end-state adequacy

Status: **ADMITTED, revision 1**. Bounded source/native supplier only; no parent gate is closed by admission.
Branch: `research/simple-sub-intrusion`
Baseline HEAD and upstream at admission: `726edb1a3f81bc525ed93b7913dc300e268cd109`.
Primary: `/root` (Luna).
Sprint cap: **7,200 seconds**, no carryover: primary source lane 2,400; proof lane 3,000; fresh review 1,500; integration 300.

## Unchanged parent and current normative context

The parent remains the original Yulang2/Simple-sub source/native A/B objective, including its original quantifiers, source domain, accepted behavior and expected outputs. The original audit is `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256 `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

The newest whole-language semantics is `docs/yulang-whole-language-semantics-ja (1).tex`, SHA-256 `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`. It is the governing semantics context for this packet. Earlier TeX files and aligned audit rewrites are historical crosswalks. The bounded solver relation below is not the newest TeX's packet evidence-hole component `H`, world-indexed value/computation semantics, complete Call evidence, or whole-language system `Y_H`.

## One bounded outcome

Fix the authentic ordinary K0 source domain and algebra of R336 rev4 and the ordinary context premises of R337 J. Let `C_s` be the occurrence-indexed Value and Effect inequalities emitted by the authenticated K0 source schedule, including the Definition-root Link and all seven constructor families. Let `H₀(S)` denote exactly R341's independent interpretation of the actual completed native state S (physical directed bounds plus its precisely defined live-work/frame formulas). The subscript is only disambiguating notation; it does not change R341's definition.

For each authentic completed state S in the contracted domain, construct the exact kind-preserving row map and any required projection from native rows to source row support. Prove, or identify the first exact obstruction to, the projected solution correspondence:

```text
{ restrict_source(ρ) | ρ ⊨ H₀(S) } = { σ | σ ⊨ C_s }
```

The left-to-right inclusion is the reviewed R341 retention result, reused only under its stated premises. The packet's new target is the other inclusion: for every source assignment σ satisfying `C_s`, exhibit an extension to the actual native coordinates satisfying `H₀(S)`. Do not assume the row map is identity or injective; state its Value/Effect sort and every auxiliary coordinate. If exact equality requires a different mathematically justified projection, define and prove that relation before claiming correspondence.

The source lane must inventory every authentic source origin, including any cache suppression before `OwnerEmission`, and follow each generated or suppressed obligation to its exact final bound, surviving entailment, or live owner. It must cover the actual source schedule, ordinary worklist/replay, intrusion/finalization guards and the state at successful completion. Do not add missing constraints to `C_s` after seeing a discrepancy. A gap in an inventory, an unrealizable valuation, and an authentic source-qualified failure of the correspondence are separate outcomes.

## Evidence already available and exact dependencies

The relevant reviewed predecessors are reused only inside their named claims:

- R336 rev4 D0/D1: `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md`, SHA-256 `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
- R337 J: `notes/theory/2026-10-23-r337-k0-context-preservation.md`, SHA-256 `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62`.
- R338 state bridge and source census: SHA-256 `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0` and `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9`.
- R339 replay retirement and reviewed outcome: SHA-256 `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87` and `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701`.
- R341 retention proof, source census and accepted outcome: SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`, `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb`, and `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc`.
- R345 reviewed whole-frame retirement: proof, census and outcome SHA-256 `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df`, `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b`, and `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce`.
- R346 independently reviewed ordinary fixed-key replay coverage: contract, proof, census and outcome SHA-256 `7f2419fa4d589ec6bb7d8af769a3eeb94f5361332483321328a06c2558327391`, `f21a15eac621216366338ceeb454aec868554668a6cc4b8da903aa79d9d2fc7d`, `1179312d8230616a0ac5cda45a1c29f08012bba9327f2f3601bb3179cfb5fdfd`, and `25748200d206c375a2e450aff688f692a4bfc5537ef7ba3fdc953423006b6512`.

R341 establishes only the `H₀(S) ⇒ C_s` direction for its authentic K0 completed-state premises. R345 and R346 cover only their named retirement and ordinary fixed-key replay families. None supplies full N, all-source cache completeness, arbitrary K0 state reachability, `Y_H` certificate soundness, principal-package completeness, or original A/B closure.

## Source baseline and domain

The six primary solver owners are pinned at admission:

| Source | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |

Use exactly R336 rev4's authentic ordinary K0 constructors, finite Value preorder, Function port order/variance, Effect set algebra, and fixed row domain, plus R337 J and R341's stated completed-state predicate. Preserve the original source occurrence identity and separate it from row identity, memo identity, operation slots, completion stamps and runtime owners. Exclude annotations outside K0, local/recursive bindings, modules/imports, roles, operators, record/variant/tuple adaptation, Comp, operations/handlers, intrusion-producing experiments and non-ordinary origins unless the census proves they are authentic in the contracted domain. If an exclusion is reachable in the stated domain, do not silently keep the exclusion: stop and return the exact constructor and source path to Luna.

This is a bounded operational/algebraic correspondence for a source-to-solver path. It does not prove all Yulang source forms, runtime value/computation semantics, effect-safe complete Calls, whole-language theorem conditions Q1–Q8, `Qualified`/`CheckedExecutable` classifier completeness, `BuildLocal` construction completeness, principality, or any unrestricted binary decision procedure. `Pending` and `ResourceExhausted` remain distinct from `TypeError`.

## Lanes, exact leases and review

**Primary source lane — `/root`, 2,400 seconds.** Own this contract, the exact source census `notes/theory/2026-10-23-r347-k0-end-state-source-census.md`, the Luna outcome `tasks/agent-loop/sprints/r347-k0-end-state-adequacy-20261023-outcome.md`, and `tasks/agent-loop/current.json`. Trace source constructors and cache/suppression origins through actual consumers and completion. No compiler edits are authorized; disposition is `NO_SAFE_CODE_SLICE`.

**Proof lane — one `prover`, requested Sol/high, 3,000 seconds.** Exact write leases only:

- `notes/theory/2026-10-23-r347-k0-end-state-adequacy.md`
- `tasks/agent-loop/inbox/20261023-r347-k0-end-state-prover.md`

Prove the projected solution correspondence across the actual source origins, row transport, owner emission/suppression, ordinary propagation/replay and completion. Reuse the left-to-right direction from R341 under its unchanged premises. Freeze the precise first missing origin, finalization mutation, projection failure or authentic counterexample if the other direction cannot be established. The proof must not infer an entailment from a cache bit or completion marker.

After proof and census freeze and writer cessation, Luna assigns one fresh non-contributor `compiler_referee`, requested Sol/medium, 1,500 seconds, message-only. It checks both directions, the exact projection and all source/completion owners. Reserve 300 seconds for integration. No descendants, Astra, tests, builds, Cargo, executable probes, worker Git, or carryover. The three legacy UNKNOWN writers and their quarantined leases remain untouched; the single prover and later single reviewer fit the existing six-assignment limit.

Success is a genuinely smaller exact premise for original N/G or a source-qualified falsifier of this same correspondence. A coverage gap alone is not a compiler defect. Stop/replan only on a qualifying counterexample, pin or authority change, unresolved writer, material review finding, or the fixed resource cap. At closeout consult `next_action_selector`, record the residual OPENs, inspect the complete outbound Git range, and stage exact paths only.
