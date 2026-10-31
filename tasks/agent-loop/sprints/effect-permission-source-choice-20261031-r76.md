# R76 — derive same-use plan and global formal-owner choice

Status: ADMITTED by Luna after R75 closeout.  
Sprint ID: `EFFECT-PERMISSION-SOURCE-CHOICE/20261031-R76`.  
Branch / baseline: `yulang3`; `9b523f587cf1e8cf2142ede750fa85121876d415`.  
Authority: continuing `research/simple-sub-intrusion`. This packet advances the earliest missing source/Internal-incidence premises. It does not change inference behavior, semantics, production authority, or the original A/B gate.

## Fixed outcome

From the actual same-owner source inventories and native incidence loop, derive all three results below for the exact Internal `DefinitionUse`:

1. the unique plan for that use;
2. R66's actual `ownerSelection` result at that plan's target-root component;
3. equality of the selected formal's exact parameter recipe.

The result must be constructed from primitive inventories. Do not accept a supplied plan, selected registration, successful `ownerSelection`, `Root`, `readRoot` success, or policy success as a decisive premise. Preserve the distinction between a formal parameter root and the registered Lambda root. Do not prefilter formal origins by the desired shared Function Term or effect-row image.

Native source anchor: `InferenceSession::internal_formal_permission_incidence` in `crates/yu-solver/src/lib.rs:18281`, especially the source/use identity and Internal-route checks, the ordered loop over eligible origins, per-registration recipe cardinality, component match, unique selected origin, exact recipe/parameter check, and source-Lambda/origin/permission checks. R45 `OwnerReads` does not establish R66's global selection.

## Rust lane

`/root/r76_rust`, Luna/high, 1000 seconds. Write only:

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-source-choice-r76-rust.md`

Expose a private owner-borrowed choice construction from complete same-owner inventories. Preserve source/use identities, component coordinates, registration identity, recipe cardinality and parameter positions. Match the native loop's failure order, including failures before it reaches the eventual target. Do not edit `lib.rs` or ordinary inference paths. No tests or build.

## Constructive Lean lane

`/root/r76_proof`, `lean_prover`, 2600 seconds. Write only:

- `notes/theory/lean/YulangClosure/SourceInternalChoiceR76.lean`
- `tasks/agent-loop/inbox/effect-permission-source-choice-r76-proof.md`

Use R55 primitive source inventories and derive the unique exact-use plan, then derive agreement with R66's actual `ownerSelection` and the exact selected parameter-recipe equation. Connect this to the native loop without assuming a successful choice. Preserve recipe-registration identity and the formal-parameter-root / registered-Lambda-root distinction. Include complete theorem types and transitive axiom reports. A finite fixture is supplemental and cannot replace constructor theorems.

At most two direct Lean stdin audits, each ≤120 seconds with `-j1 -M1024`, may be used. Before each, freeze and hash the exact flattened input, dependency manifest, command, output destination policy and audit authorization in the current record. Emit no `.olean`, `.ilean`, build/cache/target/scratch output. If required imports are unavailable without materialization, leave the audit UNCHECKED; do not build them.

## Required counterexamples and review gate

After both authors STOP / WRITES STOPPED, `/root/r76_review` independently reviews the frozen sources and receipts, writes only `tasks/agent-loop/inbox/effect-permission-source-choice-r76-review.md`, and has 1200 seconds. Review:

- duplicate plans for the same exact use;
- two eligible origins;
- missing or duplicate recipe for an eligible origin, including one encountered before the eventual target;
- wrong target-root component;
- wrong parameter-recipe index/value;
- shared Function/row with a foreign registration;
- source-level correspondence and exact native failure order;
- Lean declaration types, actual R66 definition, dependency bytes and complete axioms.

Reject a theorem whose decisive premise is the plan, selected registration, successful `ownerSelection`, `Root`, `readRoot`, or policy result it claims to derive. The review must distinguish a conditional model result from source/native extraction.

## Pins, resources and boundaries

The exact source, Lean dependency, toolchain and R75 review pins are in `effect-permission-source-choice-20261031-r76-inputs-r1.json`. Primary owns admission, exact leases, author stop/review sequencing, adjudication, state archive, exact staging, commits and pushes. Total envelope 6000 seconds: proof 2600, Rust 1000, review 1200, primary 1200 including at least 500 closeout; Astra 0.

Use this checkout and existing installed Lean only. No new environment, worktree, dependency, configuration, cache, build target, scratch directory, generated output, Cargo, compiler, tests, formatter, Lake, or project build. Static source inspection and `git diff --check` are permitted. Do not stage unrelated dirty or untracked paths. Preserve all 32 pending items, UNKNOWN worker observations, quarantined path leases, and the R24 capacity disposition. Never convert UNKNOWN to STOPPED based on capacity accounting.

## Closure boundary

Acceptance closes only the same-use plan, global formal-owner selection and selected parameter-recipe premises within this packet's source-aligned constructor. It does not establish complete incidence, actual Rust-to-Lean extraction, native source execution, physical Root joins, genuine R66 `Root`, original A/B, whole-language soundness, or production. No semantic gate is weakened.
