# IMPORT-SOURCE-AUTHORITY-AUDIT-20261027/r1

Status: Luna-admitted read-only evidence packet; original Yulang parent remains OPEN.
Baseline: `6da3e4a45` on `yulang3`. This contract changes no source semantics.

## Bounded question and outcome

Use only the already adopted source rules and the exact finite provider/import
instance from caller-realization r1: provider `std::core::id`, consumer alias
`identity`, and the prelude glob exposing the same provider. The selected
nested-shadowing source subtree and its accepted owner-table mapping are fixed
inputs; they are not reinterpreted here.

Produce either an existing-rule derivation applied to this concrete instance,
or a reviewed field-by-field authority gap. For each original `Binding` field
(`name`, `owner`, `kind`, `component`, `annotation`, `entry`, `singleUse`),
name its actual producer, the adopted rule authorizing it, and the specific
provider evidence needed; if none is adopted, state the first missing equation.
Audit complete ordered import roots separately from construction of
`OriginalSource.Source`. Trace §3.3/§3.4's external `Mono/Established`, prior
`Published`, independently typed `Family`, and alias rules through the actual
existing consumers. Determine whether the adopted linking/elaboration rules
discharge both (a) export identity to original Binding fields and (b) ordered
imports to the complete resolved source root.

This is source analysis, not theorem certification: no Lean/Lake, Cargo,
compiler build, tests, or formatter runs. Do not add a theorem, Context
constructor, import constructor, or source-elaboration rule. An equal
`SourceExportId`, resolver route, opaque `CallerEvidence`, or `moduleS` cannot
be treated as semantic provider evidence by convention. If adopted sources
leave a semantic choice, record the concrete alternatives and consequences for
a later user decision; do not select one in this packet. No production
import/Context code slice is authorized.

## Governing inputs and pins

Rehash every listed entry in the prior caller contract and its exact source,
proof and review handoffs before use. The following governing sources are
directly pinned:

| Source | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean` | `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationInstance.lean` | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean` | `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a` |
| `tools/inline-authentic-extraction/src/bin/original_owner_reify.rs` | `4921d14f813e931cb064ecc87d8120734b69d1eedaf48fe0bd36deb014e862e9` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| caller r1 contract | `9c6bb17280250a83c68f42cc17dc32ccc331e60a7f5290af1d942b5e139432e6` |
| caller r1 review | `5ad88936a23504a429d9dbaeeced0325a37849fe7628786e6ebfeaed97a1cbfc` |
| caller r1 outcome | `9e09bd1fdc7c36426ac85fa4a2fb3483d6f0ead8987ccf8a2062e3245c7f300d` |

The concrete import consumer/provider fixture is pinned by caller r1's
`module.rs` hash above and review. Any pin drift, different source domain, or
unreviewed fixture change stops this packet.

## Exact leases

Source-owner analysis — registered `researcher`:

- `tasks/agent-loop/inbox/import-source-authority-20261027-source.md`
- scratch only under `/tmp/yulang-import-source-authority-20261027/source/`

Proof/source-rule analysis — registered `lean_prover`, **source reading only**:

- `tasks/agent-loop/inbox/import-source-authority-20261027-proof.md`
- scratch only under `/tmp/yulang-import-source-authority-20261027/proof/`

Fresh independent review — `spec_auditor`, read-only, no file writes or
commands. Luna owns the review report path
`tasks/agent-loop/inbox/import-source-authority-20261027-review.md`, the
design decision packet `notes/design/2026-10-27-import-source-authority-audit.md`,
the sprint outcome and `current.json`. Luna alone adjudicates and integrates.

The source and proof lanes may work in parallel. Neither has Rust, Lean,
compiler, semantic-change, dependency, test or Git execution authority.

## Resources, stops and boundaries

Fresh budget: **1800 active seconds** — source 450, proof 600, Luna 270,
review 360, dispatcher 120; Astra 0. Cargo 0, Lean/Lake 0, tests 0; no
verification process. Prior sprint resources remain spent.

Stop if a rule is quoted without its exact adopted source, if a conclusion
depends on treating resolver identity as a typed certificate, if any Binding
field is silently defaulted, if import inventory is confused with the original
Source tree, if an independently typed `Family` is conflated with `Published`
or `Mono`, or if a semantic choice is made without authority. Preserve the
first exact unsupported equation and its premises.

The original full source domain, Simple-sub A/B, soundness, Effect hygiene,
principality, termination, complete Call, source/native, universal frontend,
receipt/admission and production gates remain OPEN with original quantifiers.
Released capacity and UNKNOWN/quarantined paths remain unchanged. Consult at a
material authority boundary, new owner obstruction, frozen review seam or END.
