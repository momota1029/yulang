# R95 independent pre-edit spec review

Reviewer role: `spec_auditor` (independent, read-only; returned through collaboration message because its role prohibited file writes). This file is a primary-preserved transcript of that receipt, not a primary review.

**CLEAN — pre-edit review of the exact R95 correction.** No new semantic decision or user approval is required for this correction. This does not accept the R93 bridge or close its remaining review obligations.

The existing test has two defective expectations:

- **major — test defect:** `crates/yu-hir/src/tests/shadow_method_role_source.rs:97` universally equates HIR receiver and provenance-node ranges. Authority: R93 proof note lines 45–51, 79–89 and 97–110; actual constructors `lib.rs:506–545`, `lib.rs:797–803`; syntax reference `call-field-path-tails.md` §4. The second receiver spans `x.first`; its paired source node is `.first`. **Closure:** preserve first-IdentifierExpression equality; replace second equality with start equal to first receiver start and end equal to prior FieldTail source end.
- **major — test defect:** same file line 98 requires every receiver slice to begin with whitespace. Authority: R93 rev2 contract lines 65–72 requires preserving constructor-owned trivia, without requiring trivia to exist; syntax reference `call-field-path-tails.md` §4 assigns continuing trivia outside the FieldTail. **Closure:** remove only that universal whitespace assertion; perform no trimming.

Requested additional assertions follow directly:

- First receiver range equals its IdentifierExpression source range: `lib.rs:561–567`.
- Second receiver child zero is pointer-identical to the first borrowed receiver: `lib.rs:521–535` moves the prior pair; `shadow.rs:1819–1823` borrows its actual child zero from shared retained roots.
- Second receiver provenance identifies the prior FieldTail: `lib.rs:545`; same-artifact `source_position` checks parse ownership and unique retained occurrence at `shadow.rs:833–843`. Obtain its key through `source_identity.rs:27–35` and compare with `fields[0].source().tail()`.

These assertions preserve and strengthen the bounded correspondence check. Field order, distinct occurrences, source kinds and declaration identity assertions must remain intact. Endpoints simplify the constructor’s general `min/max` span only for this source-ordered accepted `x.first.second` fixture.

Inspected SHA-256 bindings:

| Input | SHA-256 |
|---|---|
| R95 contract | `05eb5a3148585358e33cb573076984f07d803e71ffbd69813e7c321cd850ea29` |
| R93 proof | `6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c` |
| R93 closeout | `c235ca1ad17c45327a2fd98508b2ff1b83a582f803f434090661a0fed65b13b2` |
| R94 closeout | `541a05aae0bf4fc0d98a23b508f3b3b27c90c3d424a66811290a27e5ae6b3b83` |
| `lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| Starting focused test | `9989e108c874d30804bfbe6d2d96d26f3889934dd2104c74f0b161cca0d41e93` |

No files written: the reviewer’s read-only role prevents writing the inbox. No builds, tests, Git or descendants used. Post-edit delta review remains required.

## Post-edit delta confirmation

Reviewer: same independent `spec_auditor`; returned read-only through collaboration, transcribed by Luna. Frozen test SHA-256: `6d5c3fec7b4ca0d4618f4ad378f0ad5e8e0689b4897d406ab90d175ba78e6135`.

**CLEAN — post-edit delta confirmation.**

Reversing only the inspected assertion replacement reconstructs the exact starting SHA-256 `9989e108c874d30804bfbe6d2d96d26f3889934dd2104c74f0b161cca0d41e93`, confirming no other changes.

At `crates/yu-hir/src/tests/shadow_method_role_source.rs:95–111`, the delta implements:

- first receiver/source-node range equality;
- second receiver start equal to first receiver start, and end equal to prior FieldTail source end;
- pointer identity between second receiver child zero and first receiver;
- same-artifact checked `source_position` joining second receiver provenance to the retained first FieldTail.

Authority: R95 contract §Outcome and exact source distinction; R93 proof note §Ordered paired constructor invariant, Lemmas 1–2; constructors `lib.rs:506–567`, `lib.rs:797–803`; checked identity lookup `shadow.rs:833–843`.

Only the two overstrong expectations were removed. Both Node-shape checks remain enforced by destructuring; source kinds, field order, occurrence distinction, declaration identity assertions, other tests and semantic test names remain intact.

No findings. Caveat: this confirms the bounded test delta only; compilation, execution and final independent compiler/source review remain outstanding. No writes, builds, tests or Git used by reviewer.
