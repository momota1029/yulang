# R25 — source-bound caller evidence retained across compiler phases

Status: Luna-approved sprint contract, revision 1.
Branch: `research/simple-sub-intrusion`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, original source
domain and quantifiers unchanged, OPEN / closure 0.

## Fixed outcome

Implement and prove the transport-only claim that a caller-supplied opaque
context can remain bound to one exact parsed source, module identity and
declaration occurrence through HIR, candidate inference and the runtime's
existing retained HIR. A binding observation means only artifact
correspondence. It does not establish `j0`, `a0`, license/incidence, phase
actions, `JointWF`, world validity, or parent-theorem closure.

The original obstruction is authentic caller-owned same-fiber evidence. The
selected acquisition path permits transporting such evidence but supplies
neither its constructor nor its semantic validity. Preserve all original
quantifiers and guards. Do not alter source meaning or promote evidence to a
verified semantic token.

## Frozen dependencies and baseline

Baseline: `f7edada810d94a320fc7d5a3e785e407a0bfb01c`.

```text
d10b7a94a37c2198f36ef923bc7c2c237da3d472bc992185fa49b7030330ecda  notes/design/2026-10-18-choose-caller-registration-witness.md
da8910aa088db1455ab5e3725429621333ecb319978c933491bd6310f8bf7007  notes/progress/2026-10-18-r24-caller-binding-closeout.md
60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed  crates/yu-hir/src/module.rs
cf0a2d537df793986509175fbde2785731ac28f4bc3f2024f4f0fbca2127c5ed  crates/yu-hir/src/lib.rs
7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3  crates/yu-hir/src/source_identity.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11  tools/inference-playground/src/runtime/program.rs
```

R24 evidence establishes no actual semantic tuple. The parse's `SourceNodeKey`
is branded by an owning parse allocation; candidate inference retains the same
HIR; `RuntimeProgram` also retains an `Arc<HirModule>`. These are transport
anchors, not semantic premises.

## Lanes, leases and limits

### A. Constructive transport lemma — prover, 720 seconds

Exact writes:

- `notes/theory/2026-10-18-caller-evidence-source-binding.md`
- `tasks/agent-loop/inbox/20261018-caller-evidence-source-binding.md`

State an introduction rule requiring caller-authentic evidence independently
bound to the exact source/declaration, scopes, dependencies and shared
`(W0,xi,h0)`. Prove only that retaining the owning immutable context and exact
source keys preserves these references under the corresponding parse/module/
declaration association. Apply it to the original caller registration
obligation. Keep authentic evidence, all semantic guards, phase histories and
the original parent open. Include a falsifier for mixed contexts or foreign
source/declaration acceptance. No code, semantics, Git or parent closure.

### B. Binding design — Luna, 360 seconds

Exact write: `notes/design/2026-10-18-semantic-imports-evidence-binding.md`.
Specify an opaque, immutable, owning payload and parse/module/declaration
binding; exact mismatch failure; compatibility of `SemanticImports::empty()`;
and the structural-only meaning of observations. No public truth trait,
Boolean proof flag, `VerifiedJointWF`, or solver/runtime semantic consumption.
Freeze for independent review before implementation activation.

### C. Reversible HIR implementation — Luna/high, 600 seconds, staged

Activate only after design review is CLEAN. Exact writes:

- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/lib.rs`
- `crates/yu-hir/tests/semantic_import_binding.rs`
- `tasks/agent-loop/inbox/20261018-semantic-imports-evidence-binding.md`

Keep the owned context inside the same immutable HIR object. Do not change
`yu-solver` or runtime unless review establishes a necessary identity seam and
Luna grants a new exact lease. Structural tests cover same parsed snapshot,
fresh equal-text parse, foreign module/declaration, ownership retention,
and `empty()` compatibility. Tests establish transport only. No semantic
admission or production claim.

### D. Independent review — fresh compiler referee, 480 seconds

Review frozen proof/design first, then the coherent implementation snapshot.
Attack forged truth implications, source or declaration mixing, fresh-parse
reuse, hidden fallback to empty imports, accidental semantic consumption, and
claims beyond transport. Authors and coauthors cannot certify their own output.

### E. Luna integration — 240 seconds

Apply any valid transport lemma to the unchanged parent and record the exact
remaining authentic-evidence premise. Keep the parent OPEN/closure 0. Report
which focused tests passed and any known formatting-only CI failure separately
from changed-code checks.

Total cap 2400 seconds, fully reserved as above; Astra 0. At most three active
assignments plus reserved review capacity. One heavy build/test process and
one verification owner. Quarantined untracked files listed in current.json are
excluded from every lease and commit.

## Success, stop and next boundary

Sprint success is a reviewed transport lemma applied to the exact source
binding obstruction, plus a reversible HIR retention path with focused tests.
This is one genuine source-binding condition reduced, not a discharge of
authenticity or `JointWF`. Stop on design review rejection, API insufficiency
that requires a semantic choice, dependency drift, resource limit, or any need
to expand exact code leases. Consult the dispatcher at the next substantive
blocker, integration seam or sprint closeout.
