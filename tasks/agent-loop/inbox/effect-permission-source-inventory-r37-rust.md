# R37 Rust source inventory handoff — candidate, writes stopped

Sprint-ID / contract revision and SHA-256:
EFFECT-PERMISSION-SOURCE-INVENTORY/20261031-R37, revision 1,
33c4c4f1d60e69c11a1a082cbe10a91728888bcdcbf2e11b8f735aa5d14dc756.

Assignment-ID / handoff revision: effect-permission-source-inventory-r37-rust, revision 1.
Parent gate: R36 source-owned callback-use selection, advancing the source-use
extraction gap named in R37 §1; original effect-hygiene, Simple-sub A/B and
production claims remain OPEN.

Baseline / direct dependency hashes:
- Baseline: yulang3 / ce922eed506e1471abe9a0f6823674da7ba55039.
- Governing design, notes/design/2026-10-10-annotation-effect-hygiene-integration.md:
  a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18.
- crates/yu-hir/src/module/local_source.rs:
  7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1.
- crates/yu-hir/src/module.rs:
  6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646.
- R36 Rust handoff r2:
  df72f3c643b1267f4d9ff40e737890d45fe4059f4c9e5b75a7c246bb5d480ec5.
- R36 proof handoff r1:
  0d1a5d7e4c31ff6722269c6d894f301950c87b34c641b395e11c8360aebd8558.
- R36 review:
  2b2f8bb23727c82fc572046e36d2aba64b63ac2020cbb491151b871ee3779afe.
- Current program.rs includes R36's primary B1 correction
  (annotation.ty.effects); R36 review's repaired pre-R37 file hash was
  b3fc1daacdba9fa9618b9b741e4f85d8e9ea0dcd5e859540204d09200d23a65d.

Role / actual worker: /root/r37_inventory_rust, this assignment session.
Launch/runtime receipt unavailable in this worker context. Requested model and
effort: Luna / high. Observed model and effort: UNKNOWN.
Exact leased paths: tools/inference-playground/src/runtime/program.rs and
this handoff. Author: /root/r37_inventory_rust; no descendants.

Outcome class: implementation candidate and source-native evidence, uncompiled
and pending independent review.

## Behavior added

RuntimeProgram::source_callback_uses now returns
Result<Option<Vec<SourceCallbackUseWitness>>, TryReserveError>. A semantic or
identity rejection is Ok(None), a successful inventory is Ok(Some(uses))
including Ok(Some(vec![])), and a failed fallible reservation is Err.

Before selecting the Lambda, it walks the entire retained
LocalSource::expressions() vector and constructs an occurrence-to-vector-index
map. It rejects duplicate occurrence IDs rather than overwriting or choosing
one. Every vector occurrence must belong to the retained HIR artifact and its
occurrence_source_key must equal the expression's retained source key. The
requested Lambda is resolved through this map and checked at that exact vector
index.

Before filtering for the selected formal, it walks every retained Apply.
LocalSource::expression(callee) validates the source index owner and bounds;
the resolved expression must map back to the same vector entry. Thus an invalid
unrelated callee edge rejects the inventory too. Apply-parent multiplicity is
counted by occurrence only after the complete unique-identity map exists.

The second pass walks Apply expressions in retained vector order. It emits each
matching direct Name-as-callee use in that order, preserving distinct-use
multiplicity. A shared Name occurrence with multiple Apply parents rejects the
whole lookup. The existing snapshot, source-root, Lambda/formal, annotation,
Observe classification, and authenticated R35 selected-result-row checks
remain in force. No Simple-sub bypass or Instruction::Apply change was made.

Fallible reservations for the occurrence map, Apply-parent map, and output
vector propagate allocation failure separately from semantic rejection. Existing
R35 witness payload cloning still uses its established Clone paths; this
packet does not claim that every internal Rust clone is fallible.

## Parent/source/native correspondence

- HirModule::local_source_for authenticates the requested source root before
  returning the retained source carrier. LocalSource::expression checks an
  index's source-root owner and vector bounds.
- The retained vector is the inventory domain. R37's map makes its occurrence
  identities explicitly correspond to vector indices. HirModule::owns_occurrence
  checks artifact ownership; occurrence_source_key supplies the source-key
  crosswalk for each retained expression.
- LocalSourceForm::Lambda supplies the selected annotated formal;
  LocalSourceForm::Name with LocalSourceResolution::Parameter(formal.id)
  supplies resolver identity; LocalSourceForm::Apply.callee supplies the
  indexed source edge. R35 supplies the authenticated ordered result row and
  R36 retains the Observe classification and exact source coordinates.
- The R36 Lean handoff intentionally did not prove Rust vector enumeration,
  duplicate-ID rejection, empty-vector equality, or an extraction simulation.
  R37's Lean lane owns the finite indexed relation and theorems connecting its
  individual R36 issuer to the inventory. Proof-to-Rust source correspondence
  remains pending that frozen artifact and fresh review.
- This slice ends at source-planned inventory. It adds no generated
  constraints, propagation, runtime Name receipt, invocation, Grant, Catch,
  native Step/History, or execution claim. Those owners and the original A/B
  premises remain OPEN.

## Reused and rejected evidence

Reused R36's frozen Rust selection guards and R35 row witness. Reused the R36
review's correction that SourceAnnotation stores effect information under
annotation.ty, and its finding that the old implementation's first-match
Lambda search and partial Apply scan did not prove full vector extraction.
The current source already contains Luna's R36 B1 field-path repair.

Rejected any inference that the R36 per-use issuer proves enumeration,
uniqueness of an arbitrary HIR occurrence map, runtime invocation, permission
consumption, or parent-theorem closure. R36's unauthorized quarantined-file
search disclosure remains preserved in its handoff/review; neither quarantined
consumer was opened or searched for this assignment.

## Artifact and checks

tools/inference-playground/src/runtime/program.rs SHA-256:
d2a54ae0409d71ddf384a1c4045188096d3a8b1e610f8b5666de949960337c5a.
This hash includes the retained R36 candidate plus this R37 method delta.
The handoff hash is frozen by Luna after this file is complete.

Focused check: git diff --check -- tools/inference-playground/src/runtime/program.rs
passed. Manual source review checked map construction, duplicate rejection,
all-Apply edge validation, vector-order enumeration, the three outcome cases,
and the unchanged root/formal/Observe/R35 guards.

No build, Cargo, test, formatter, Lean/Lake, target/cache, worktree, copy,
scratch, new environment, Git mutation, or quarantined path read/search was
used. Rust compilation and runtime behavior remain unobserved. Active-work
metering was unavailable; charge this assignment conservatively against its
1,600-second cap. No generated or disposable scratch output exists.

## Remaining premise and next related step

The Lean lane should prove lookup soundness and completeness against its R36
individual issuer, vector order and multiplicity, duplicate rejection, and the
empty inventory, stating allocation success where required. First missing
cross-lane evidence: a fresh reviewer must reconstruct that finite Lean
inventory relation against this exact source hash and the pinned HIR owner/index
methods. The original parent still needs runtime consumption and the source-to-
constraints-to-propagation-to-execution owners; this source-only contribution
does not close those gates.

Worker state / writes stopped: STOPPED after this handoff freeze. No descendants,
generated outputs, scratch or unresolved child leases.
