# Independent review — FORMAL-PERMISSION-PROJECTION-20261028/r1

Reviewer: `/root/formal_permission_projection_review`; fresh non-author, read-only. No files changed, descendants launched, or Lean/Lake/Cargo/tests/Git commands run. This receipt is transcribed by the primary from the reviewer’s final message after STOP.

**Verdict: failure disclosure accepted; proof acceptance blocked.** The submission exposes exporter lookup equations and identifies the unresolved construction/capture responsibility. It does not repair or discharge that obligation. Source correspondence remains unreviewed/OPEN because the source lane supplied no handoff.

Initial assessment used the module, contract, governing design and actual failure logs before reading the author's explanation.

## Findings

### BLOCKING — final artifact lacks successful verification

Locations: `notes/theory/lean/YulangClosure/OriginalFormalPermissionProjection.lean:130`, `:159`, `:161`; retained `verification.log`; `FinalModuleAudit.lean:161`; `final-audit.log`.

The official helper with `--full` exited 1 during the module build, before default-target verification and theorem auditing. The later audit also exited 1 and produced recovery declarations:

- `export_provenance`: `[propext, sorryAx]`
- `list_export_provenance`: `[propext, sorryAx, Quot.sound]`

The audited source used `rfl` for the captured-root equality; frozen final line 159 instead uses `captured`. Consequently, these failed logs concern earlier bytes and establish neither success nor failure of the final repair. The final artifact is **unchecked**, not a verified theorem containing an established final `sorryAx` dependency.

Violated acceptance requirement: sprint verification contract and `yulang-lean-proofs` require successful checking of exact delivered declarations, complete transitive axiom audits and the integration target.

Minimum closure evidence: a newly authorized bounded verification of the frozen final bytes, successful helper/full execution and complete accepted axiom results for all ten declarations. The handoff correctly discloses this blocker at lines 33–34 and 52–56.

### BLOCKING — constructor-port/capture-image invariant remains absent

Locations: module lines 34–37, 85–88, 130–135; `candidate_effect.rs:1461–1487`, `:1494–1544`; `candidate_scheme.rs:2784–2800`; `shadow_apply.rs:2638–2696`.

`Graph` supplies arbitrary node/root maps. `project` reads those maps, and `export_provenance` concludes lookup equations plus metadata preservation. No constructor execution, allocated-port witness, capture mapping, or relation identifying that port's captured image occurs in the theorem.

Concrete logical separation: `unrelatedGraph` maps every domain root to node 0, whose Result effect is row node 1. Export succeeds independently of any constructor provenance. The theorem's additional `1 ≠ 2` does not encode a constructor allocating node 2. This is appropriately described as a graph-only example, not a Rust counterexample.

The inspected Rust constructor allocates and records permission paths separately from the port; root publication only retains endpoints already present in capture. Exporter lookup cannot supply the missing preservation argument.

Governing requirement: sprint “Fixed outcome” and constructive-proof lane require the exact constructor-created port image, including polarity, aliases and shared rows. Authoritative annotation integration §4 preserves canonical identity and annotation authority separately.

Minimum closure evidence: a source-qualified constructor/capture endpoint-image invariant, derived at the actual interning/expansion owners and composed with exporter lookup. Cover Function polarity changes, Tuple children, representatives/aliases and occurrence identity. Do not substitute equal families or equal canonical coordinates.

## Scope and disclosure assessment

No additional major/minor defect found within this bounded review.

The handoff accurately retains incomplete status, failed verification, omitted source simulation and open parent gates. Eight independent declarations print `[propext]` in the failed audit; this is useful fragment evidence, not acceptance of the final whole module.

The exporter model reflects inspected Function/Element lookup and failure branches. Native overflow, allocation failures and owner filtering remain explicitly outside its proof. Relevant existing tests were read, including the Tuple projection test and the internal shared-port/polarity test; none were executed and neither supplies the general capture invariant.

Parent, effect hygiene, source/native, consumer and production gates remain **OPEN**. The result can support an honest failure/outcome receipt; it cannot support proof promotion.

## Artifact authentication

SHA-256, independently computed:

| Artifact | SHA-256 |
|---|---|
| Final Lean module | `287908091421872e42a07214199351794f2b81d881c161797516a7f218171be3` |
| Proof handoff | `5dd1842a36fdab29deff532f1b23d240679f659b891c411fb1803ee9ec530a84` |
| Sprint contract | `3d7230480fd223028c076a70ea948e80f9857af64fddaad05d25fb0944a14be9` |
| `verification.log` | `83a72a8dc89f3fb377a328f7bbac53eac2cb82b973c7321f2679512db29ae59e` |
| `final-audit.log` | `7c439d36c8d767cb024e9609cd466d6ea4be25498867511fb019aaf61b243bd5` |
| `FinalModuleAudit.lean` | `9aac4e5ff4d9a2382d7273af4aea187705f72db2f86c645ffabf1391a7f8a748` |
| Scratch manifest | `4cd68c53dc69d338ce5eaa2a7164f09e053a0de9ed4ae6a729acf352f93f791e` |
| `candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| Authoritative annotation integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

The final module and handoff hashes were rechecked unchanged at review end. The isolated project's module matches the final module hash.

Observed clock interval: `2026-10-27 21:44:49–21:45:23 UTC`, 34 seconds; initial reads preceded the first clock sample, so total review duration was not precisely instrumented.

**STOP.** No writes or launched processes remain from this reviewer.
