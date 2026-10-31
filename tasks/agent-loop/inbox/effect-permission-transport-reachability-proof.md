# EFFECT-PERMISSION-TRANSPORT-REACHABILITY-20261028/r1 — proof handoff

Assignment: `/root/effect_permission_transport_proof`; handoff revision 1.
Contract: `tasks/agent-loop/sprints/effect-permission-transport-reachability-20261028-r1.md`, SHA-256 `9318a0697e21e781db875101e781927c91e282b832308ff47d0174846fee58c4`.
Outcome: bounded static source/native correspondence audit; no attributable unequal-transport instance and no new Lean declaration.
Requested role: registered `lean_prover`; effective model/effort: UNKNOWN to this interface. Sole author, no descendants. Current packet ACK sent to Luna before analysis.

## Original obligation and corrections

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. Its quantifiers cover every supported original source program, lawful finite Simple-sub construction history, and actual retained extrusion occurrence, retaining the actual origin/receiver, polarity-specific pairs, scopes and one shared source-admissible witness/strategy. Source typing, required principal coverage, soundness, ordinary progress and termination remain required. No smaller source language or pointwise independent witness substitutes for that statement.

Read the current qualification correction in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: actual source Values qualify through the graph induced by one immutable Value birth level. Current type-row levels and Value birth levels are distinct. The old cross-level helper application in parent §5 is historical evidence under its superseded rule, not a current qualified-source witness.

Effect semantics: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`, including §§1.1–1.2 corrections. A negative annotation grants local concrete subtraction permission; inflow and residual remain constraint-derived. Row equality does not supply annotation authority or erase boundary ownership. The existing injective-renaming theorem does not establish a potentially identifying parent/copy operation.

The whole-source root inspected is `YulangClosure.SourceProblem.InferenceSoundness` in `YulangClosure/Contracts.lean`: for every `s x d a`, supported `s`, generation `generates s x d`, and `solves d a`, obtain one `e` with `sourceJudgment s x e ∧ sameScoped s x e a`. It is a proposition definition, not a proved concrete source instance. The companion `SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence` and `InferenceTermination` definitions also remain separate obligations.

## Frozen dependency intake

Rust revision 1: `tasks/agent-loop/inbox/effect-permission-transport-reachability-rust.md`, SHA-256 `d2562c3e8be3ec1633f47adde6add41d4d92bf361b71d25d0eba3582a24cfe5c`. Independently rehashed this handoff and every contract source pin:

| Input | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1` |
| `candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `Cargo.toml` | `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed` |
| `FormalPermissionExportWitness.lean` | `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f` |
| `FormalPermissionExportWitnessNative.lean` | `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1` |

Rust paths above are under `crates/yu-solver/src/`, except `Cargo.toml` under `crates/yu-solver/`; Lean paths are under `notes/theory/lean/YulangClosure/`. Both existing decoder modules remain immutable.

## Independent source and position audit

The recursive test at `candidate_effect.rs:3045` is ordinary source: it constructs text containing `my f(pair:((int -> [io] ()), (int, int -> [io] ()))) = f pair`, parses, lowers and calls `CandidateInference::solve`, then exports the actual definition owner. This classification is independent of whether its demanded transition occurs. An internal fixture that directly installs or merges Effect parents supplies no ordinary-source reachability evidence.

At `candidate_formal_annotation` (`candidate_effect.rs:1815–1849`), nested rows receive the enclosing formal parameter's current Value-row level. `candidate_extrude` (`candidate_extrusion.rs:94–139`) examines the actual nested Effect row's level: `original_level <= target` records the original endpoint and continues; only `original_level > target` allocates a fresh lower-level copy and retains a Parent. The source dispatch at `lib.rs:14714–14738` obtains target from the receiving Value row. No source-attributed strict level drop for the exact annotated Effect row is provided by this packet. Thus no inference that all ordinary source routes lack such a drop follows.

Further guards remain material: `retain_extrusion_parent` (`candidate_intrusion.rs:324–356`) inserts a pending parent only for a qualifying actual source event; recapture activation (`:393–415`) retains its own real-source condition; `settle_candidate_intrusion` (`:570–593`) processes pending parents. Current qualification must be interpreted under the Value-birth-level correction above.

Directionality is an additional necessary premise: `merge_candidate_rows` canonicalizes `copy` and `parent`, returns if equal, and writes the COPY representative's forest entry to the PARENT representative (`candidate_intrusion.rs:613–679`). Therefore a qualified extrusion whose parent is the original annotation allocation `r` does not by itself show `effect_rep(r) != r`. The witness must identify the actual allocated `r`, demonstrate a write affecting its representative chain on the copy side, and connect that final representative to the independently materialized captured graph row `q`. The bounded Rust backward slice establishes relevant guards, not that extra premise.

Position mapping is presently incomplete. `FormalEffectSite` at `candidate_effect.rs:1654–1659` records the actual nested `SourceEffectRow.position`, full structural path, formal occurrence, parameter, owner and constructor. `SignatureContext::position` at `:309` returns the enclosing annotation's `position`; `DelegatedTail` at `:2424–2429` and `DelegatedPort` at `:2485–2486` record that enclosing position. The test at `:3224` compares these different coordinates for equality and previously found zero matching sites. Owner/constructor/name equality alone cannot disambiguate multiple nested rows. A valid join must preserve both coordinates and their actual source-tree occurrence/path relation, retaining both positive/negative port allocations and their shared tail. No such corrected observation is furnished here. I made no compiler/instrumentation edit.

## Exact Lean boundary and parent application

Inspected `YulangClosure.FormalPermissionExportWitness.expected`, `expected_fields`, `expectedAll`, `observationsMatch`, `decodeObserved`, and `observed_origins`, plus all ten declarations of `YulangClosure.FormalPermissionExportWitnessNative`. `decodeObserved c s code snapshot observations` first requires `decodeValue c false s code = some out`, then consistency of observations with `out.entries` and the supplied snapshot. Its record consistency does not authenticate native data.

The existing `run1_decode` and `run2_decode` are conditional in `c s code out`, capture/root/node identities, both metadata/path values, successful decode and exact retained-entry equality. Their only specialized numeric data are the earlier logged identity pairs `[(19,19),(21,21)]` and `[(21,21),(23,23)]`. They do not yield unequal transport. `changed_q_rejected` additionally requires `changed ≠ representative fixed origin.allocatedRow`; replacing `q` by `r` is ineffective on these identity observations. The concrete-set lemmas require independent fixed origin metadata. Neither premises nor native authenticity arise from the static source audit.

Consequently there is no sound application to the original parent from a new concrete instance. `FormalPermissionTransportInstance.lean` was NOT CREATED. No theorem was added or strengthened. The earliest missing premise for this packet is a source-generated demand reaching the exact permission Effect row with strict lowering; subsequent qualification, copy-side representative change, capture/export join and nested-position association must also be evidenced. Even supplying all those observations would leave whole-source induction, shared strategy, coverage, principality, termination and production authority separate and OPEN.

## Evidence, omitted cases and handoff

Checks performed: read-only source inspection and Python SHA-256 intake checks; all executed shell inspections returned exit 0. Read the Lean skill and both references, repository invariants, contract, relevant original/corrected sources, exact Lean definitions, project pin, lakefile and manifest. The project states Lean `4.35.0`, `-j1 -M1024`, and no external packages. Actual Lake/Lean version commands, build, checker and `#print axioms` were NOT RUN in this packet because the contract forbids an audit without native unequal-transport data. There are no fresh checker exits, theorem-type printouts or axiom results to report; prior checked status is dependency history only. No Cargo/tests, scratch project, generated artifacts or runtime measurements were created. Zero of the one allowed Lean invocation was spent.

Represented here: static negative concrete-only permission allocation, ordinary recursive source classification, extrusion/qualification/forest-write guards, existing finite observation decoder and the two identity-pair diagnostics. Omitted as unestablished: actual unequal transport; complete source occurrence mapping for delegated mixed symbolic rows; all-source reachability or unreachability; concrete decoder authenticity; source-to-native parent preservation. Static falsifier discussion does not count as executed mutation tests or independent certification.

TODO `TRANSPORT-NATIVE-STRICT-LOWERING`: Luna/source-demand owner needs an attributable ordinary source demand, row allocation/levels/target, actual event qualification and write trace showing that `r`'s representative changes; output must join to the captured `Node::Row`/`Graph.rows` datum `q`. Falsifier: an unrelated Effect merge or a write only from a fresh copy into unchanged parent `r` does not qualify.

TODO `TRANSPORT-NESTED-POSITION`: Luna/Rust source-construction owner needs both enclosing annotation position and nested row position with actual occurrence/path relation, linking delegated tail and both returned ports. Falsifier: two different nested rows in one annotation must not collapse under the common enclosing coordinate.

No next construction is justified inside this leaf packet without new frozen native evidence and primary direction. Pending fresh independent review and Luna adjudication; this artifact is not gate closure or production authorization. Exact lease used: only this handoff. Conditional Lean-file lease unused. Worker state: STOPPED; all writes stopped; no descendants, scratch outputs or remaining processes.
