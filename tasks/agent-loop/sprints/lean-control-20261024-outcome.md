# Lean seven-frame control: finite-trace safety and root application

LEAN-CONTROL-20261024/r1. Baseline `035c04780dc1cdfd0f35eabe1e56726bff7caacc`. Contract SHA-256 `7c71a1aa5f04f3a8180920f08dfbb4cbef513f892d0b74967042413847e3b43e`. All nine dependency pins matched before review; existing root mathematical modules unchanged. Whole goal ACTIVE/OPEN; compiler implementation excluded.

## Constructed and checked

The raw machine admits wrong responses, Bad and all seven frame families without typing premises. Extrinsic judgments type values, continuations, frames, candidate lists, packets and current heads. Value and operation searches are explicit ordered transitions. Shallow selection gives the original K to the chosen arm; exhausted operation search adds the handler to K. Wait preserves the original pending packet while a distinct request escapes, and No uses the current input world. Mapper adapters use ordinary run/bind exits outside the mapper. Failure never becomes No or a successful result.

`control_preservation` and `progress` exhaust control constructors. `capture_typed` and `packet_capture_typed` construct continuation typing from typed frame words. `resume_reusable` plugs two paired responses into the same K at any two current worlds, with no snapshot stored in K. `prefix_fail_absorbing` covers all finite raw internal traces. `finite_trace_safety` covers every finite root-machine trace, including arbitrary legal external responses, proving the same result type, Bad exclusion and progress.

`localLaws` supplies actual proofs of `internal_preservation`, `resume_formation`, `no_bad` and `progress`. `finite_prefix_control` applies the unchanged root composition theorem to that instance. Registered bodies, source initial typing and actual finite-cell seed/simulation/observation remain explicit inputs. No singleton/all-output Analysis or certificate was supplied.

## Coauthorship and exact repairs

Producer actual FINAL/STOP froze:

| Producer output | SHA-256 |
| --- | --- |
| ControlSyntax.lean | `5dceecc694c7ddf8dc304946c3f9a4e02e27a6d0670d3ccfb4b13e69404158a4` |
| ControlTyping.lean | `d7e250df8e5299a59f14deef9d0f063f9e339ffe956c14638a1e56e138d01765` |
| ControlComposition.lean | `f2f2b8bb98338c680caca69c2cf9c614c91b2d4bd800bb79783d5e885aa999e6` |

Producer supplied raw rules/typing/capture/response/failure and Machine adapter, explicitly reporting missing exhaustive preservation/progress and the value-pending/nonempty-operation-list gap. Primary took the three leases only after actual STOP. Primary fixed reserved `instance` spelling, replaced unsupported single induction on a mutually inductive judgment by frame-list induction, separated value/operation candidate positions, and exposed the complete value candidate search. Primary then constructed exhaustive preservation/progress, admissible resume formation, finite-trace safety, the LocalLaws adapter and root application. Both are authors; the independent reviewer is separate.

One later attempt to minimize the simplifier proof in `resume_atom_typed` failed on unresolved Bool equality; the known checked proof was restored and the whole project was checked again. No failing proof or hole remains in the frozen version.

## Actual verification receipts

Primary alone used the already verified official task-local Lean4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), no global configuration or package installation. Same official archive SHA as the preceding root sprint. One verifier, one CPU affinity, `-j1 -M1024`,120sec process timeout. Module checks in dependency order, final `lake build`, and `lake env lean -j1 -M1024 YulangClosure.lean` all returned exit0. Compiler tests/build/probes were not run; Lean proof checking is the authorized verification here.

| Export audit | Kernel axiom dependencies |
| --- | --- |
| Existing four root exports | none |
| Control.control_preservation | none |
| Control.progress; Control.prefix_fail_absorbing | `propext` |
| Control.resume_reusable; Control.finite_trace_safety; Control.finite_prefix_control | `propext`, `Classical.choice`, `Quot.sound` |

These are Lean's standard foundational axioms, not project assumptions or unproved Yulang results. There is no `sorry`, `admit`, project `axiom`, `unsafe` or native-decision escape in the mathematical modules. Axiom auditing does not discharge explicit theorem arguments such as BodyLaws or AnalysisLaws.

## Frozen review inputs

| Path | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/ControlSyntax.lean | `76b250485b899bf9f7f5d0b9445d869f4c5961b155a21a520b0802678a1db46f` |
| notes/theory/lean/YulangClosure/ControlTyping.lean | `33ddb90ec39e8136c1ec9bb72b0ef4edf35d85fb32c1884cff3a2bcc5819ebfa` |
| notes/theory/lean/YulangClosure/ControlComposition.lean | `23c7b251ef307a61ccaca7e2ec959d4a5583b649309a26cf27eff1eb9e9cb791` |
| notes/theory/lean/YulangClosure.lean | `0da5ae8619020d4cf5ef64a425d9ae9ffde6c5fc7d96867ca265aa086454e988` |
| notes/theory/lean/README.md | `375a4ede2842f37779523587b05319f13d84f923a82c291cf3cbbcbd0f8d1388` |
| notes/theory/2026-10-24-lean-control-correspondence.md | `a1f7add2b977b0b1a9200a74c8e0223035bc86ff820d4697c95d7742905fc0ad` |
| docs/yulang-whole-proof-closure-ja.md | `f706d12381e0e3dddc4f96a1f0a8f68a2194c5f68fbf8cf98a862d8f935e843b` |
| docs/yulang-proof-index-ja.md | `65efb500914f3dfdb837af561b71ff375246c0083aec7547c4f24ffaaf751e6f` |

## Independent review and original boundary

Independent `/root/astra_semantics_review` returned actual FINAL/STOP accepting the stated control abstraction. No BLOCKING/MAJOR finding. All supplied output/contract hashes and unchanged root mathematical module hashes matched. The reviewer confirmed raw malformed responses, extrinsic typing, exhaustive dispatch outside BodyLaws, shallow selection/forwarding, current-world No/pending retention, ordinary mapper effects/failure, all finite machine traces and actual four-field root application. The Nat-tagged/body/metadata/source boundary was explicitly accepted, with no whole-language claim. Reviewer had no authorship contribution, reran no checker and made no writes or descendants. Next owning obligation: original value/typing/registered-body interpretation, including direct result adapters before Yes.

The checked machine is a value-type control abstraction. `atom Nat Nat` does not define the full original values, recursive/nominal/evidence types, closures or graph. Each registered principal body still needs its actual operational relation and BodyLaws proof, including substitution and direct result adapters before Yes. Metadata has no concrete CM/H instance; release Ret route transport, L-Enter activation and immutable evidence correspondence remain. Exposed outputs currently cover terminal requests only; the actual emission/View/Ret/latent/reentry family and finite-cell laws remain. Initial formation from full source, native correspondence, original intrusion/SCC/extrusion A/B, source-scoped coverage, principality and inference termination are still OPEN. AH/RZ remain unreviewed and unused.

Next owning proof work must instantiate the registered-body/value boundary from the original syntax and type rules, or the actual metadata/observation/analysis boundary, and apply the result to the existing root. Reproving finite-prefix composition or relabeling its unproved premises does not close these obligations.

## Runtime, resources and integration

Actual direction30sec FINAL; producer190sec FINAL/STOP; independent reviewer80sec actual FINAL/STOP. Full grants charged: previous9650+30+190+80=9950 cumulative, exactly300 this sprint, max1 active Astra child, no renewal. Requested inherited Astra/medium; observed model/effort/elapsed UNKNOWN. No descendants; original checkout unknown writers and leases remain quarantined. Protected question files are untouched and excluded.

Primary adjudication: accept the independently reviewed conditional control milestone; original whole goal and all residual obligations above remain OPEN. All workers actually STOP. README/correspondence edits after freeze are review-status text only; mathematical modules remain byte-identical to the accepted freeze.

Post-review status-only file hashes:
- `notes/theory/lean/README.md`: `a4c018ce0856ef389abc182f2fb2f521564e3291c4531c29584f02555b8bebdb`.
- `notes/theory/2026-10-24-lean-control-correspondence.md`: `9a4aa76f9db1b9df2dcf386388e4962bbfa6c00f451c769791afa781d2bee4d5`.

Static verification and intended-range integration are recorded by the primary. Only explicit proof/doc/state paths are intended; `.lake` and pending questions are not staged.


### Final static audit

New/changed relative Markdown link targets exist; the audit does not claim that every historical link was rechecked. New file whitespace and mathematical-module project-axiom/proof-hole scan passed. `git diff --check` passed. All nine frozen dependencies and independent-review mathematical hashes remain unchanged. No compiler files, generated `.lake` artifacts or protected questions are in the intended path set. Resolved upstream is `origin/research/semantics-proof-20261024`; pre-commit outbound range is empty at035c04780. Primary will inspect the complete new one-commit outbound range and use ordinary authorized push.
