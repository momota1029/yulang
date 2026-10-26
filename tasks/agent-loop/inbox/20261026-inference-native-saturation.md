# Native replay/saturation construction handoff

Assignment: `20261026-inference-native-saturation`
Handoff revision: 1
Worker: `/root/native_saturation_construction`, generic bounded proof leaf
Parent: `/root`; assigned baseline `bf81a1bd444b3bcbecca6b754ea6fb603262f368`
Branch: `yulang3`
Contract: parent NEW_TASK packet in this session; no separate contract-file hash
was supplied. Requested/effective model and effort: inherited / UNKNOWN.
Outcome class: checked finite proof plus candidate source-native derivation.
Review: PENDING fresh nonauthor review; no production authority or self-review.

## Parent application and exact result

The original whole-source inference A/B obligation remains OPEN, preserving
the quantifiers and scope of
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` section 1 and
`docs/yulang-whole-proof-closure-ja.md`. No semantic solution, `RegularSub`,
local semantic preservation, or saturation assumption is a premise of the
new finite scheduling root. Applying it to arbitrary native execution is an
additional operational source-correspondence obligation.

The constructive packet has four usable parts:

1. The actual two incremental replay quadrants cover the current full fiber
   product, with old/old prior work kept separate. Incoming-use replay resets
   old heads and covers the full current product.
2. A concrete finite append/merge/consume program starts empty, generates every
   retained lower/upper pair, and on empty pending work has completed every
   such pair. Rejected route actions contribute no ghost suffix.
3. The saved-count/live-index scan visits every old direct entry under arbitrary
   suffix growth, and every old exact entry when the direct prefix is fixed.
   The checked three-case temporal assignment formalizes the reviewed
   DL/upper, EL/DU, EL/EU complete-block argument with actual snapshot-membership
   premises. It never assumes that each individual restoration visits all old
   atoms.
4. The paper derives those premises for current all-local Value blocks and a
   bounded extension to plain all-local Effect rows, using one prepared map
   and all four Function ports. The Effect extension requires no
   capture-incidence/reverse-frontier additions and identity, demand-free,
   empty scoped flow. Mixed/shared rows, merge during restoration, full
   contextual effects, Call and original physical-incidence authentication
   remain outside that bounded application and inside the unchanged parent.

The initial shifted-index investigation duplicated reviewed 2026-10-13 work.
The primary corrected the route before a new probe was requested to run.
Inventory was sent a stop on the redundant fixture. The small final arithmetic
example is labeled an illustration of established selected behavior, not a new
counterexample, defect, or repair recommendation. No Rust was edited or run.

## Delivered files, authors, and frozen hashes

Only this leaf authored the three leased files; no descendants or coauthors.
No shared root import, current.json, production Rust, tests, manifests, or Git
operations changed. Inbox hash is supplied in the final parent receipt.

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-26-native-replay-saturation.md` | `4759c80a17b6275e4184880cc43407ed86846b65b79bc592d3446eb26dfd90a4` |
| `notes/theory/lean/YulangClosure/NativeReplayCoverage.lean` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| isolated built `NativeReplayCoverage.olean` | `677860b08f586a0782d71dcdbf22dd084700b9ea69a1faf165d8606e759c2131` |
| isolated `NativeReplayOriginAudit.lean` | `aa2a640bf575d6ac4f04accf6edd62cdd04d40dee1762a84f78f8cdbc230a2eb` |
| `check-05-final.log` | `b27e952c6a839de8179ff44b6b7418f0deefe947d6999de281dae238453b8e81` |
| `origin-audit-06.log` | `60a6d71b7e94da2c7ef1f2e054ec018d5d857977228fd92d6e7f13a614a86675` |

Scratch root:
`/workspace/scratch/f98087c7ac1a/inference-native-saturation`.
It owns `project/`, its entire generated `.lake` cache, the copied module and
three pinned project files, the module-origin audit, logs, and
`freeze-manifest.json`. Repository/project source bytes compare equal.
The exact built-olean path is
`project/.lake/build/lib/lean/YulangClosure/NativeReplayCoverage.olean`.
The audit imports that built artifact, enumerates declarations by module
origin rather than name prefix, and checks required theorem roots exist.

## Complete root and module-origin audit

All names below have prefix `YulangClosure.NativeReplayCoverage.`.
The final named audit printed the exact type and `#print axioms` result for
every theorem; definitions were not substituted for theorem roots.

| Theorem | Complete axiom list |
| --- | --- |
| `mem_product` | `propext`, `Quot.sound` |
| `replay_quadrants_cover` | `propext`, `Quot.sound` |
| `incoming_replay_covers_all` | `propext`, `Quot.sound` |
| `empty_covered` | none |
| `step_covered` | `propext`, `Quot.sound` |
| `run_covered` | `propext`, `Quot.sound` |
| `committed_routes_covered` | `propext`, `Quot.sound` |
| `completed_routes_cover` | `propext`, `Quot.sound` |
| `scan_direct` | `propext`, `Quot.sound` |
| `scan_exact_without_direct_growth` | `propext`, `Quot.sound` |
| `temporal_three_case_coverage` | `propext`, `Quot.sound` |
| `equal_level_row_bound_is_upper` | `propext`, `Quot.sound` |
| `function_children_exact` | `propext` |
| `live_concat_saved_count_misses_atom` | `propext` |

The full module-origin pass printed the type and recursively collected complete
axiom list for **276 declarations**, including **5 private declarations** and
all generated declarations originating in the module. Exactly 276 unique
ordered BEGIN/END pairs, 276 TYPE records and 276 AXIOMS records were verified.
Observed axiom sets are only `[]`, `[propext]`, `[propext, Quot.sound]`.
There is no `Classical.choice` dependency and no nonstandard axiom. Source
search found no hole, project axiom, `native_decide`, or checker bypass.

Required roots checked independently by origin audit:
`replay_quadrants_cover`, `incoming_replay_covers_all`,
`completed_routes_cover`, `scan_direct`,
`scan_exact_without_direct_growth`, `temporal_three_case_coverage`,
`equal_level_row_bound_is_upper`, and `function_children_exact`.

## Checks, real failures, and resources

Pinned native executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual versions: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb (Lean version 4.35.0)`.

Named verification command is the repository
`.agents/skills/yulang-lean-proofs/scripts/check_lean.py`, with
`--project /workspace/scratch/f98087c7ac1a/inference-native-saturation/project`,
the pinned `--lake`, `--module YulangClosure.NativeReplayCoverage`, one
`--theorem` per table row, and `--timeout 120`. The helper invokes
`lake --no-cache build +YulangClosure.NativeReplayCoverage` before imported
readback. Module-origin command is
`lake --no-cache env lean -j1 -M1024 NativeReplayOriginAudit.lean`, cwd that
isolated project, with `LEAN_NUM_THREADS=1` and 120-second subprocess timeout.
Both final commands exited 0. Escalation was solely for executing the known
pinned toolchain locator, as assigned; no toolchain install occurred.

Material failed attempts remain evidence:

* Attempt 1: record update indentation caused a parser failure at line 66 and
  downstream type errors; tool transcript chunk `954ea1`, exit 1.
* Attempt 2: the same issue remained in the merge case, line 75; preserved in
  `check-02.log`, exit 1.
* Attempt 3: repaired source built and all then-13 theorem roots passed;
  `check-03.log`, exit 0.
* Attempt 4: audit-only mutable counter lacked a Nat annotation;
  `origin-audit-failed-04.log`, exit 1. No proof or checker policy changed.
* Attempt 5: final module built, all 14 theorem roots passed;
  `check-05-final.log`, exit 0.
* Attempt 6: corrected full module-origin audit passed;
  `origin-audit-06.log`, exit 0.

This is 6 focused attempts / 8 substantive Lean invocations, below the 16
invocation grant. Every invocation used one Lean thread and 1024 MiB Lean
memory cap; no timeout, Cargo, experiment, or heavy parallel build was run.
Peak OS RSS/CPU and exact initial worker wall timestamp were not exposed.
The full 1800-second grant was not intentionally extended. Source whitespace,
source-copy equality, root presence, origin-audit cardinality, axiom whitelist,
and SHA-256 readback checks passed. No default/root project build is claimed.

## Frozen direct dependencies

| Current source/input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `2026-10-13-restoration-temporal-coverage-proof.md` | `57d4cd90eab5c2de5ffb0709ed7d00a55a98e96b8169cdfa42ca7c0722aa6eeb` |
| `2026-10-13-fresh-use-restoration-disposition-proof.md` | `947981cb10d88ac599fa0cbde72125382393dc73635b6ddfd61fcbeaeb883cd3` |
| `2026-10-13-restoration-live-index-pair-audit.md` | `b98c41d86c8ef9c5b0ba0430d0f0c18d43fc9f9e9eb42fb7dd85e629ec85822f` |
| `2026-10-11-private-candidate-suspension-contract.md` | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

These are observed source bytes. The inventory worker owns a disjoint test
module declaration in candidate_context.rs; primary should revalidate that
file's hash/semantic delta at integration. No moving proof module was imported:
the checked new module depends only on installed pinned Std.

## Remaining owner and mutual TODOs

`NATIVE-SAT-TRANSPORT-1`: original whole-native saturation; first missing
evidence is a joint original-incidence transport for mixed/shared FreshUse and
representative-changing execution, preserved through all four Function ports
and later reuse. Owners: `prepare_candidate_fresh_use`,
`begin_candidate_fresh_bound`, `merge_candidate_rows`, contextual
Function-port admission and source reuse. Use actual captured/reconstructed
maps and the reviewed mixed-level owner trace. Falsifier: an authentic
source-history requirement with no owned pending/completed/transport
disposition after **all** compensating restorations and reuse activations.
Do not repeat private shifted-index fixtures or change the selected indexing.

`NATIVE-SAT-MODEL-2`: model producer's finite table C still requires syntactic
row/row reachable-head inclusion, row/head expansion, and exact head/head
children. The current packet contributes local generation and P-specialized
activation; it cannot fill those fields universally. Original optional-record
width and contextual effect checks cannot be replaced by the older equal-label
structural relation. Parent owns integration of the finite path/alias closure
and original source construction/transport proof.

Next action: fresh independent review of these exact bytes and the bounded
Effect extension, then parent adjudication and Git integration if accepted.
No production code change is proposed. This is a research checkpoint, not a
parent gate closure.

Worker state: STOPPED after submitting this frozen revision. All three leased
files and isolated generated outputs are write-stopped. No descendants or
unresolved child leases exist. The parent may integrate or assign nonauthor
review without waiting for another producer turn.
