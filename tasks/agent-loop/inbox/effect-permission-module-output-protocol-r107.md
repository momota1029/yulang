# R107 Lean output protocol audit — revision 1

Status: **FROZEN / WRITES STOPPED / PROTOCOL EVIDENCE, NOT PROOF**.
Assignment `R107-LEAN-OUTPUT-PROTOCOL`; sole author and actual leaf identity
`/root/r107_lean_output_audit`; session
`EFFECT-PERMISSION-BASELINE-RECONSTRUCTION/20261101-R107`. Parent NEW_TASK is
the live assignment receipt. Requested/effective model and effort: UNKNOWN
to this leaf. No descendants. Baseline supplied by contract:
`d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.
Sole write lease: this handoff; no other writes, scratch, cache or outputs.
Independent review and primary adjudication: pending.

## Frozen inputs

SHA-256 of inspected governing inputs and relevant declarations:

| Repository-relative path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/effect-permission-baseline-reconstruction-20261101-r107.md` | `47bf64e9e7e3d099c002083d1300a1573e49458f0064c820e7876b0d2b823efa` |
| `tasks/agent-loop/inbox/effect-permission-logical-owner-r106-module-validation.md` | `0117aa23acba54d083b67c05cbf2fd1f3c5008ae2630368b594c3d233b00273f` |
| `tasks/agent-loop/history/effect-permission-source-admission-20261101-r106-outcome.md` | `0f0ad632aba0b5e6f735c2eda7c9233d670589bd425ab0a7c183470150e779e9` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/lean/YulangClosure/SourceLogicalOwnerBridgeR105.lean` | `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

The exact Python body extracted in memory from the frozen R106 handoff,
between its `python3 - <<'PY'` line and closing `PY` (including a final newline),
is 13,511 bytes, SHA-256
`b154b0724da67e72c8e50ae4f42ab21559901d482942727a41849403d00e4548`.
It was read/hashed, never evaluated.

Installed source root:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`.
Every substantively inspected installed source is pinned here; search-only
unrelated identifier hits were not used as evidence.

| Path under installed source root | SHA-256 |
| --- | --- |
| `Lean/Environment.lean` | `6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43` |
| `Lean/Util/Path.lean` | `52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f` |
| `Lean/CompactedRegion.lean` | `56ef2a63c2394faefe590b58a5e3bd239589ddb6657a8523e5b0385800043f94` |
| `Lean/Elab/Frontend.lean` | `423d17e49722e901e5f82bd4b86e7cf2dd80c352fc55b3d72ac1301a79ead634` |
| `Init/System/IO.lean` | `409886ee25dd6ee5455dbb83269edbef98012dd22c5b6c45198b47514aeaca25` |
| `Init/System/FilePath.lean` (inventory/hash only) | `5f56ac500142ec0bcd1c219e186854ef357520d9ff1967d728d0b425dbc8856e` |
| `Std/Internal/UV/System.lean` | `0e310ebc5f51f373212dce6b3b07f0e6ac952323188bf1f4919a9459031b504d` |

## What the saved R106 receipt establishes

The primary-owned outcome records exactly one first-module invocation:

```text
/usr/bin/timeout --signal=KILL 60s /usr/bin/taskset -c 0 /usr/bin/time -v /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --root=/home/momota1029/rust/yulang/notes/theory/lean -o /dev/shm/yulang-source-owner-module-validation-20261101-r106/YulangClosure/OriginalSourceSyntax.olean /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
```

Saved result: exit `-9`, wall `5.918905` seconds, sampled group peak
`819956` KiB, empty stdout and stderr, GNU time peak absent,
`UNEXPECTED_OUTPUT YulangClosure/OriginalSourceSyntax.olean.tmp.7`, remaining
group member `[[7,0]]`. No second module ran. The runner quarantined its root
because cessation was unconfirmed. Later independent checks reportedly found
PID 7, relevant processes and root absent; root disappearance has unknown
cause. The runner supplied neither a successful cleanup receipt nor retained
artifact hashes. These are inherited receipt facts, not observations repeated
by this leaf. No quarantined runtime path was accessed.

This supports an output-policy failure. It supplies no Lean error diagnostic,
no accepted module, no bridge theorem type and no axiom audit. The R106 one-batch
allowance is consumed; R107 permits no retry.

## Serialization: established source behavior and exact limitation

`Lean.Elab.Frontend` at lines 381–389 returns before module output when
`hasErrors`; otherwise its selected output invokes `Lean.writeModule`.
`Lean.writeModule` (`Environment.lean:1902–1918`) distinguishes:

- Legacy environment: one `Lean.saveModuleData fname ...` call.
- New module environment: exported `fname`, `fname.server`, `fname.private`,
  followed, when `writeIR`, by extension-replaced `fname.ir.sig` and `fname.ir`.

`Lean.saveModuleData` at 1793–1794 delegates to
`Lean.CompactedRegion.save`; `saveModuleDataParts` at 1773–1777 performs
sequential saves with shared compactor state. `Lean.CompactedRegion.save`
is an unsafe opaque extern `lean_compacted_region_save`, not a Lean
implementation. The installed source inventory exposed no C++/header
implementation. Consequently the installed Lean files do **not** establish
the general temporary-name formula, whether the suffix is a PID, atomic rename,
replacement rules, flush/fsync behavior, or exception/SIGKILL unlink behavior.
The observed `.olean.tmp.7` is the exact one known temporary name. Treating
`.tmp.<pid>` as a fully established implementation contract would exceed the
evidence. `Std.Internal.UV.System.osGetPid` exposes a PID extern but no inspected
serialization source calls it. `IO.FS.rename` documents POSIX rename semantics;
that does not prove the compactor uses it.

`Lean.Util.Path.initSearchPath` at 95–110 places LEAN_PATH before the builtin
library; `findOLean` at 117 onward searches final `.olean` names. Temporary
files are not fresh-import evidence. `moduleNameOfFileName` at 146–159 derives
the module identity from the source path under `--root`; no flattening or
renaming is needed.

## Runner findings

1. `files_and_size` permits only five final suffixes for each of 13 names.
   Monitoring calls it every loop, records its first exception as the reason,
   and sends SIGKILL to the whole process group. A transient `.olean.tmp.7`
   therefore deterministically violates policy if sampled. Listing final
   names alone is insufficient during serialization.
2. The directory scan separately performs `is_symlink`, `is_file`, `stat`
   and later hashing. Rename/disappearance between these operations can raise
   or evade that particular sample. Merely adding a temporary-name pattern
   does not resolve these races or establish a hard total-size limit. The
   file-size rlimit is per file; aggregate checks are sampled.
3. Process creation uses `start_new_session=True`; the timeout PID is used
   as process-group ID. `kill_group` sends SIGKILL; `active.wait(timeout=2)`
   reaps the direct wrapper, not every descendant. `group_members` scans
   `/proc/*/stat`, ignores state Z, and sums reported RSS. Thus an empty
   live-member scan is a point observation, not proof of descendant reaping.
   A zero-RSS member is still considered live by this code.
4. After killing leftovers the ordinary path does not wait for their exit;
   it raises, and `finally` kills/scans again immediately. Delayed cessation
   can correctly leave cleanup unconfirmed. Exceptions while reaping or
   scanning can also interrupt the receipt path. Do not reinterpret later
   absence as this runner having certified its cleanup.
5. Root ownership begins only after absent-root preflight and successful
   mkdir. Existing roots are preserved. When cessation is unconfirmed,
   cleanup is skipped. Otherwise artifacts are listed/hashed before exact-root
   deletion; a vanished file during inventory can prevent deletion. A future
   run needs a separately admitted fresh root and one verification owner.

## Concrete recommendation for a separately admitted run

First obtain and pin the exact matching native implementation of
`lean_compacted_region_save` through the primary; no installation or source
fetch is authorized here. Review its temporary naming, publication and failure
cleanup before declaring a compatible allowlist. If those bytes remain
unavailable, a future bounded experiment must explicitly label a conservative
filename guard as a hypothesis and stop on any unfamiliar output.

For the unchanged legacy 13-module cone, prefer a per-call monitor state:
completed modules admit only their final `.olean`; the active module admits
its exact final name plus an anchored same-directory temporary candidate
`<active>.olean.tmp.[0-9]+`, initially at most one. This proposed pattern covers
the observed filename only; it is **not** a source-proved naming law. Do not
accept temporaries belonging to future modules or treat any temporary as an
import. Check that entries are regular, nonsymlink files in the owned root;
reject unexpected directories and special files too. Count temporary and final
bytes against one aggregate bound, retaining per-file rlimits and bounded logs.
Exceeding the proposed one-temporary cap is a stop, not authority to widen it.

Use race-aware bounded rescans for ENOENT during live publication, retaining
observed unexpected-name evidence. After the direct process exits zero and
all writers are confirmed absent, require the expected final file and zero
temporary files; only then inventory/hash final artifacts and allow the next
import. Never manually rename a leftover temporary into a successful artifact.

On any abort, kill the owned group, reap the direct child, and use a short,
bounded cessation loop with monotonic deadline; retain all observations and
exceptions. Keep the group identity until cessation is confirmed. Check the
owned root identity before cleanup; preserve all failure evidence, then delete
only that exact newly owned root after confirmed writer absence and report
`lexists=false`. If identity, cessation or cleanup is uncertain, quarantine
the root and stop. No retry follows automatically. Native publication is not
proved merely by adding this monitor protocol.

## Parent application and limits

Original parent: intrusion manuscript §§1,3,5, corrected by immutable
birth-level induced-SCC decision §§2–6: every supported original source,
lawful finite construction history and retained qualified extrusion, with
original scopes, fixed dependencies and one joint strategy. No language case
or witness is removed. This packet adds no theorem and changes no semantics.

Inspected declarations include
`YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_bridge` (arbitrary
context, mark, callee, argument; inventory membership, exact route and empty
ViewLogic binder owner) and `.lambda_body_bridge` (arbitrary context, mark,
formal, pattern, body; inventory, owner and route conjunction). These establish
no semantic witness merely from their statements. All 15 bridge printed types
and complete `#print axioms` results remain **NOT RUN**, as in R106.
`YulangClosure.LocalLaws` contains obligations; the
`YulangClosure.SourceProblem.InferenceSoundness`, `.SourceScopedCoverage`
and `.PrincipalCoverage` definitions quantify the missing concrete laws and
shared scoped witnesses, rather than establish them.

First execution prerequisite: exact native serialization behavior and a freshly
reviewed guard/cleanup plan; owner Luna/verification owner. First semantic
premise remains actual scoped logical-witness admission and lawful joint lift
through publication/use, then source-generated native realization; owner
Luna source/proof intake. App/Lambda syntax/owner routing is represented;
logical admissions, full Call/effects/hygiene, other semantic constructors,
source/native correspondence, A/B and production remain open.

## Actual work and stop receipt

Commands were read-only `cat`, `sed`, `rg`, `rg --files`, and Python SHA-256 /
in-memory runner extraction; only `apply_patch` wrote this leased handoff.
Productive targeted reads/hash extraction exited 0. One guessed
`Lean/Util/CompactRegion.lean` lookup produced rg exit 2 / sed missing-file
diagnostics; corrected actual path is `Lean/CompactedRegion.lean`. Native C++
inventory search had no match (exit 1). Some broad searches were truncated;
no conclusion relies on their omitted output. No external paper or native
implementation was read; no claim about either is certified.

Lean/Lake/checker/version/build/test/compiler invocations: **0**. Actual tool
versions: **NOT RUN**; project pin read as `leanprover/lean4:v4.35.0`, no external
packages. No theorem construction, kernel acceptance or new axiom results.
No scratch/cache/generated outputs, process launch, dependency change, Git
mutation, children, or background tasks. One 300-second author packet; exact
elapsed wall time UNKNOWN (no reliable start timer); zero heavy execution
seconds and zero Astra. Remaining work requires separate primary admission.
**All writes STOPPED at revision 1.** Fresh independent review is pending;
this audit does not self-certify or close any parent gate.
