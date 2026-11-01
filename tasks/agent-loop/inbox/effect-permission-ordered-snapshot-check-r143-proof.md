# R143 frozen native Lean check handoff

Assignment-ID: EFFECT-PERMISSION-ORDERED-SNAPSHOT-KERNEL-CHECK/20261102-R143 proof; revision 1.
Worker: /root/r143_proof, registered lean_prover leaf; observed model/effort UNKNOWN.
Author: /root/r143_proof; descendants: none. Active acknowledgement sent to primary.
Baseline: a51fb4894bfe27714c6f9db8bfbef8dcabe96c86.
Exact write lease: this handoff; optional R143 Lean repair only after actual elaboration diagnostics.
Initial state before invocation 1: no optional repair existed. Invocation 2 below uses the authorized R143 repair. Frozen R140 remains unchanged.

## Source, parent and represented scope

Original source: notes/theory/2026-10-13-intrusion-source-preservation-proof.md §1;
current Authoritative correction: notes/design/2026-10-24-birth-level-scc-intrusion.md §§2–6;
whole original domain: docs/yulang-whole-proof-closure-ja.md §§1–3;
source-owner correction: docs/yulang-source-type-safety-ja.tex sec:owners.
The original all-supported-source quantifiers, lawful finite histories, lexical/type/event scopes,
complete Call, correlated evidence and one shared witness are unchanged. Research drafts are not semantic authority.

Exact original parent, notes/theory/lean/YulangClosure/Contracts.lean:128,
YulangClosure.SourceProblem.InferenceSoundness:
```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```
This is a proposition definition, not a proved concrete instance. No LocalLaws instance or parent witness is supplied.
The checked candidate namespace is YulangClosure.FormalPermissionOrderedSnapshotR140.
Std is its sole import. The R140 review and full R140 proof handoff remain the exact source/statement map.
All six leaves, function children/optional rows, tuple elements/indices including rejected annotated and empty
cases, eight identity tags with seven separate payload types, one shared table, ordered paths/rows/concrete
members including duplicates, separate root entry vector, support gate, AAR/RRR and error nonpublication are represented.
Omissions: native widths (Nat models indices), table registration coverage and chronology, Eq/Clone correspondence,
variable/hole registration side effects, actual Rust State/transaction, real source admission and native execution.
idxOf absent-key sentinel is not authenticated identity. Pure append/comparison lemmas do not identify actual native images.

Parent application: successful kernel checking can establish only the table-local ordered projection lemmas.
It does not construct the sourceJudgment/sameScoped shared witness. First source/native premise remains an authenticated
Rust-to-Lean identity/table map and equality of the same successful invocation's actual suffix and root vectors to
this model (owner: Luna source/proof intake). Consumers/arrival/capture/copy/Catch, A/B, effect hygiene H,
original inference soundness and production remain OPEN. Fresh independent R143 review is primary-owned and pending.

## Protocol and actual evidence

The bundled checker was not invoked: this exact packet authorizes direct Std-only stdin checking and forbids Lake/cache/scratch.
Toolchain pin, lakefile.toml, lake-manifest.json and README verification sections were read; pin is Lean 4.35.0, no external packages.
Native child starts a new session/process group and is pinned with os.sched_setaffinity to the first allowed CPU.
Python subprocess communicate polls at at most 0.1 seconds while /proc/<pid>/stat is sampled for all matching pgrp members;
RSS is sum of resident pages times page size. Threshold is 1073741824 bytes and timeout terminates the whole process group
using TERM with one-second grace then KILL. Sampling is not a hard aggregate memory cap. Native -M1024 is per process.
Raw streams below are complete. No scratch, cache, generated output, installation, environment setup, Lake/Cargo/Rust
build/test, Git command or unrelated write was performed. LEAN_NUM_THREADS=1 is the required per-child environment override.

UTC receipt time: 2026-11-01T02:01:30.803626+00:00

Preliminary result: NATIVE_FAILURE_STOP_OR_REPAIR_REQUIRES_DIAGNOSTIC

### Authenticated inputs

```json
[
  {
    "path": "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean",
    "bytes": 23626,
    "sha256": "da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985",
    "matches": true
  },
  {
    "path": "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "bytes": 9024,
    "sha256": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
    "matches": true
  },
  {
    "path": "tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-proof.md",
    "bytes": 21870,
    "sha256": "a0a8e21563435014b8da3c48bcae871ae87794e4f0ec68d842e243825364de05",
    "matches": true
  },
  {
    "path": "tasks/agent-loop/history/effect-permission-ordered-snapshot-20261102-r140-review.md",
    "bytes": 11552,
    "sha256": "d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624",
    "matches": true
  },
  {
    "path": "tasks/agent-loop/sprints/effect-permission-ordered-snapshot-kernel-check-20261102-r143.md",
    "bytes": 5302,
    "sha256": "0838ea6f2493416c57fdbb1809cf2ad1ae5e87fdd40fe2ccc436954eb3b2d4f7",
    "matches": true
  },
  {
    "path": "tasks/agent-loop/history/effect-permission-ordered-snapshot-kernel-check-20261102-r143-admission.md",
    "bytes": 1040,
    "sha256": "d88f9e5260d58fe269cda82aa8a4dad5366c774117143a959c3586f7e72a249d",
    "matches": true
  }
]
```

### Version preflight metadata and complete monitor samples

```json
{
  "argv": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "--version"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "LEAN_NUM_THREADS": "1",
  "allowed_cpus": [
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19
  ],
  "selected_cpu": 0,
  "pid_pgid": 4,
  "exit": 0,
  "wall_seconds": 0.38964073100942187,
  "user_cpu_seconds": 0.044497999999999996,
  "system_cpu_seconds": 0.063569,
  "peak_sampled_group_rss_bytes": 70930432,
  "termination_reason": null,
  "termination_signals": [],
  "rss_sampling_interval_seconds": 0.1,
  "rss_sampling_guard_is_hard_aggregate_cap": false,
  "samples": [
    {
      "seconds": 0.001575,
      "rss_bytes": 163840,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 163840,
          "utime_ticks": 0,
          "stime_ticks": 0
        }
      ]
    },
    {
      "seconds": 0.10247,
      "rss_bytes": 31821824,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 31821824,
          "utime_ticks": 0,
          "stime_ticks": 1
        }
      ]
    },
    {
      "seconds": 0.203086,
      "rss_bytes": 51269632,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 51269632,
          "utime_ticks": 2,
          "stime_ticks": 3
        }
      ]
    },
    {
      "seconds": 0.303622,
      "rss_bytes": 70930432,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 70930432,
          "utime_ticks": 3,
          "stime_ticks": 5
        }
      ]
    },
    {
      "seconds": 0.389641,
      "rss_bytes": 0,
      "members": []
    }
  ],
  "stdout_sha256": "eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}
```

Complete stdout:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

```

Complete stderr:

```text

```

### Proof invocation 1 metadata and complete monitor samples

```json
{
  "argv": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "--stdin",
    "-j1",
    "-M1024"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "LEAN_NUM_THREADS": "1",
  "allowed_cpus": [
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19
  ],
  "selected_cpu": 0,
  "pid_pgid": 6,
  "exit": 1,
  "wall_seconds": 6.524346414982574,
  "user_cpu_seconds": 2.478939,
  "system_cpu_seconds": 0.92858,
  "peak_sampled_group_rss_bytes": 784080896,
  "termination_reason": null,
  "termination_signals": [],
  "rss_sampling_interval_seconds": 0.1,
  "rss_sampling_guard_is_hard_aggregate_cap": false,
  "samples": [
    {
      "seconds": 0.001702,
      "rss_bytes": 491520,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 491520,
          "utime_ticks": 0,
          "stime_ticks": 0
        }
      ]
    },
    {
      "seconds": 0.102457,
      "rss_bytes": 95256576,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 95256576,
          "utime_ticks": 3,
          "stime_ticks": 1
        }
      ]
    },
    {
      "seconds": 0.202984,
      "rss_bytes": 100171776,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 100171776,
          "utime_ticks": 3,
          "stime_ticks": 3
        }
      ]
    },
    {
      "seconds": 0.303497,
      "rss_bytes": 105086976,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 105086976,
          "utime_ticks": 3,
          "stime_ticks": 5
        }
      ]
    },
    {
      "seconds": 0.404008,
      "rss_bytes": 110821376,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 110821376,
          "utime_ticks": 3,
          "stime_ticks": 7
        }
      ]
    },
    {
      "seconds": 0.504538,
      "rss_bytes": 115572736,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 115572736,
          "utime_ticks": 3,
          "stime_ticks": 9
        }
      ]
    },
    {
      "seconds": 0.605086,
      "rss_bytes": 119996416,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 119996416,
          "utime_ticks": 4,
          "stime_ticks": 11
        }
      ]
    },
    {
      "seconds": 0.705641,
      "rss_bytes": 124583936,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 124583936,
          "utime_ticks": 4,
          "stime_ticks": 13
        }
      ]
    },
    {
      "seconds": 0.806211,
      "rss_bytes": 129662976,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 129662976,
          "utime_ticks": 4,
          "stime_ticks": 15
        }
      ]
    },
    {
      "seconds": 0.906751,
      "rss_bytes": 134742016,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 134742016,
          "utime_ticks": 4,
          "stime_ticks": 17
        }
      ]
    },
    {
      "seconds": 1.007338,
      "rss_bytes": 139493376,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 139493376,
          "utime_ticks": 4,
          "stime_ticks": 18
        }
      ]
    },
    {
      "seconds": 1.107818,
      "rss_bytes": 144244736,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 144244736,
          "utime_ticks": 4,
          "stime_ticks": 20
        }
      ]
    },
    {
      "seconds": 1.208302,
      "rss_bytes": 149651456,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 149651456,
          "utime_ticks": 5,
          "stime_ticks": 22
        }
      ]
    },
    {
      "seconds": 1.308845,
      "rss_bytes": 154730496,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 154730496,
          "utime_ticks": 5,
          "stime_ticks": 24
        }
      ]
    },
    {
      "seconds": 1.409363,
      "rss_bytes": 159809536,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 159809536,
          "utime_ticks": 6,
          "stime_ticks": 25
        }
      ]
    },
    {
      "seconds": 1.510031,
      "rss_bytes": 164233216,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 164233216,
          "utime_ticks": 7,
          "stime_ticks": 27
        }
      ]
    },
    {
      "seconds": 1.610612,
      "rss_bytes": 169148416,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 169148416,
          "utime_ticks": 7,
          "stime_ticks": 28
        }
      ]
    },
    {
      "seconds": 1.711215,
      "rss_bytes": 174391296,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 174391296,
          "utime_ticks": 7,
          "stime_ticks": 30
        }
      ]
    },
    {
      "seconds": 1.811842,
      "rss_bytes": 180916224,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 180916224,
          "utime_ticks": 8,
          "stime_ticks": 32
        }
      ]
    },
    {
      "seconds": 1.912442,
      "rss_bytes": 185831424,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 185831424,
          "utime_ticks": 9,
          "stime_ticks": 33
        }
      ]
    },
    {
      "seconds": 2.01301,
      "rss_bytes": 190910464,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 190910464,
          "utime_ticks": 9,
          "stime_ticks": 35
        }
      ]
    },
    {
      "seconds": 2.11354,
      "rss_bytes": 197955584,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 197955584,
          "utime_ticks": 9,
          "stime_ticks": 37
        }
      ]
    },
    {
      "seconds": 2.214203,
      "rss_bytes": 213684224,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 213684224,
          "utime_ticks": 9,
          "stime_ticks": 39
        }
      ]
    },
    {
      "seconds": 2.314737,
      "rss_bytes": 236556288,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 236556288,
          "utime_ticks": 10,
          "stime_ticks": 41
        }
      ]
    },
    {
      "seconds": 2.415319,
      "rss_bytes": 264540160,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 264540160,
          "utime_ticks": 10,
          "stime_ticks": 43
        }
      ]
    },
    {
      "seconds": 2.515981,
      "rss_bytes": 292065280,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 292065280,
          "utime_ticks": 10,
          "stime_ticks": 46
        }
      ]
    },
    {
      "seconds": 2.616542,
      "rss_bytes": 316968960,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 316968960,
          "utime_ticks": 10,
          "stime_ticks": 48
        }
      ]
    },
    {
      "seconds": 2.717154,
      "rss_bytes": 346624000,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 346624000,
          "utime_ticks": 11,
          "stime_ticks": 51
        }
      ]
    },
    {
      "seconds": 2.817817,
      "rss_bytes": 374116352,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 374116352,
          "utime_ticks": 11,
          "stime_ticks": 54
        }
      ]
    },
    {
      "seconds": 2.91838,
      "rss_bytes": 397709312,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 397709312,
          "utime_ticks": 11,
          "stime_ticks": 57
        }
      ]
    },
    {
      "seconds": 3.019004,
      "rss_bytes": 421793792,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 421793792,
          "utime_ticks": 12,
          "stime_ticks": 58
        }
      ]
    },
    {
      "seconds": 3.119577,
      "rss_bytes": 445222912,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 445222912,
          "utime_ticks": 12,
          "stime_ticks": 60
        }
      ]
    },
    {
      "seconds": 3.220182,
      "rss_bytes": 469143552,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 469143552,
          "utime_ticks": 12,
          "stime_ticks": 63
        }
      ]
    },
    {
      "seconds": 3.320765,
      "rss_bytes": 498110464,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 498110464,
          "utime_ticks": 13,
          "stime_ticks": 65
        }
      ]
    },
    {
      "seconds": 3.421377,
      "rss_bytes": 519245824,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 519245824,
          "utime_ticks": 13,
          "stime_ticks": 67
        }
      ]
    },
    {
      "seconds": 3.521926,
      "rss_bytes": 545951744,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 545951744,
          "utime_ticks": 13,
          "stime_ticks": 70
        }
      ]
    },
    {
      "seconds": 3.622473,
      "rss_bytes": 574590976,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 574590976,
          "utime_ticks": 14,
          "stime_ticks": 72
        }
      ]
    },
    {
      "seconds": 3.722998,
      "rss_bytes": 598347776,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 598347776,
          "utime_ticks": 15,
          "stime_ticks": 75
        }
      ]
    },
    {
      "seconds": 3.823553,
      "rss_bytes": 620793856,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 620793856,
          "utime_ticks": 16,
          "stime_ticks": 77
        }
      ]
    },
    {
      "seconds": 3.924189,
      "rss_bytes": 649732096,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 649732096,
          "utime_ticks": 16,
          "stime_ticks": 79
        }
      ]
    },
    {
      "seconds": 4.024815,
      "rss_bytes": 681287680,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 681287680,
          "utime_ticks": 17,
          "stime_ticks": 82
        }
      ]
    },
    {
      "seconds": 4.125423,
      "rss_bytes": 703143936,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 703143936,
          "utime_ticks": 21,
          "stime_ticks": 83
        }
      ]
    },
    {
      "seconds": 4.226092,
      "rss_bytes": 737521664,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 737521664,
          "utime_ticks": 27,
          "stime_ticks": 86
        }
      ]
    },
    {
      "seconds": 4.326669,
      "rss_bytes": 745525248,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 745525248,
          "utime_ticks": 36,
          "stime_ticks": 86
        }
      ]
    },
    {
      "seconds": 4.427305,
      "rss_bytes": 751943680,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 751943680,
          "utime_ticks": 46,
          "stime_ticks": 86
        }
      ]
    },
    {
      "seconds": 4.527978,
      "rss_bytes": 752291840,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 752291840,
          "utime_ticks": 55,
          "stime_ticks": 86
        }
      ]
    },
    {
      "seconds": 4.628674,
      "rss_bytes": 754880512,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 754880512,
          "utime_ticks": 65,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 4.729587,
      "rss_bytes": 757772288,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 757772288,
          "utime_ticks": 75,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 4.830193,
      "rss_bytes": 761208832,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 761208832,
          "utime_ticks": 84,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 4.930801,
      "rss_bytes": 761208832,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 761208832,
          "utime_ticks": 94,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.031393,
      "rss_bytes": 761372672,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 761372672,
          "utime_ticks": 104,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.131962,
      "rss_bytes": 761372672,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 761372672,
          "utime_ticks": 114,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.232523,
      "rss_bytes": 763633664,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 763633664,
          "utime_ticks": 124,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.333092,
      "rss_bytes": 763961344,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 763961344,
          "utime_ticks": 134,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.433633,
      "rss_bytes": 768155648,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 768155648,
          "utime_ticks": 144,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.534265,
      "rss_bytes": 767569920,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 767569920,
          "utime_ticks": 154,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.634974,
      "rss_bytes": 769781760,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 769781760,
          "utime_ticks": 164,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.736105,
      "rss_bytes": 769781760,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 769781760,
          "utime_ticks": 174,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.836715,
      "rss_bytes": 769781760,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 769781760,
          "utime_ticks": 184,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 5.937309,
      "rss_bytes": 769945600,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 769945600,
          "utime_ticks": 194,
          "stime_ticks": 87
        }
      ]
    },
    {
      "seconds": 6.03809,
      "rss_bytes": 772694016,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 772694016,
          "utime_ticks": 204,
          "stime_ticks": 88
        }
      ]
    },
    {
      "seconds": 6.138627,
      "rss_bytes": 775053312,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 775053312,
          "utime_ticks": 213,
          "stime_ticks": 89
        }
      ]
    },
    {
      "seconds": 6.239217,
      "rss_bytes": 777490432,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 777490432,
          "utime_ticks": 222,
          "stime_ticks": 89
        }
      ]
    },
    {
      "seconds": 6.340446,
      "rss_bytes": 779718656,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 779718656,
          "utime_ticks": 231,
          "stime_ticks": 90
        }
      ]
    },
    {
      "seconds": 6.441351,
      "rss_bytes": 784080896,
      "members": [
        {
          "pid": 6,
          "rss_bytes": 784080896,
          "utime_ticks": 241,
          "stime_ticks": 90
        }
      ]
    },
    {
      "seconds": 6.524346,
      "rss_bytes": 0,
      "members": []
    }
  ],
  "stdout_sha256": "022b2839c5014321ae0de2bcdda0f3b4b688a80c0ba8b8f611d6099ee371ae46",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}
```

Complete stdout:

```text
<stdin>:184:33: error: Application type mismatch: The argument
  table
has type
  Table
but is expected to have type
  Value Node Effect Symbol
in the application
  inventory_order_filter table
<stdin>:185:33: error: Application type mismatch: The argument
  table
has type
  Table
but is expected to have type
  Value Node Effect Symbol
in the application
  inventory_order_filter table
<stdin>:181:37: error: unsolved goals
case function
Owner Occurrence Formal Scope Node Effect Symbol : Type
inst✝⁶ : DecidableEq Owner
inst✝⁵ : DecidableEq Occurrence
inst✝⁴ : DecidableEq Formal
inst✝³ : DecidableEq Scope
inst✝² : DecidableEq Node
inst✝¹ : DecidableEq Effect
inst✝ : DecidableEq Symbol
table : Table
context : Context Owner Occurrence Scope
positive : Bool
path : List Step
argument : Value Node Effect Symbol
ar : Option (Row Node Effect Symbol)
result : Value Node Effect Symbol
rr : Option (Row Node Effect Symbol)
⊢ inventory table context argument (!positive) (path ++ [Step.argument]) ++
      (inventory table context result positive (path ++ [Step.result]) ++
        (emit table context { positive := !positive, path := path ++ [Step.argument], row := ar } ++
          emit table context { positive := positive, path := path ++ [Step.result], row := rr })) =
    List.flatMap (emit table context) (ports argument (!positive) (path ++ [Step.argument])) ++
      (List.flatMap (emit table context) (ports result positive (path ++ [Step.result])) ++
        (emit table context { positive := !positive, path := path ++ [Step.argument], row := ar } ++
          emit table context { positive := positive, path := path ++ [Step.result], row := rr }))
<stdin>:186:51: error: Application type mismatch: The argument
  table
has type
  Table
but is expected to have type
  Elements Node Effect Symbol
in the application
  element_order_filter table
<stdin>:195:33: error: Application type mismatch: The argument
  table
has type
  Table
but is expected to have type
  Value Node Effect Symbol
in the application
  inventory_order_filter table
<stdin>:196:31: error: Application type mismatch: The argument
  table
has type
  Table
but is expected to have type
  Elements Node Effect Symbol
in the application
  element_order_filter table
<stdin>:193:26: error: unsolved goals
case cons
Owner Occurrence Formal Scope Node Effect Symbol : Type
inst✝⁶ : DecidableEq Owner
inst✝⁵ : DecidableEq Occurrence
inst✝⁴ : DecidableEq Formal
inst✝³ : DecidableEq Scope
inst✝² : DecidableEq Node
inst✝¹ : DecidableEq Effect
inst✝ : DecidableEq Symbol
table : Table
context : Context Owner Occurrence Scope
positive : Bool
path : List Step
index : Nat
value : Value Node Effect Symbol
row : Option (Row Node Effect Symbol)
rest : Elements Node Effect Symbol
⊢ inventory table context value positive (path ++ [Step.element index]) ++
      elementInventory table context rest positive path (index + 1) =
    List.flatMap (emit table context) (ports value positive (path ++ [Step.element index])) ++
      List.flatMap (emit table context) (elementPorts rest positive path (index + 1))
<stdin>:248:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:252:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:259:2: error: Tactic `rfl` failed: The left-hand side
  supported (Value.tuple Elements.nil) positive
is not definitionally equal to the right-hand side
  false

Node Effect Symbol : Type
inst✝² : DecidableEq Node
inst✝¹ : DecidableEq Effect
inst✝ : DecidableEq Symbol
positive : Bool
⊢ supported (Value.tuple Elements.nil) positive = false
<stdin>:321:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:351:25: error: unexpected token 'prefix'; expected '_' or identifier
<stdin>:351:31: error: unexpected identifier; expected ':'
<stdin>:352:11: error: unexpected token '++'; expected ':'
@YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (value : YulangClosure.FormalPermissionOrderedSnapshotR140.Value Node Effect Symbol) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step),
  YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context value positive path =
    List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context)
      (YulangClosure.FormalPermissionOrderedSnapshotR140.ports value positive path)
'YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter' depends on axioms: [sorryAx]
@YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (elements : YulangClosure.FormalPermissionOrderedSnapshotR140.Elements Node Effect Symbol) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step) (index : Nat),
  YulangClosure.FormalPermissionOrderedSnapshotR140.elementInventory table context elements positive path index =
    List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context)
      (YulangClosure.FormalPermissionOrderedSnapshotR140.elementPorts elements positive path index)
'YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter' depends on axioms: [sorryAx]
@YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol),
  (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).parameter = context.parameter ∧
    (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).formalPosition =
        List.idxOf
          (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.formalPosition context.owner context.parameter)
          table ∧
      (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).occurrence =
          List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.occurrence context.occurrence) table ∧
        (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).owner =
            List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.owner context.owner) table ∧
          (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).scope =
              List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.scope context.scope) table ∧
            (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).path = path ∧
              (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).sourceRow =
                  List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.node row.position) table ∧
                (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).concrete =
                  List.map
                    (fun effect =>
                      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect effect) table)
                    row.concrete
'YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol),
  (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).concrete.length =
    row.concrete.length
'YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol) (index : Nat),
  (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row).concrete[index]? =
    Option.map
      (fun effect => List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect effect) table)
      row.concrete[index]?
'YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step) (position : Node) (effect : Effect)
  (rest : List Effect),
  (YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path
        { position := position, concrete := effect :: effect :: rest, variables := [] }).concrete =
    List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect effect) table ::
      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect effect) table ::
        List.map
          (fun item => List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect item) table) rest
'YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context
      { positive := Bool.true, path := path, row := Option.some row } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step),
  YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context
      { positive := positive, path := path, row := Option.none } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step) (position : Node) (concrete : List Effect)
  (name : Symbol) (rest : List Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context
      { positive := positive, path := path,
        row := Option.some { position := position, concrete := concrete, variables := name :: rest } } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step) (position : Node) (variables : List Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context
      { positive := positive, path := path,
        row := Option.some { position := position, concrete := [], variables := variables } } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR140.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol),
  row.concrete ≠ [] →
    row.variables = [] →
      YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context
          { positive := Bool.false, path := path, row := Option.some row } =
        [YulangClosure.FormalPermissionOrderedSnapshotR140.record table context path row]
'YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (position : Node) (effect : Effect) (tail : List Effect)
  (name : Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR140.rowAllowed Bool.false
      (Option.some { position := position, concrete := effect :: tail, variables := [name] }) =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol]
  (value : YulangClosure.FormalPermissionOrderedSnapshotR140.Value Node Effect Symbol)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol)
  (rest : YulangClosure.FormalPermissionOrderedSnapshotR140.Elements Node Effect Symbol) (positive : Bool),
  YulangClosure.FormalPermissionOrderedSnapshotR140.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR140.Value.tuple
        (YulangClosure.FormalPermissionOrderedSnapshotR140.Elements.cons value (Option.some row) rest))
      positive =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected' depends on axioms: [propext,
 Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (positive : Bool),
  YulangClosure.FormalPermissionOrderedSnapshotR140.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR140.Value.tuple
        YulangClosure.FormalPermissionOrderedSnapshotR140.Elements.nil)
      positive =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (annotation : YulangClosure.FormalPermissionOrderedSnapshotR140.Annotation Node Effect Symbol)
  (output : List YulangClosure.FormalPermissionOrderedSnapshotR140.PermissionImage),
  YulangClosure.FormalPermissionOrderedSnapshotR140.constructProjection table context annotation = Option.some output ↔
    YulangClosure.FormalPermissionOrderedSnapshotR140.supported annotation.value Bool.false = Bool.true ∧
      output =
        List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR140.emit table context)
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ports annotation.value Bool.false [])
'YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (value : YulangClosure.FormalPermissionOrderedSnapshotR140.Value Node Effect Symbol)
  (before after : Option (YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol)),
  YulangClosure.FormalPermissionOrderedSnapshotR140.nestedProjection table context
      { value := value, rootRow := before } =
    YulangClosure.FormalPermissionOrderedSnapshotR140.nestedProjection table context
      { value := value, rootRow := after }
'YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope)
  (first second : YulangClosure.FormalPermissionOrderedSnapshotR140.Row Node Effect Symbol),
  first.concrete ≠ [] →
    first.variables = [] →
      second.concrete ≠ [] →
        second.variables = [] →
          YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context
              (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows first second) Bool.false [] =
            [YulangClosure.FormalPermissionOrderedSnapshotR140.record table context
                YulangClosure.FormalPermissionOrderedSnapshotR140.aar first,
              YulangClosure.FormalPermissionOrderedSnapshotR140.record table context
                YulangClosure.FormalPermissionOrderedSnapshotR140.rrr second]
'YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context
      (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io)
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io))
      Bool.false [] =
    [YulangClosure.FormalPermissionOrderedSnapshotR140.record table context
        YulangClosure.FormalPermissionOrderedSnapshotR140.aar
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io),
      YulangClosure.FormalPermissionOrderedSnapshotR140.record table context
        YulangClosure.FormalPermissionOrderedSnapshotR140.rrr
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io)]
'YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (first second : Node) (io : Effect),
  YulangClosure.FormalPermissionOrderedSnapshotR140.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io)
        (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io))
      Bool.false =
    Bool.true
'YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR140.PermissionImage.path
      (YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io))
        Bool.false []) =
    [YulangClosure.FormalPermissionOrderedSnapshotR140.aar, YulangClosure.FormalPermissionOrderedSnapshotR140.rrr]
'YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR140.PermissionImage.sourceRow
      (YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io))
        Bool.false []) =
    [List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.node first) table,
      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.node second) table]
'YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR140.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR140.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR140.PermissionImage.concrete
      (YulangClosure.FormalPermissionOrderedSnapshotR140.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR140.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR140.ioRow second io))
        Bool.false []) =
    [[List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect io) table],
      [List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR140.TaggedKey.effect io) table]]
'YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect' depends on axioms: [propext]
<stdin>:437:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix`
<stdin>:438:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix`
@YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success : ∀ {Key : Type} (table : List Key)
  (expected actual : List YulangClosure.FormalPermissionOrderedSnapshotR140.PermissionImage)
  (entryBefore entryAfter : List YulangClosure.FormalPermissionOrderedSnapshotR140.EntryImage)
  (snapshot : YulangClosure.FormalPermissionOrderedSnapshotR140.Snapshot Key),
  YulangClosure.FormalPermissionOrderedSnapshotR140.compareAndFinish table expected actual entryBefore entryAfter =
      Except.ok snapshot →
    actual = expected ∧ entryAfter = entryBefore
'YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot : ∀ {Key : Type}
  (error : YulangClosure.FormalPermissionOrderedSnapshotR140.Failure)
  (snapshot : YulangClosure.FormalPermissionOrderedSnapshotR140.Snapshot Key),
  YulangClosure.FormalPermissionOrderedSnapshotR140.authenticated (Except.error error) ≠ Option.some snapshot
'YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot' depends on axioms: [propext]

```

Complete stderr:

```text

```

## Target coverage and stop receipt

Target names from frozen paired #check/#print axioms surface:

- `YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success`
- `YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot`

Invocation 1 target list above is the frozen R140 surface; the final complete R143 coverage and audit follow below.

## Genuine elaboration repair and proof invocation 2

Invocation 1 was REJECTED: exit 1, actual elaboration errors and recovery-generated sorryAx; appended_suffix did not exist.
R140 remains immutable and rejected as checked input. The optional R143 module preserves all 25 proposition statements,
with namespace R143 and the bound variable prefix renamed initialPrefix. Mutual recursive calls now use only their
recursive arguments, since table/context are fixed section variables within the mutual block; empty_tuple_rejected
uses the supported defining equation rather than rfl. No semantic predicate, quantifier, hypothesis, constructor or
conclusion was changed. Only comments, namespace, these proof terms and one alpha-renamed binder differ.

Native identity and original input hash rechecked immediately before invocation 2.

```json
{
  "argv": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "--stdin",
    "-j1",
    "-M1024"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "input_path": "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR143.lean",
  "input_bytes": 23632,
  "input_sha256": "88efc42949e7d912189313b670bc3537879d4b2eb6998b195ba606e44de536e9",
  "binary_sha256_rechecked": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
  "R140_sha256_rechecked": "da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985",
  "LEAN_NUM_THREADS": "1",
  "allowed_cpus": [
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19
  ],
  "selected_cpu": 0,
  "pid_pgid": 4,
  "exit": 0,
  "wall_seconds": 6.112120202014921,
  "user_cpu_seconds": 2.077482,
  "system_cpu_seconds": 0.740807,
  "peak_sampled_group_rss_bytes": 781639680,
  "termination_reason": null,
  "termination_signals": [],
  "rss_sampling_interval_seconds": 0.1,
  "rss_sampling_guard_is_hard_aggregate_cap": false,
  "samples": [
    {
      "seconds": 0.001646,
      "rss_bytes": 163840,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 163840,
          "utime_ticks": 0,
          "stime_ticks": 0
        }
      ]
    },
    {
      "seconds": 0.102539,
      "rss_bytes": 31662080,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 31662080,
          "utime_ticks": 0,
          "stime_ticks": 2
        }
      ]
    },
    {
      "seconds": 0.203092,
      "rss_bytes": 52420608,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 52420608,
          "utime_ticks": 2,
          "stime_ticks": 2
        }
      ]
    },
    {
      "seconds": 0.303592,
      "rss_bytes": 73883648,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 73883648,
          "utime_ticks": 3,
          "stime_ticks": 4
        }
      ]
    },
    {
      "seconds": 0.404142,
      "rss_bytes": 92962816,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 92962816,
          "utime_ticks": 4,
          "stime_ticks": 4
        }
      ]
    },
    {
      "seconds": 0.504649,
      "rss_bytes": 99188736,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 99188736,
          "utime_ticks": 4,
          "stime_ticks": 5
        }
      ]
    },
    {
      "seconds": 0.605154,
      "rss_bytes": 105414656,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 105414656,
          "utime_ticks": 4,
          "stime_ticks": 7
        }
      ]
    },
    {
      "seconds": 0.705653,
      "rss_bytes": 111476736,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 111476736,
          "utime_ticks": 4,
          "stime_ticks": 8
        }
      ]
    },
    {
      "seconds": 0.806178,
      "rss_bytes": 116883456,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 116883456,
          "utime_ticks": 5,
          "stime_ticks": 8
        }
      ]
    },
    {
      "seconds": 0.906715,
      "rss_bytes": 123109376,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 123109376,
          "utime_ticks": 5,
          "stime_ticks": 9
        }
      ]
    },
    {
      "seconds": 1.007194,
      "rss_bytes": 128352256,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 128352256,
          "utime_ticks": 5,
          "stime_ticks": 11
        }
      ]
    },
    {
      "seconds": 1.107689,
      "rss_bytes": 133431296,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 133431296,
          "utime_ticks": 6,
          "stime_ticks": 12
        }
      ]
    },
    {
      "seconds": 1.208167,
      "rss_bytes": 138182656,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 138182656,
          "utime_ticks": 6,
          "stime_ticks": 13
        }
      ]
    },
    {
      "seconds": 1.308661,
      "rss_bytes": 143261696,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 143261696,
          "utime_ticks": 7,
          "stime_ticks": 14
        }
      ]
    },
    {
      "seconds": 1.40919,
      "rss_bytes": 148668416,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 148668416,
          "utime_ticks": 7,
          "stime_ticks": 16
        }
      ]
    },
    {
      "seconds": 1.509721,
      "rss_bytes": 154402816,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 154402816,
          "utime_ticks": 7,
          "stime_ticks": 18
        }
      ]
    },
    {
      "seconds": 1.610319,
      "rss_bytes": 159809536,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 159809536,
          "utime_ticks": 7,
          "stime_ticks": 19
        }
      ]
    },
    {
      "seconds": 1.710819,
      "rss_bytes": 165052416,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 165052416,
          "utime_ticks": 7,
          "stime_ticks": 21
        }
      ]
    },
    {
      "seconds": 1.811324,
      "rss_bytes": 170950656,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 170950656,
          "utime_ticks": 7,
          "stime_ticks": 23
        }
      ]
    },
    {
      "seconds": 1.911838,
      "rss_bytes": 178667520,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 178667520,
          "utime_ticks": 7,
          "stime_ticks": 24
        }
      ]
    },
    {
      "seconds": 2.012367,
      "rss_bytes": 184074240,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 184074240,
          "utime_ticks": 7,
          "stime_ticks": 26
        }
      ]
    },
    {
      "seconds": 2.112899,
      "rss_bytes": 189480960,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 189480960,
          "utime_ticks": 7,
          "stime_ticks": 27
        }
      ]
    },
    {
      "seconds": 2.213442,
      "rss_bytes": 196853760,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 196853760,
          "utime_ticks": 7,
          "stime_ticks": 29
        }
      ]
    },
    {
      "seconds": 2.313974,
      "rss_bytes": 213401600,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 213401600,
          "utime_ticks": 8,
          "stime_ticks": 30
        }
      ]
    },
    {
      "seconds": 2.414548,
      "rss_bytes": 235782144,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 235782144,
          "utime_ticks": 8,
          "stime_ticks": 32
        }
      ]
    },
    {
      "seconds": 2.515139,
      "rss_bytes": 265732096,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 265732096,
          "utime_ticks": 8,
          "stime_ticks": 34
        }
      ]
    },
    {
      "seconds": 2.615724,
      "rss_bytes": 296042496,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 296042496,
          "utime_ticks": 8,
          "stime_ticks": 37
        }
      ]
    },
    {
      "seconds": 2.716298,
      "rss_bytes": 324222976,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 324222976,
          "utime_ticks": 8,
          "stime_ticks": 39
        }
      ]
    },
    {
      "seconds": 2.816809,
      "rss_bytes": 356499456,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 356499456,
          "utime_ticks": 9,
          "stime_ticks": 41
        }
      ]
    },
    {
      "seconds": 2.917323,
      "rss_bytes": 385630208,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 385630208,
          "utime_ticks": 11,
          "stime_ticks": 41
        }
      ]
    },
    {
      "seconds": 3.017915,
      "rss_bytes": 410370048,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 410370048,
          "utime_ticks": 11,
          "stime_ticks": 43
        }
      ]
    },
    {
      "seconds": 3.118528,
      "rss_bytes": 436748288,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 436748288,
          "utime_ticks": 11,
          "stime_ticks": 45
        }
      ]
    },
    {
      "seconds": 3.21903,
      "rss_bytes": 460668928,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 460668928,
          "utime_ticks": 12,
          "stime_ticks": 47
        }
      ]
    },
    {
      "seconds": 3.31965,
      "rss_bytes": 490946560,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 490946560,
          "utime_ticks": 12,
          "stime_ticks": 49
        }
      ]
    },
    {
      "seconds": 3.420166,
      "rss_bytes": 513228800,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 513228800,
          "utime_ticks": 13,
          "stime_ticks": 51
        }
      ]
    },
    {
      "seconds": 3.520714,
      "rss_bytes": 541736960,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 541736960,
          "utime_ticks": 13,
          "stime_ticks": 53
        }
      ]
    },
    {
      "seconds": 3.621275,
      "rss_bytes": 572014592,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 572014592,
          "utime_ticks": 13,
          "stime_ticks": 56
        }
      ]
    },
    {
      "seconds": 3.72183,
      "rss_bytes": 595771392,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 595771392,
          "utime_ticks": 14,
          "stime_ticks": 57
        }
      ]
    },
    {
      "seconds": 3.822408,
      "rss_bytes": 618217472,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 618217472,
          "utime_ticks": 15,
          "stime_ticks": 59
        }
      ]
    },
    {
      "seconds": 3.92294,
      "rss_bytes": 648626176,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 648626176,
          "utime_ticks": 16,
          "stime_ticks": 61
        }
      ]
    },
    {
      "seconds": 4.023527,
      "rss_bytes": 682254336,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 682254336,
          "utime_ticks": 18,
          "stime_ticks": 62
        }
      ]
    },
    {
      "seconds": 4.124121,
      "rss_bytes": 716656640,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 716656640,
          "utime_ticks": 21,
          "stime_ticks": 65
        }
      ]
    },
    {
      "seconds": 4.22464,
      "rss_bytes": 741801984,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 741801984,
          "utime_ticks": 27,
          "stime_ticks": 67
        }
      ]
    },
    {
      "seconds": 4.32513,
      "rss_bytes": 747425792,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 747425792,
          "utime_ticks": 37,
          "stime_ticks": 67
        }
      ]
    },
    {
      "seconds": 4.425661,
      "rss_bytes": 752312320,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 752312320,
          "utime_ticks": 46,
          "stime_ticks": 67
        }
      ]
    },
    {
      "seconds": 4.526338,
      "rss_bytes": 754835456,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 754835456,
          "utime_ticks": 56,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 4.626918,
      "rss_bytes": 757297152,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 757297152,
          "utime_ticks": 65,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 4.727513,
      "rss_bytes": 760868864,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 760868864,
          "utime_ticks": 75,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 4.82809,
      "rss_bytes": 761032704,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 761032704,
          "utime_ticks": 84,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 4.928719,
      "rss_bytes": 761032704,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 761032704,
          "utime_ticks": 94,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 5.029304,
      "rss_bytes": 763293696,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 763293696,
          "utime_ticks": 105,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 5.129878,
      "rss_bytes": 763621376,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 763621376,
          "utime_ticks": 115,
          "stime_ticks": 68
        }
      ]
    },
    {
      "seconds": 5.230449,
      "rss_bytes": 768307200,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 768307200,
          "utime_ticks": 124,
          "stime_ticks": 69
        }
      ]
    },
    {
      "seconds": 5.33102,
      "rss_bytes": 770576384,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 770576384,
          "utime_ticks": 134,
          "stime_ticks": 69
        }
      ]
    },
    {
      "seconds": 5.431794,
      "rss_bytes": 770576384,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 770576384,
          "utime_ticks": 144,
          "stime_ticks": 69
        }
      ]
    },
    {
      "seconds": 5.532343,
      "rss_bytes": 770351104,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 770351104,
          "utime_ticks": 154,
          "stime_ticks": 69
        }
      ]
    },
    {
      "seconds": 5.632858,
      "rss_bytes": 772612096,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 772612096,
          "utime_ticks": 164,
          "stime_ticks": 69
        }
      ]
    },
    {
      "seconds": 5.733407,
      "rss_bytes": 774799360,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 774799360,
          "utime_ticks": 173,
          "stime_ticks": 70
        }
      ]
    },
    {
      "seconds": 5.833964,
      "rss_bytes": 774963200,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 774963200,
          "utime_ticks": 183,
          "stime_ticks": 70
        }
      ]
    },
    {
      "seconds": 5.934487,
      "rss_bytes": 777441280,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 777441280,
          "utime_ticks": 193,
          "stime_ticks": 70
        }
      ]
    },
    {
      "seconds": 6.035023,
      "rss_bytes": 781639680,
      "members": [
        {
          "pid": 4,
          "rss_bytes": 781639680,
          "utime_ticks": 202,
          "stime_ticks": 71
        }
      ]
    },
    {
      "seconds": 6.11212,
      "rss_bytes": 0,
      "members": []
    }
  ],
  "stdout_sha256": "72e2c9d0a63e64d6858486156e47cd2c18d50ee43148fb97fd03e2a67e60c65b",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}
```

Complete stdout:

```text
<stdin>:248:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:252:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:257:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:321:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted`:
  [DecidableEq Node]
  [DecidableEq Effect]
  [DecidableEq Symbol]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@YulangClosure.FormalPermissionOrderedSnapshotR143.inventory_order_filter : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (value : YulangClosure.FormalPermissionOrderedSnapshotR143.Value Node Effect Symbol) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step),
  YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context value positive path =
    List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context)
      (YulangClosure.FormalPermissionOrderedSnapshotR143.ports value positive path)
'YulangClosure.FormalPermissionOrderedSnapshotR143.inventory_order_filter' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.element_order_filter : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (elements : YulangClosure.FormalPermissionOrderedSnapshotR143.Elements Node Effect Symbol) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step) (index : Nat),
  YulangClosure.FormalPermissionOrderedSnapshotR143.elementInventory table context elements positive path index =
    List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context)
      (YulangClosure.FormalPermissionOrderedSnapshotR143.elementPorts elements positive path index)
'YulangClosure.FormalPermissionOrderedSnapshotR143.element_order_filter' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.record_fields : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol),
  (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).parameter = context.parameter ∧
    (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).formalPosition =
        List.idxOf
          (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.formalPosition context.owner context.parameter)
          table ∧
      (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).occurrence =
          List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.occurrence context.occurrence) table ∧
        (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).owner =
            List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.owner context.owner) table ∧
          (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).scope =
              List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.scope context.scope) table ∧
            (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).path = path ∧
              (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).sourceRow =
                  List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.node row.position) table ∧
                (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).concrete =
                  List.map
                    (fun effect =>
                      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect effect) table)
                    row.concrete
'YulangClosure.FormalPermissionOrderedSnapshotR143.record_fields' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_length : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol),
  (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).concrete.length =
    row.concrete.length
'YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_length' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_position : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol) (index : Nat),
  (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row).concrete[index]? =
    Option.map
      (fun effect => List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect effect) table)
      row.concrete[index]?
'YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_position' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_duplicates : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step) (position : Node) (effect : Effect)
  (rest : List Effect),
  (YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path
        { position := position, concrete := effect :: effect :: rest, variables := [] }).concrete =
    List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect effect) table ::
      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect effect) table ::
        List.map
          (fun item => List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect item) table) rest
'YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_duplicates' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR143.positive_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context
      { positive := Bool.true, path := path, row := Option.some row } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR143.positive_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.omitted_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step),
  YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context
      { positive := positive, path := path, row := Option.none } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR143.omitted_filtered' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR143.symbolic_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step) (position : Node) (concrete : List Effect)
  (name : Symbol) (rest : List Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context
      { positive := positive, path := path,
        row := Option.some { position := position, concrete := concrete, variables := name :: rest } } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR143.symbolic_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.empty_filtered : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (positive : Bool)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step) (position : Node) (variables : List Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context
      { positive := positive, path := path,
        row := Option.some { position := position, concrete := [], variables := variables } } =
    []
'YulangClosure.FormalPermissionOrderedSnapshotR143.empty_filtered' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_emitted : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (path : List YulangClosure.FormalPermissionOrderedSnapshotR143.Step)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol),
  row.concrete ≠ [] →
    row.variables = [] →
      YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context
          { positive := Bool.false, path := path, row := Option.some row } =
        [YulangClosure.FormalPermissionOrderedSnapshotR143.record table context path row]
'YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_emitted' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (position : Node) (effect : Effect) (tail : List Effect)
  (name : Symbol),
  YulangClosure.FormalPermissionOrderedSnapshotR143.rowAllowed Bool.false
      (Option.some { position := position, concrete := effect :: tail, variables := [name] }) =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol]
  (value : YulangClosure.FormalPermissionOrderedSnapshotR143.Value Node Effect Symbol)
  (row : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol)
  (rest : YulangClosure.FormalPermissionOrderedSnapshotR143.Elements Node Effect Symbol) (positive : Bool),
  YulangClosure.FormalPermissionOrderedSnapshotR143.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR143.Value.tuple
        (YulangClosure.FormalPermissionOrderedSnapshotR143.Elements.cons value (Option.some row) rest))
      positive =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected' depends on axioms: [propext,
 Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (positive : Bool),
  YulangClosure.FormalPermissionOrderedSnapshotR143.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR143.Value.tuple
        YulangClosure.FormalPermissionOrderedSnapshotR143.Elements.nil)
      positive =
    Bool.false
'YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR143.projection_success : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (annotation : YulangClosure.FormalPermissionOrderedSnapshotR143.Annotation Node Effect Symbol)
  (output : List YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage),
  YulangClosure.FormalPermissionOrderedSnapshotR143.constructProjection table context annotation = Option.some output ↔
    YulangClosure.FormalPermissionOrderedSnapshotR143.supported annotation.value Bool.false = Bool.true ∧
      output =
        List.flatMap (YulangClosure.FormalPermissionOrderedSnapshotR143.emit table context)
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ports annotation.value Bool.false [])
'YulangClosure.FormalPermissionOrderedSnapshotR143.projection_success' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR143.root_row_separate : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (value : YulangClosure.FormalPermissionOrderedSnapshotR143.Value Node Effect Symbol)
  (before after : Option (YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol)),
  YulangClosure.FormalPermissionOrderedSnapshotR143.nestedProjection table context
      { value := value, rootRow := before } =
    YulangClosure.FormalPermissionOrderedSnapshotR143.nestedProjection table context
      { value := value, rootRow := after }
'YulangClosure.FormalPermissionOrderedSnapshotR143.root_row_separate' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR143.fixture_order : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope)
  (first second : YulangClosure.FormalPermissionOrderedSnapshotR143.Row Node Effect Symbol),
  first.concrete ≠ [] →
    first.variables = [] →
      second.concrete ≠ [] →
        second.variables = [] →
          YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context
              (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows first second) Bool.false [] =
            [YulangClosure.FormalPermissionOrderedSnapshotR143.record table context
                YulangClosure.FormalPermissionOrderedSnapshotR143.aar first,
              YulangClosure.FormalPermissionOrderedSnapshotR143.record table context
                YulangClosure.FormalPermissionOrderedSnapshotR143.rrr second]
'YulangClosure.FormalPermissionOrderedSnapshotR143.fixture_order' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.exact_aar_rrr_fixture : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context
      (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io)
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io))
      Bool.false [] =
    [YulangClosure.FormalPermissionOrderedSnapshotR143.record table context
        YulangClosure.FormalPermissionOrderedSnapshotR143.aar
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io),
      YulangClosure.FormalPermissionOrderedSnapshotR143.record table context
        YulangClosure.FormalPermissionOrderedSnapshotR143.rrr
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io)]
'YulangClosure.FormalPermissionOrderedSnapshotR143.exact_aar_rrr_fixture' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted : ∀ {Node Effect Symbol : Type}
  [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol] (first second : Node) (io : Effect),
  YulangClosure.FormalPermissionOrderedSnapshotR143.supported
      (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io)
        (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io))
      Bool.false =
    Bool.true
'YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_paths : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage.path
      (YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io))
        Bool.false []) =
    [YulangClosure.FormalPermissionOrderedSnapshotR143.aar, YulangClosure.FormalPermissionOrderedSnapshotR143.rrr]
'YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_paths' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_rows : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage.sourceRow
      (YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io))
        Bool.false []) =
    [List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.node first) table,
      List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.node second) table]
'YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_rows' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_shared_effect : ∀
  {Owner Occurrence Formal Scope Node Effect Symbol : Type} [inst : DecidableEq Owner] [inst_1 : DecidableEq Occurrence]
  [inst_2 : DecidableEq Formal] [inst_3 : DecidableEq Scope] [inst_4 : DecidableEq Node] [inst_5 : DecidableEq Effect]
  [inst_6 : DecidableEq Symbol] (table : YulangClosure.FormalPermissionOrderedSnapshotR143.Table)
  (context : YulangClosure.FormalPermissionOrderedSnapshotR143.Context Owner Occurrence Scope) (first second : Node)
  (io : Effect),
  List.map YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage.concrete
      (YulangClosure.FormalPermissionOrderedSnapshotR143.inventory table context
        (YulangClosure.FormalPermissionOrderedSnapshotR143.fixtureRows
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow first io)
          (YulangClosure.FormalPermissionOrderedSnapshotR143.ioRow second io))
        Bool.false []) =
    [[List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect io) table],
      [List.idxOf (YulangClosure.FormalPermissionOrderedSnapshotR143.TaggedKey.effect io) table]]
'YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_shared_effect' depends on axioms: [propext]
YulangClosure.FormalPermissionOrderedSnapshotR143.appended_suffix : ∀
  (initialPrefix suffix : List YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage),
  List.drop initialPrefix.length (initialPrefix ++ suffix) = suffix
'YulangClosure.FormalPermissionOrderedSnapshotR143.appended_suffix' depends on axioms: [propext]
@YulangClosure.FormalPermissionOrderedSnapshotR143.comparison_success : ∀ {Key : Type} (table : List Key)
  (expected actual : List YulangClosure.FormalPermissionOrderedSnapshotR143.PermissionImage)
  (entryBefore entryAfter : List YulangClosure.FormalPermissionOrderedSnapshotR143.EntryImage)
  (snapshot : YulangClosure.FormalPermissionOrderedSnapshotR143.Snapshot Key),
  YulangClosure.FormalPermissionOrderedSnapshotR143.compareAndFinish table expected actual entryBefore entryAfter =
      Except.ok snapshot →
    actual = expected ∧ entryAfter = entryBefore
'YulangClosure.FormalPermissionOrderedSnapshotR143.comparison_success' does not depend on any axioms
@YulangClosure.FormalPermissionOrderedSnapshotR143.error_excludes_snapshot : ∀ {Key : Type}
  (error : YulangClosure.FormalPermissionOrderedSnapshotR143.Failure)
  (snapshot : YulangClosure.FormalPermissionOrderedSnapshotR143.Snapshot Key),
  YulangClosure.FormalPermissionOrderedSnapshotR143.authenticated (Except.error error) ≠ Option.some snapshot
'YulangClosure.FormalPermissionOrderedSnapshotR143.error_excludes_snapshot' depends on axioms: [propext]

```

Complete stderr:

```text

```

## Final evidence classification and complete audit summary

Outcome class: proof candidate, KERNEL_ACCEPTED_R143_PENDING_FRESH_INDEPENDENT_REVIEW.
The exact frozen R140 file is REJECTED by invocation 1, not silently relabeled as checked.
R143 source repair is checker-accepted on invocation 2; KERNEL_CHECKED_RESEARCH_ONLY acceptance remains
conditional on the primary-assigned fresh independent review. No self-certification or production promotion.
All 25 target names have exactly one complete printed type and exactly one complete axiom result in invocation 2.
All 25 are theorem declarations in the actual source, not proposition definitions or axioms. Full printed types
and complete raw audit output are retained verbatim above. Four unused-section-variable linter warnings remain;
they change no hypotheses and are not hidden or disabled. No further Lean invocation is needed or authorized
without another genuine source repair. The third available invocation is unused.

| Fully qualified theorem | Complete transitive axiom list |
| --- | --- |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.inventory_order_filter` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.element_order_filter` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.record_fields` | `[]` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_length` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_position` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_duplicates` | `[]` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.positive_filtered` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.omitted_filtered` | `[]` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.symbolic_filtered` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.empty_filtered` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_emitted` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected` | `propext, Classical.choice, Quot.sound` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected` | `propext, Quot.sound` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected` | `propext, Quot.sound` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.projection_success` | `propext, Quot.sound` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.root_row_separate` | `[]` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.fixture_order` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_aar_rrr_fixture` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted` | `propext, Quot.sound` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_paths` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_rows` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_shared_effect` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.appended_suffix` | `propext` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.comparison_success` | `[]` |
| `YulangClosure.FormalPermissionOrderedSnapshotR143.error_excludes_snapshot` | `propext` |

Successful stdout SHA-256 was recomputed from the exact retained raw text and matches its capture metadata.
Static source scan found no sorry/admit/project axiom/sorryAx/kernel bypass/native_decide. The scan is supplementary;
the actual per-theorem transitive outputs above supply the dependency audit. Std supplies the imported library;
no project import, generated olean or shared cache was written. Installed Lean commit is
eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release, x86_64-unknown-linux-gnu.

### Exact R140-to-R143 source delta

```diff
--- FormalPermissionOrderedSnapshotR140.lean
+++ FormalPermissionOrderedSnapshotR143.lean
@@ -1,14 +1,14 @@
 import Std
 
 /-!
-R140 constructed, UNCHECKED ordered projection. No executable verification is
-authorized by this packet. No theorem below asserts Rust/native correspondence.
+R143 repair of the frozen R140 ordered projection after actual elaboration
+diagnostics. Kernel status is recorded in the R143 check handoff. No theorem below asserts Rust/native correspondence.
 The eight identity tags retain their distinct payload types; FormalPosition is
 owner/index, separately from Formal. All raw codes refer to one supplied table.
 idxOf on an unregistered key is a length sentinel, not authenticated identity.
 The order/filter theorems do not assume code injectivity or native equality.
 -/
-namespace YulangClosure.FormalPermissionOrderedSnapshotR140
+namespace YulangClosure.FormalPermissionOrderedSnapshotR143
 
 inductive TaggedKey (Owner Occurrence Formal Scope Node Effect Symbol : Type) where
   | owner : Owner → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
@@ -181,9 +181,9 @@
     | function argument ar result rr =>
         simp only [inventory, ports, List.flatMap_append, List.flatMap_cons,
           List.flatMap_nil, List.append_nil,
-          inventory_order_filter table context argument (!positive) (path ++ [.argument]),
-          inventory_order_filter table context result positive (path ++ [.result]), List.append_assoc]
-    | tuple elements => exact element_order_filter table context elements positive path 0
+          inventory_order_filter argument (!positive) (path ++ [.argument]),
+          inventory_order_filter result positive (path ++ [.result]), List.append_assoc]
+    | tuple elements => exact element_order_filter elements positive path 0
   theorem element_order_filter (elements : Elements Node Effect Symbol) (positive : Bool)
       (path : List Step) (index : Nat) :
       elementInventory table context elements positive path index =
@@ -192,8 +192,8 @@
     | nil => rfl
     | cons value row rest =>
         simp only [elementInventory, elementPorts, List.flatMap_append,
-          inventory_order_filter table context value positive (path ++ [.element index]),
-          element_order_filter table context rest positive path (index + 1)]
+          inventory_order_filter value positive (path ++ [.element index]),
+          element_order_filter rest positive path (index + 1)]
 end
 
 theorem record_fields (path : List Step) (row : Row Node Effect Symbol) :
@@ -256,7 +256,7 @@
 
 theorem empty_tuple_rejected (positive : Bool) :
     supported (Value.tuple (Elements.nil : Elements Node Effect Symbol)) positive = false := by
-  rfl
+  simp only [supported]
 
 end Theorems
 
@@ -348,8 +348,8 @@
 
 /-- Pure append algebra only: connecting prefix/suffix to an actual same call
 and State is an external source obligation, never a premise hidden here. -/
-theorem appended_suffix (prefix suffix : List PermissionImage) :
-    (prefix ++ suffix).drop prefix.length = suffix := by
+theorem appended_suffix (initialPrefix suffix : List PermissionImage) :
+    (initialPrefix ++ suffix).drop initialPrefix.length = suffix := by
   simp
 
 structure Snapshot (Key : Type) where
@@ -385,58 +385,58 @@
     authenticated (.error error) ≠ some snapshot := by
   simp [authenticated]
 
-end YulangClosure.FormalPermissionOrderedSnapshotR140
-
-
--- Future complete audit surface; NOT EXECUTED under R140.
+end YulangClosure.FormalPermissionOrderedSnapshotR143
+
+
+-- Complete audit surface for the R143 direct native check.
 set_option pp.fullNames true
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success
-#check @YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot
-#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.inventory_order_filter
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.inventory_order_filter
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.element_order_filter
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.element_order_filter
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.record_fields
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.record_fields
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_length
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_length
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_position
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_position
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_duplicates
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_duplicates
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.positive_filtered
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.positive_filtered
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.omitted_filtered
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.omitted_filtered
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.symbolic_filtered
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.symbolic_filtered
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.empty_filtered
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.empty_filtered
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_emitted
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.concrete_emitted
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.mixed_negative_rejected
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.tuple_annotated_child_rejected
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.empty_tuple_rejected
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.projection_success
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.projection_success
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.root_row_separate
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.root_row_separate
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.fixture_order
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.fixture_order
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.exact_aar_rrr_fixture
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.exact_aar_rrr_fixture
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_admitted
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_paths
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_paths
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_rows
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_rows
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_shared_effect
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.exact_fixture_shared_effect
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.appended_suffix
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.appended_suffix
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.comparison_success
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.comparison_success
+#check @YulangClosure.FormalPermissionOrderedSnapshotR143.error_excludes_snapshot
+#print axioms YulangClosure.FormalPermissionOrderedSnapshotR143.error_excludes_snapshot

```

### Source/dependency/artifact byte revisions

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | 34671 | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | 7812 | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `docs/yulang-whole-proof-closure-ja.md` | 57870 | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |
| `docs/yulang-source-type-safety-ja.tex` | 184349 | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | 7467 | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/lean-toolchain` | 25 | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | 311 | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | 145 | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean` | 23626 | `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985` |
| `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR143.lean` | 23632 | `88efc42949e7d912189313b670bc3537879d4b2eb6998b195ba606e44de536e9` |

### Resources, remaining goal and cessation

Proof invocations: 2/3, aggregate native proof wall 12.636466617s/240s; remaining 227.363533383s is unspent and does not authorize another retry.
Aggregate proof child user+system CPU 6.225808s; each native process was pinned to CPU 0 with LEAN_NUM_THREADS=1.
Invocation 1 max sampled RSS 784080896 bytes; invocation 2 max 781639680 bytes.
Nominal monitor wait was 0.1s; actual maximum interval between recorded proof samples was 0.101229s, including /proc scan/scheduling overhead.
This is explicitly a sampling guard, not a hard aggregate memory cap. No observed threshold, timeout, environment/thread
failure, or termination event occurred. Native process groups exited and final samples contain no group members.
Version preflight is separately retained above; no attempt budget was reset.

Local kernel premise is discharged for R143's unchanged mathematical statements, pending independent review of
this exact artifact and full capture. Original parent application remains blocked first on authentic native identity/table
and same-invocation suffix equality, owned by Luna source/proof intake. The actual parent still requires
`∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a` for every original supported successful input; no such
concrete witness is constructed by these projection lemmas. No counterexample to the original parent is claimed.
Mutual TODO R143-NATIVE-TABLE-1: source/proof intake supplies an authenticated Rust-to-Lean identity/table map,
with registered-key coverage and exact same-call expected/actual image equality; first falsifier is a constructor/order/
retained-field mismatch. This TODO is not a lease or semantics decision.

Exact writes: R143 Lean repair and this sole handoff. Scratch paths: none. Generated/cache paths: none.
All other source, compiler, expected-output, rule/configuration, shared state/index and Git paths remained untouched.
No children or unresolved descendant leases. All native children are reaped; no remaining verification process.
Worker state: **STOPPED_WRITING** after this final freeze. Primary owns fresh review/adjudication/integration.
