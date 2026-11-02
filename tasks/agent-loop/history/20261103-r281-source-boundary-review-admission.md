# R281 source-boundary review admission

Frozen preparation contract:
`tasks/agent-loop/sprints/extrusion-entry-validity-r281.md`, SHA-256
`4b737c39cb35cd9de013b053eeee4397e48e4f770fa64500969d66b0f658477f`.

Luna completed the 600-second source-view preparation stage. The view contains
38 exact function ranges, 134 byte-exact source payloads and 96 separate
`cfg(test)`-false omissions. Initial Luna integrity check confirmed every
payload SHA and original byte slice, disjointness from omitted spans, all 36
R255 rows, and the additional candidate_context pin. This is preparation
integrity only; it does not establish complete constructor coverage or source
boundary correctness.

Frozen artifacts:

- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-ranges.json` —
  `a94d3ed3245dec8baa012b8fe75e054f4b1819f615474bba5da7b0e852d03f4a`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-cfg-exclusions.json` —
  `3c39decd7832045fa8ff79d5a41f80571aca84a9d5ba13f203214df79688ee20`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-source-view.txt` —
  `66b64c0c9ca440bb03c110953adfce1a6aa218a62bd3a3f028bb04d220a3b8ca`
- `tasks/agent-loop/sprints/extrusion-entry-validity-r281-view-index.json` —
  `d9c47173c35e4e69b0082e8db62eb9f2f73c626d00736a21e21db51073375750`

Admit one fresh, read-only `compiler_referee`, identity
`/root/r281_source_boundary_review`, requested Sol/medium, 300 seconds, no
children. First gate is metadata-only WAITING: verify this admission and R281
contract hashes; do not open source view, ranges, exclusion list or any source
body until Luna separately revalidates the four artifact hashes and sends GO.
The reviewer may inspect the frozen view and pinned source intervals only after
that GO. No code/test/build/Cargo/Lean/probe/Git writes or external source.

The reviewer must independently validate every payload against its exact
original interval; ensure payloads avoid all false-under-production nested cfg
spans; check each exclusion predicate/offset/hash; and identify omitted direct
helper bodies or missing row/level/forest constructor, mutation, restoration,
rollback or resume owner. Any ambiguity or omission is INCOMPLETE and blocks the
Sol owner gate. No later proof review is granted here.
