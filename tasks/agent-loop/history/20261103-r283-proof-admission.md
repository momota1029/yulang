# R283 proof admission

Admit the bounded Lean model trial under
`tasks/agent-loop/sprints/extrusion-row-validity-r283.md`, SHA-256
`6ef81be17b0a3377e2563967ba515c7f31bba6dfec9ccc7f164b46d22c5a4885`.
Dispatcher `/root/r272_goal_dispatch` selected this after R282's Luna
preparation STOP. Preserve R282's exact STOP receipt and full 600s charge; its
boundary-review and proof stages were never issued.

Luna resolved native Lake at
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Lake reports `5.0.0-src+eb6cafb`; `lake env lean --version` reports Lean
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, matching
`lean-toolchain` (`leanprover/lean4:v4.35.0`). The Lake manifest declares no
packages; `lakefile.toml` pins `-j1 -M1024`.

The exact recursive import cone of `OriginalExtrusionWork.lean` has 11
workspace modules, all present and hash-pinned below. Luna's read-only
`git status --porcelain -- <cone/config>` returned no changes. No external
source bodies are required. The source/model distinction remains explicit.

| SHA-256 | Imported module |
|---|---|
| `9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8` | `NativeContextExpansion.lean` |
| `f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e` | `NativeMergeExpansion.lean` |
| `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` | `NativeRecordPlan.lean` |
| `1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a` | `NativeRelationInterner.lean` |
| `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` | `NativeReplayCoverage.lean` |
| `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` | `NativeReplayCurrent.lean` |
| `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` | `NativeValuePorts.lean` |
| `81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc` | `NativeValueStructure.lean` |
| `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58` | `OriginalExtrusionWork.lean` |
| `a89a316ea72e472b0e2c09effc144730dc4c683228008caf42a433d0a969a6dd` | `OriginalInferenceTerminationResolution.lean` |
| `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` | `RecordBoundaryPreservation.lean` |

Project configuration pins: `lakefile.toml`
`212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
`lake-manifest.json`
`058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`, and
`lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.

Live roster synchronized before assignment: Luna RUNNING; all earlier listed
children/selector completed, with no other RUNNING or WAITING child. No capacity
override was needed and no unknown path lease was changed. The existing
`notes/theory/lean/.lake/build` lease is held by Luna and has no competing live
writer; it transfers exclusively to Sol for this packet. No review worker has
been launched yet.

Grant `/root/sol_r283_extrusion_row_validity`, registered `lean_prover`,
requested Sol/high, up to 1,800s, no descendants. Exact Sol paths are the new
module, inbox and `.lake/build` listed in the contract. Sol owns both proof
construction and all Lake/checker execution until its STOP. No install, update,
test, Cargo, Rust, compiler or Git work is granted. A different fresh reviewer
up to 900s is reserved only after Sol freezes. Luna owns the unchanged parent
edge and all status/review decisions.
