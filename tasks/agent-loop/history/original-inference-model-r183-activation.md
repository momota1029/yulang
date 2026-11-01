# R183 activation — original inference model and App readback

State: admitted by Luna; launches are recorded only after current-session ACKs.
Baseline: `yulang3` at `89d0dd2bfc3619e6034360e8aa0837bf834499a`.

User objective: prove Yulang type/effect inference sound against the original
source typing rules. Rust implementation correctness is supporting
correspondence evidence, not the theorem target. Parent remains the unchanged
`SourceProblem.InferenceSoundness`, retaining all source forms and quantifiers,
one satisfying assignment `a`, and one shared `sameScoped` witness.

R182 was reviewed and closed incomplete. Its exact first gaps are the missing
complete syntax catalogue behind authenticated source authorities, and the
unidentified concrete inference-model/readback declaration. The R183 selector
recommends recovering the original model and checking whether its equations
are specified before deciding whether a user semantic choice is needed.

Contract: `tasks/agent-loop/sprints/original-inference-model-r183.md`, SHA-256
`b416e0fb91b86df096fa2c106d2c95b0d17e2015556f70fba0f52c0df60d3d0d`.

Luna recomputed all 14 exact dependency rows in the contract before any semantic
reads of the newly located source authorities; all 14 full digests matched.
The two exact output paths were absent at admission:

- `tasks/agent-loop/inbox/original-inference-model-r183-source.md`
- `tasks/agent-loop/inbox/original-inference-model-r183-proof.md`

The source and Lean-model lanes have separate sole write leases, 900 seconds
each, read-only semantic authority, no recursive imports or additional source
owners, and a hard stop at any essential unpinned reference. Fresh independent
exact-conformance review follows frozen outputs, 300 seconds. No theorem
closure, semantic adoption, implementation edit, Lean execution, Rust
inspection, build, test, Cargo or runtime work is authorized. Unknown workers
and quarantined paths remain untouched. Parent remains OPEN.
