# Sprint R182 — authenticate the App syntax and inference owners

Status: admitted bounded continuation of the unchanged Yulang type/effect
inference-soundness goal. Baseline: `yulang3` at
`e673a698b2bbfd8e9a9890fc03a87b6b069c3d3e`.

## Parent claim and evidence target

The parent is still `SourceProblem.InferenceSoundness`: for every source form,
generated constraint set, and satisfying assignment `a`, derive the original
source typing judgment under that same `a` and one shared `sameScoped` witness.
Do not narrow its quantifiers, forms, effects, telescope, admissions, or witness.
Rust correctness is not the target theorem.

R181 established that the App inference-result/readback proposal is not yet
adopted: the complete syntax catalogue and the concrete source inference model
were not authenticated. This sprint must identify actual declarations and
equations that connect:

> App syntax/endpoints → concrete generation and solution interpretation →
> source-owned image/readback → unchanged `Logical` and
> `LocalAdmissions.logical` admission.

The two source owners are independent inputs. A syntax catalogue alone does not
construct the source image or admission. A generic `SourceProblem`, a variable,
an example, or a conditional theorem is not a concrete inference instance.

## Fixed lanes and outputs

1. Syntax owner, read-only: enumerate actual endpoint constructors, App source
   operands and binder identity, plus every syntactically admissible descriptor
   or interface write location. Distinguish representability from formation,
   typing, and admission. Output only to
   `tasks/agent-loop/inbox/app-syntax-owner-r182-source.md`.
2. Inference-model owner, read-only: inspect only the named declarations and
   symbol occurrences in the pinned files. Identify a concrete `SourceProblem`
   instance only if a declaration fixes its fields. Map any real construction
   and readback equations to the original App payload/admission; otherwise name
   the first missing owner and required equation. Output only to
   `tasks/agent-loop/inbox/app-inference-instance-r182-proof.md`.

Combined success is a hash-authenticated owner map and an exact first missing
edge, or an actual constructible theorem target retaining the original claim.
Do not select a semantic alternative, adopt R181's proposal, define `solves` as
constraint satisfaction, strengthen `generates`, assume admission as output,
or use a fresh/per-field witness. A reference to another file is a stop point:
return its exact path/declaration for a sequential primary pin. No recursive
imports, broad search, Lean command, Rust inspection/edit, build, test, Cargo,
runtime, or new environment/cache.

## Frozen direct inputs

Recompute every digest before content reads. A mismatch stops the dependent
lane for sequential primary review.

- `tasks/agent-loop/sprints/app-inference-owner-intake-r181.md` —
  `763dfdfbdd53063a490d171a75ebe0f3aea886e5373c9853d633b45797649b36`
- `tasks/agent-loop/history/app-inference-owner-intake-r181-activation.md` —
  `387a872031838f7ae8190a031d26572aa89419fe947f0a28f6cb3292b2c4f92e`
- `tasks/agent-loop/history/app-inference-owner-intake-r181-outcome.md` —
  `5ea0d03e862749b3e7b921326cc6c717e3eed54b842e0da340c818f7b8a1c905`
- `tasks/agent-loop/inbox/app-inference-owner-intake-r181.md` —
  `623b09934b0c153b989130438820c98e40f195767d62ab81aad415d33fe5bbb8`
- `tasks/agent-loop/inbox/original-app-admission-r179-proof.md` —
  `7180e445a11fa926b52081677d3f917a6f30a5bca40278e533230b6cf95528d7`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalProofProgress.lean` —
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`

## Bounds, review, and stop conditions

Each lane has at most 450 seconds. A fresh independent exact-conformance review
gets 300 seconds after both outputs freeze. No proof closure or compiler change
is authorized by this sprint. Implementation remains `NO_SAFE_CODE_SLICE` until
an approved source-owned inference/readback construction gives an actionable
behavioral obligation. Preserve all unknown worker rows and quarantined paths.
Parent theorem remains OPEN unless a genuine full-scope proof or
source-qualified counterexample is independently reviewed.
