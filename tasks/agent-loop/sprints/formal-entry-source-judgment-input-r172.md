# Sprint R172 — connect FormalEntry inputs to the original Lambda judgment

Status: **ADMITTED** under the unchanged user goal of Yulang type-inference
soundness, including inferred effect rows, against the original source typing
rules. Rust runtime/machine correctness is outside scope.

Branch / baseline: `yulang3` / `008c5fd5b`.

## Parent and fixed outcome

The parent stays `YulangClosure.SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:127–130` with its original
quantifiers and one shared witness. R171 is kernel-accepted conditional
mathematics, but independent review found its intended successful-trace source
application uninhabited: new formal entries start with `entry = none`, while a
successful R169 trace requires `entry = some port`. The current model also
omits interleaved record-field recipe appends. No theorem currently derives an
actual source typing judgment, concrete `generates`/`solves`, or the parent
shared witness.

Freeze the independent original Lambda typing inputs for the formal, source
annotation, type interface, computation-entry/effect-flow, body check, and
retained-entry permission. Map those inputs to the actual constraint-generation
and preparation states, preserving the formal's owner/Lambda/parameter/recipe
origin across record-field recipe appends and `entry_effect` preparation.
Identify the first premise that cannot be derived from the pinned construction
and exact owner of that premise. An exact missing-input result is a successful
outcome; do not state an invented inference theorem or shrink the source set.

The only candidate semantic route to assess is the independent source rule in
Source Generalize §§2–3 and
`OriginalSourceGeneration.generated_constraints_imply_source_judgment`. Its
`Kernel`/`Satisfies` premises must remain distinct from the repository parent
`generates`/`solves` until an actual bridge is shown. The theorem name alone is
not evidence that the bridge exists.

## Frozen inputs

- R171 contract SHA-256:
  `8289f460cb3a3057118bda0337722699714c1debe3b349db51691cae2d7e541e`
- R171 proof module SHA-256:
  `03e727c104e2773ec3bbe1589c5dfb61ddb2df40d40a54de6be45583d01506f6`
- R171 proof handoff SHA-256:
  `a1818e9797e8bdef8fac49157dc061fbf94b56b2bbd2981e436e7236a038caca`
- R171 Rust/HIR source handoff SHA-256:
  `8db9a9730932aedd162ad4c918000c6c73176323eae797be022a197db2174f22`
- `OriginalSourceSyntax.lean` SHA-256:
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean` SHA-256:
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalFormalShared.lean` SHA-256:
  `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7`
- `OriginalSourceClosure.lean` SHA-256:
  `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a`
- `OriginalSourceChecking.lean` SHA-256:
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `OriginalSourceEvents.lean` SHA-256:
  `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`
- `Contracts.lean` SHA-256:
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- Source Generalize authoritative design SHA-256:
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- Source Generalize construction SHA-256:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- Annotation effect hygiene policy SHA-256:
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `candidate_source.rs` SHA-256:
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `candidate_effect.rs` SHA-256:
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`

## Lanes and exact outputs

- Proof/source-semantics lane, registered `lean_prover`, read-only on all
  frozen inputs above; may write only
  `notes/theory/2026-11-02-formal-entry-source-judgment-input.md` and
  `tasks/agent-loop/inbox/formal-entry-source-judgment-input-proof.md`.
  Determine the exact independent Lambda premises and identify whether an
  existing original-source theorem can consume them. Do not run Lean: no new
  Lean theorem has been admitted and all R171 checker allowance is spent.
- Rust inference/source lane, registered `researcher`, read-only on the two
  frozen solver files and R171 source handoff; may write only
  `tasks/agent-loop/inbox/formal-entry-source-judgment-input-source.md`.
  Trace collection, record-field recipe append/duplicate handling, formal
  registration, `entry_effect` preparation, action generation, and effect-row
  consumer within the single inference construction. Runtime/machine sources
  are excluded. Report `NO_SAFE_CODE_SLICE` absent a concrete reachable bug.
- Luna owns integration and assigns a fresh independent reviewer after both
  lanes stop. Review the semantic mapping and exact source correspondence;
  no compiler or production authority is granted.

## Resource and stop boundaries

Proof lane: at most 900 seconds. Source lane: at most 600 seconds. Independent
review: at most 300 seconds. Astra: 0. No Lean invocation, build, Cargo, tests,
generated file, cache growth, environment, target, scratch, or runtime path
inspection. No write or lease may be added beyond the listed three outputs.

Stop on a changed dependency, missing authority for an original typing rule,
need to alter language semantics, reachable source bug, or any requirement to
claim the candidate `Kernel` is the concrete parent inference relation. Preserve
both blockers from R171 unless an exact construction establishes their repair.
Keep `InferenceSoundness`, its source domain, quantifiers, and shared witness
unchanged. A conditional theorem or source map does not close the parent.
