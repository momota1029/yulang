# R110 closeout: finite §21 entry demand at the CLI boundary

Status: **CLOSED_CLEAN_FINITE_CLI_OBSERVATION**. The one authorized command ran
once and passed. No retry was used.

## Command receipt

Exact command:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_entry_demand entry_demand_controls_cli_completion -- --exact --nocapture
```

Exit code: `0`. Cargo compiled the target in `0.31s`; the one integration test
passed in `0.08s` (`1 passed, 0 failed`). Existing dead-code/unused warnings
were emitted from `yu-hir`, `yu-solver`, and `yu-playground`; they did not
prevent compilation or execution.

The test ran two serial public CLI subprocesses, each receiving one exact source
on stdin with `--run main --steps 10000 -`:

- Value formal source, 97 bytes, no final LF: child exited unsuccessfully,
  stdout was empty, and stderr contained the existing 10,000-step exhaustion
  diagnostic.
- Computation formal source, 106 bytes, no final LF: child exited successfully,
  stdout was exactly `9\n`, and stderr was empty.

The exact sources and hashes remain in the contract and proof/implementation
receipts. The test checks its own byte lengths/no-final-LF conditions and its
asserted CLI outcomes. It does not claim internal event or source identities
that were not asserted by this test.

## Finite proof-backed interpretation

R97 had already observed these same source bodies through the public
parse/lower/candidate/runtime integration helper: the Value cell reached
`ResourceExhausted`, and the Computation cell completed with Integer 9. R103
provided a finite same-source projection for the original annotated formal and
its positive `RootCompSchema`. R110 newly crossed the separate CLI stdin,
preparation, exit-status, stdout and stderr boundary for the exact two sources.

The proof traces the original formal annotation to its RuntimeProgram role and
the actual invocation branches: ValueEntry executes the delayed recursive
argument; Computation entry binds the entire Delay without executing it, so the
unused body returns 9. Finite exhaustion is an observation at 10,000 steps,
not a mathematical divergence result. A green test establishes only these
finite inputs and the pinned public CLI path.

Fresh pre-edit spec, post-output spec and compiler/source reviews were all
CLEAN. The R110 contract and test-only scope remained unchanged. The R109
nested-handler SourceSite range mismatch was explicitly excluded and remains
untouched. R101/R102 commands remain `NOT_RUN`; `R101-ENTRY-1` remains `OPEN`.
The six effect-hygiene parents, method/role behavior, original Simple-sub and
evaluator quantifiers, R85 adoption and production authority remain open. No
production code or language rule changed.

Frozen artifacts:

- Contract: `tasks/agent-loop/sprints/cli-entry-demand-20261019-r110-rev1.md`, SHA-256 `d651d326981e1b27bb329b3655ccd612809a1c871f67511baf365cd7d0082976`
- Proof: `notes/theory/2026-10-19-r110-cli-entry-demand.md`, SHA-256 `edb279cab8e76f6fbff38eaac85d5cc8478fd5785cc6cd04b4fe071dc528f11f`
- Proof handoff: `tasks/agent-loop/inbox/20261019-r110-proof.md`, SHA-256 `11e950999109f314ae9617dc73422be3576581d0f79b56842e7045eff3b500b1`
- Test: `tools/inference-playground/tests/cli_entry_demand.rs`, SHA-256 `283e3518f8d28efedd171cacfe97fc7246225339b1c160d06b3c58944f86c8bc`
- Implementation handoff: `tasks/agent-loop/inbox/20261019-r110-implementation.md`, SHA-256 `3965fb85fb4a97936c241a919d284d03ab18c00eeed986516802bc57d371fc34`
- Pre-spec: `tasks/agent-loop/inbox/20261019-r110-pre-spec-review.md`, SHA-256 `fa767add9732b937bd4155c0c13c9e408d1f9f5e3f06042dba560c1fe9fbcaee`
- Post-spec: `tasks/agent-loop/inbox/20261019-r110-post-spec-review.md`, SHA-256 `beb028b89f37746b49106f78d52a41bebf5d9944991ef05733706db7287e5152`
- Compiler/source review: `tasks/agent-loop/inbox/20261019-r110-compiler-review.md`, SHA-256 `9bab38cda9288cbbf115dfea048a433f0b58fabdc84c0e1c94528303481ebd0c`

Next sprint selection should rotate toward an independently open effect-hygiene
front or method/role source behavior. Do not let this finite entry result close
or dominate those tracks.
