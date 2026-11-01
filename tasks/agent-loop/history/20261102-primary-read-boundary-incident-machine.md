# Primary read-boundary incident — quarantined runtime path

Disposition: `STOPPED; NO WRITES`.

During the 2026-11-01 continuation, before refreshing `current.json`, the primary
ran `sha256sum` and `git diff` on
`tools/inference-playground/src/runtime/machine.rs`. The subsequent authoritative
state read showed that exact path leased to `UNKNOWN_WRITER` with state
`QUARANTINED` and recorded SHA-256
`fd7383cc1a96ae5601a3ccf563b19ef4f6381d798d3ce1c72b94929aa7c193f0`.

This was an improper read. No edit, stage, build, test, cache operation, or
follow-up read occurred. The path and its companion quarantined runtime paths
remain untouched and quarantined. No inference from the observed diff is used
in R171. The mistake came from acting on the worktree listing before checking
the live lease state.
