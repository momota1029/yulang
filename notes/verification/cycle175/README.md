# Cycle175 verification scope

Final sources: nine new modules in `lean/Yulang/*175.lean`; 72 public named
`theorem`s, excluding definitions/private/generated constants. The final module
origin axiom gate also covers those other constants: 183 declarations, only
propext, Classical.choice and Quot.sound. Exact signatures are in declarations.md.

## What ran

Lean4.35.0, sequential `lean -j1 --trust=0` source compilation and small audit
files. A previously verified local dependency cache was reused; focused source
comparison rebuilt changed modules, never a whole `lake build`. The initial
three-module union had879 dependencies, the flexible six-module union882.
New helper sources were compiled separately with the same compiler and audited
as exact-source prefixes or against their matching compiled source. Tests use
kernel `decide`, not native_decide. Benchmarks are executable smoke/performance
observations, separate from theorem proofs.

Original base0d2, latest basef196 after the midcycle integration fetch. The only
changed imported earlier module was Edge174's doc comment; its latest source
was recompiled and all-gate rerun successfully. All2750 existing Lean files in
f196, excluding the root import list, match their base blobs. New centered/Astra
modules outside this closure are preserved, not claimed checked in this cycle.

No clean full-repository build, full verify-lean.sh, or CI success is claimed.
Standing orders prohibit those full runs. There is no guarantee that untouched
modules outside the focused closure build together.

## Logs and failures

- `core-gate-final.log`: seven core modules,131 declarations.
- `all-gate-final.log`: nine modules,183 declarations before the latest rebase.
- `latest-edge-build.log`, `latest-all-gate.log`: final dependency refresh and183
  declaration gate on the latest source base.
- `flexible/`: failed initial namespace reference, corrected compilation,
  final named audits, nominal-view regression failures and successful correction.
- `performance/`: original/table and table/compact benchmark inputs/results,
  table boundary test first syntax failure and corrected success. Numeric
  results are limited to the named synthetic fixtures, not Checked programs.
- `reach/`: read-only type/value/opaque-proof dependency traces. The final seven groups all load
  seven core modules/131 declarations; pre-compact/ retains the earlier five
  six-module/100-declaration snapshots.
- `checkpoint*-verification.json`: fetch-back blob comparison records.
  `checkpoint2-prior-log-gap.json` records41 ignored earlier logs omitted from
  an intermediate tree. The checkpoint3 record verifies all41 were restored
  to their original published hashes; no old proof source was lost.

Commands were run with the prepared `LEAN_PATH` pointing to that verified
cache and with180-second per compiler command bounds. A new checkout must first
build its own dependencies; these logs are evidence of this run, not a promise
that copying only the changed files creates a standalone Lean project.
