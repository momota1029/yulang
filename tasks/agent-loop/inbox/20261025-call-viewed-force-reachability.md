# P viewed Force reachability — frozen handoff

- Sprint: `LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r2`.
- Assignment/handoff: `CALL-VIEWED-FORCE-REACHABILITY-P`, revision 1.
- Contract r2 SHA-256: `01aa44596c1f2aeae77afb0c90f5026fc263e522b7771c2ced274deb957f9e9c`.
- Governing r1 SHA-256: `6020b57d97d0642be5702dafe52efa5fc302165ded16d5e717a159b7e92bee5c`.
- Baseline supplied by Luna: HEAD `9cdcab55e`; no Git operation performed by P.
- Author/worker: `/root/view_force_reachability_prover`, constructive leaf P.
  Activation: primary ACTIVATE message for r2. Session identifier: UNKNOWN.
- Requested model/effort: Sol/high. Observed model/effort: UNKNOWN/UNKNOWN;
  no runtime model receipt was exposed. No descendants or coauthors.
- Outcome: **candidate, unchecked**. First-failure stop reached before Lean ran.
  No independently reviewed theorem or source/native result is claimed.

## Parent claim and application

Parent remains original Call progress/A-B and source/native obligations, OPEN.
The frozen P proposition is, for arbitrary `W`, `md`, `sig`, `world`,
`occurrence`, `suffix`, `result`, and independent
`hsuffix : FramesTyped sig suffix (.original (.base .unit)) result`:

```lean
∃ (term : TypedCall.CallTerm) (target : CallState W),
  Prefix (CallControlStep md) 5 (CallState.initial term world suffix) target ∧
  target.head = .active
    (.force (.view (.delay (.ret (.original .unit))) occurrence))
```

The candidate supplies a Value-entry identity lambda and identity declared-result
consumer, empty receipt/interface/wrap plan, a viewed delayed unit return,
receiver owner 0, and an empty active-owner list. It explicitly supplies the
FunctionTyped proof, carrier thunk typing, receipt equality, wrap-plan equality,
and receiver freshness. Carrier occurrence metadata is `[occurrence]`.

Five constructors compose using `Prefix.snoc`: `start`, `attachReceipt`,
`enterLambda`, `enterBind` for the consumer, and `enterBind` for the body.
The target retains the two identity bind frames followed by the receiver scope,
the unchanged world, occurrence metadata and literal independently typed suffix.
No metadata law or suffix inspection is used.

Public `viewedForceCallTerm` and `viewedForceTarget` expose the chosen witnesses.
`viewed_force_prefix` supplies their specific five-step candidate derivation;
`viewed_force_reachable` derives the exact existential proposition. The specific
lemma makes the Call result definitionally unit for Luna's intended finite-typing
composition, avoiding an unavailable equality from the existential alone.

After successful checking and fresh review, Luna can apply accepted
`initial_call_prefix_terminal_typing` to this specific witness and the original
independent suffix premise, then compose Q's no-successor theorem. P currently
provides no checked result for that composition. No parent closure follows.

## Exact formal evidence and reused work

The constructor signatures actually read were
`TypedCall.FunctionTyped.lambdaValue`, `TypedCall.ValueTyped.view/delay/original`,
`Original.ValTyped.unit`, every `TypedCall.CallTerm` field,
`TypedCall.callEntryBody`, `consumeCallResult`, `valueEntryBody`, and
`CallControlStep.start/attachReceipt/enterLambda/enterBind`.
The existing finite-typing result is reused only as Luna's prospective typing
preservation step; it supplies neither progress nor source reachability.
No historical failed proof or narrowed-domain theorem was reused.

Formal syntax and actual relation constructors are the accepted domain here.
No Rust/frontend producer was audited and no native correspondence is claimed.
Actual producer realization remains unestablished; formal entry-body owner is
`CoreExecution.lean: TypedCall.callEntryBody`, and transition consumer owner is
`ControlSyntax.lean: CallControlStep`. Q owns inversion/no-successor evidence.
No Simple-sub inference transition, semantics or production source was changed.

## Dependency pins

All following SHA-256 values were rechecked and matched the frozen contract:

| Input under `notes/theory/lean/YulangClosure/` | SHA-256 |
| --- | --- |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CallPrefixTyping.lean` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `CallTerminalTyping.lean` | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| `CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |

The r1 and r2 contract hashes above also matched exactly. No dependency changed.

## Check failure and resources

Intended sole check, working directory `notes/theory/lean`:

```text
lake env lean -j1 -M1024 YulangClosure/CallViewedForceReachability.lean
```

Exact attempted shell command/wrapper:

```sh
python - <<'PY'
import json
import subprocess
import time
command = ['lake', 'env', 'lean', '-j1', '-M1024', 'YulangClosure/CallViewedForceReachability.lean']
started = time.monotonic()
try:
    completed = subprocess.run(command, capture_output=True, text=True, timeout=120)
    print(json.dumps({'command': command, 'exit': completed.returncode, 'stdout': completed.stdout, 'stderr': completed.stderr, 'elapsed_seconds': time.monotonic() - started, 'timeout': False}))
except subprocess.TimeoutExpired as error:
    print(json.dumps({'command': command, 'exit': None, 'stdout': str(error.stdout), 'stderr': str(error.stderr), 'elapsed_seconds': time.monotonic() - started, 'timeout': True}))
PY
```

The shell returned exit 127, with:

```text
/usr/bin/bash: line 1: python: command not found
```

`python` did not start; consequently `lake env lean` never launched. Actual Lean
invocations: 0. Lean exit, stdout, stderr and elapsed: NOT_RUN. The failed tool's
reported `wall_time_seconds` was `0.000015095` (outer tool display 0.2 seconds).
No Lean session ID or persistent process was returned. No retry or source repair
was attempted under r2. No tests or unrelated builds ran.

Grant: 900 seconds active work and one serialized check capped at 120 seconds,
1 CPU, 1 GiB. Actual total active duration and remaining budget are UNKNOWN;
there was no activation timestamp/elapsed receipt. This does not renew resources.

## Frozen outputs, TODO and stop receipt

- New source: `notes/theory/lean/YulangClosure/CallViewedForceReachability.lean`
  (121 lines), SHA-256
  `ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c`.
- New handoff: `tasks/agent-loop/inbox/20261025-call-viewed-force-reachability.md`.
  Its hash is delivered separately to avoid a self-referential byte hash.
- Neither leased generated output exists: `.lake/build/lib/lean/YulangClosure/CallViewedForceReachability.olean`
  and `.ilean` under `notes/theory/lean`. They were not emitted.
- No scratch path or other file was created or changed. No descendants,
  unresolved descendant leases, background processes or active Lean processes.
- `P-VERIFY-1`: Luna owns a revised authorization if checking is resumed. Input is
  this frozen source and matched dependencies; proposed output is one actual
  serialized direct Lean check, with no unavailable Python wrapper. Falsifier:
  first Lean error, timeout or pin mismatch. No further P step is authorized r2.
- `P-COMPOSE-1`: after checking and Q, Luna owns specific-witness finite-typing
  composition and fresh independent review. Parent/source-native gates stay OPEN.

**STOPPED; all P writes stopped after freezing this handoff.** Author P is
ineligible to independently certify its candidate or the combined result.
Primary may intake as an unchecked research candidate pending revised check,
fresh review and integration; this is not a checked proof milestone.
