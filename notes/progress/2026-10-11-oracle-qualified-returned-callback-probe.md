# Oracle returned callback: one clean bounded dump qualification

Date: 2026-10-11
Status: frozen unreviewed research observation; original H remains OPEN
Claim class: single-source executable characterization, not a theorem or counterexample
Y3 baseline: `161886f1b63b93a3f1d08130170c509bae2feb7d`
Oracle source revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle binary SHA-256: `0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58`
Exclusive lease: this note only; leaf, no delegation or Git mutation

## Objective, authority and exact envelope

Qualify the exact candidate supplied by the primary after the
[static operation-path audit](2026-10-11-oracle-operation-path-source-audit.md).
The [prior failed call](2026-10-11-oracle-postpublication-call-probe.md) used
one of two authorized calls. This packet uses exactly the remaining **one**
serial invocation, with no controls, syntax changes or alternative programs.

Governing sources: [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and withdrawn callback result §6;
[original universal H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1 and remaining generalized-observation premise §5;
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The accepted concrete polarity policy is unchanged. No withdrawn
callback result is used as an expected scheme. Successful publication safety
and the original H domain are not weakened.

The execution hypothesis is the primary-pinned prebuilt Oracle binary with
the named source revision. Its hash is independently checked as bytes before
and after execution; this does not establish reproducible build provenance
or correctness of the binary's compiler implementation.

Exact input, including one final newline:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
my provider() = \() -> tick::ping()
my observed() = f provider
```

Input SHA-256: `2e07291d89dfc9057ce42c8331b7aefb21bd862657b05d9b24076bd92fe4e9fc`.

## Reproducible command and complete captured result

Executed from `/home/momota1029/rust/yulang`. The Python wrapper holds input
and capture in memory, creates no temporary/log files, and applies a hard
2 GiB virtual-address-space limit inherited by timeout and Oracle. It launches
Oracle once with `timeout 20s` and the exact requested flags:

```sh
python3 - <<'PY'
import hashlib
import resource
import subprocess
import time
from pathlib import Path
binary = Path('/tmp/yulang2-oracle-read/target/debug/yulang')
expected = '0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58'
before = hashlib.sha256(binary.read_bytes()).hexdigest()
assert before == expected, before
source = b'pub act tick:\n    pub ping: () -> ()\nmy f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()\nmy provider() = \\() -> tick::ping()\nmy observed() = f provider\n'
def limit_memory():
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
started = time.monotonic()
result = subprocess.run(['timeout', '20s', str(binary), '--no-prelude', '--no-cache', 'dump', '/dev/stdin', '--poly'], input=source, capture_output=True, preexec_fn=limit_memory)
elapsed = time.monotonic() - started
after = hashlib.sha256(binary.read_bytes()).hexdigest()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
print('BINARY_SHA256_BEFORE:', before)
print('SOURCE_SHA256:', hashlib.sha256(source).hexdigest())
print('STDOUT_BEGIN')
print(result.stdout.decode('utf-8'), end='')
print('STDOUT_END')
print('STDERR_BEGIN')
print(result.stderr.decode('utf-8'), end='')
print('STDERR_END')
print('TIMEOUT_WRAPPER_STATUS:', result.returncode)
print('BINARY_SHA256_AFTER:', after)
print('ELAPSED_SECONDS:', format(elapsed, '.6f'))
print('CHILDREN_USER_SECONDS:', format(usage.ru_utime, '.6f'))
print('CHILDREN_SYSTEM_SECONDS:', format(usage.ru_stime, '.6f'))
print('CHILDREN_MAX_RSS_KIB:', usage.ru_maxrss)
assert after == expected, after
PY
```

Complete captured stdout, stderr and status/resource metadata follow.
`STDOUT_*`, `STDERR_*` and the metadata labels belong to the wrapper.

```text
BINARY_SHA256_BEFORE: 0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58
SOURCE_SHA256: 2e07291d89dfc9057ce42c8331b7aefb21bd862657b05d9b24076bd92fe4e9fc
STDOUT_BEGIN
roots d0:tick d2:f d3:provider d4:observed
pub d0:tick mod {
}
my d2:f: (() -> ['a] () -> ['a & [tick; 'b]] ()) -> ['b#0[tick], 'a] () = e5:(fn p0:d5:cb -> e4:(e2:(e0:r0:cb->d5:cb e1:()) e3:()))
my d3:provider: () -> () -> [tick] () = e10:(fn p1:() -> e9:(fn p2:() -> e8:(e6:r1:"tick::ping"->d1:"tick.ping" e7:())))
my d4:observed: () -> [tick] () = e14:(fn p3:() -> e13:(e11:r2:f->d2:f e12:r3:provider->d3:provider))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d5:cb arg
}
STDOUT_END
STDERR_BEGIN
STDERR_END
TIMEOUT_WRAPPER_STATUS: 0
BINARY_SHA256_AFTER: 0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58
ELAPSED_SECONDS: 0.031637
CHILDREN_USER_SECONDS: 0.030878
CHILDREN_SYSTEM_SECONDS: 0.000000
CHILDREN_MAX_RSS_KIB: 37440
```

Python wrapper status: **0**. Timeout wrapper status: **0**; no timeout or
signal failure was reported. Stderr was exactly empty, and stdout contains no
diagnostic. Unlike the prior failed qualification, the provider has a concrete
scheme and nested lambda body. The declaration-only operation is still shown
with `<missing>`; that marker is on `tick.ping`, not on the provider. The static
audit's declaration owner explains this bodyless operation form. This is
qualification for the observed dump mode, not execution of `observed()`.

## What the dump establishes and the remaining bridge

| Item | Direct bounded observation |
| --- | --- |
| Provider formation | `d3:provider` has `() -> () -> [tick] ()` and two nested lambda bodies. |
| Operation reference | The inner provider body contains `r1:"tick::ping"->d1:"tick.ping"` and its unit application. |
| Named later use | `observed` contains a reference to `d2:f`, a reference to `d3:provider`, and their application. |
| f display | The nested formal scheme and weighted residual `'b#0[tick]` remain printed. |
| Observed output | `d4:observed` displays `() -> [tick] ()`; concrete tick is retained in this printed output. |
| Qualification | One clean dump, nonmissing provider, empty stderr, normal wrapper status, unchanged pinned binary hash. |

No direct evidence identifies printed `#0` with a raw annotation SubtractId,
shows its actual quantified/freshened map at the use of `f`, or captures SCC
event order establishing postpublication instantiation. Textual ordering and
resolved references do not supply those facts. The dump does not expose
annotation-check replay, contribution independence or the complete attachment
incidence for the provider/call/output route. Its retained `[tick]` is neither
proof of H nor a counterexample to H; an independent same-family contribution
was not constructed in this input. No scheme universally follows from this
single run.

The exact next semantic bridge is to connect the actual generalized use of
`d2:f` at `r2` to its selected annotation/quantified SubtractId and fresh use
map, then trace the actual `d3:provider` nested operation contribution through
both callback applications to `observed`'s output. Compaction, pruning,
principal finalization and root POP must be accounted for together with
retained lower checks, as required by original H §5. That bridge remains OPEN.

## Independence, coverage, resources and frozen handoff

Oracle provides executable behavior independent of a hand-written toy model,
but the static audit and this run share its source/binary assumptions. The
Oracle is not an independent proof of its own universal hygiene. There is no
differential reference, second control, mutation, seed range or exhaustive
enumeration. Coverage is exactly the five-line input once, without prelude or
cache, in poly dump mode. No runtime handler or dynamic operation execution,
independent contribution, rejected lower, alternate annotation or second use
was covered. No source/compiler changes, Cargo, builds or tests were made/run.

Budget: **1/1** call here, **2/2** across this packet and the prior failed
packet; no remaining invocation allowance. Process execution was serial with
20-second timeout and 2 GiB virtual-memory limit. Wall time was 0.031637 s;
child CPU was 0.030878 s user plus 0 system; child maximum RSS was 37,440 KiB.
The CPU/RSS readings are `RUSAGE_CHILDREN` wrapper/descendant measurements,
not a separately instrumented Oracle-only profile or performance study.

Before handoff, Oracle revision remained pinned and its working tree was
clean. Y3 HEAD advanced concurrently from the assigned baseline to
`8017f0425efdcdf08dca8dcb37dae6bedea9419b` at final recheck; all five listed
dependency hashes were unchanged. Note integrity, embedded command syntax,
exact input hash and the command's single subprocess invocation were checked
without executing the embedded command again. Writes stop at handoff; no
independent review is claimed.

Recommended next action: assign a bounded source-to-artifact proof/audit of
the exact generalized-use/fresh-ID/call-output bridge above, using this frozen
input and dump. Do not repeat another equivalent dump without new authority
and a discriminating instrumentation plan. Original H remains OPEN.

## Dependency snapshot and commit packet

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-postpublication-call-probe.md` | `09ea064b0598b59414be2debc2aea9c31a2bcc831f95e4fc36a22b0a1658da96` |
| `notes/progress/2026-10-11-oracle-operation-path-source-audit.md` | `a39b7ff03f7358e31ce811c5e1d933bdfcb06b6de8c477590aecb87a37178819` |

- Exact leased/change path: `notes/progress/2026-10-11-oracle-qualified-returned-callback-probe.md`.
- Baseline: Y3 `161886f1b63b93a3f1d08130170c509bae2feb7d`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`; binary pin unchanged before/after. No dependency hashes changed by this worker.
- Claim/review status: frozen unreviewed single-source dump characterization; H and generalized-use/fresh-ID/call-output bridge OPEN.
- Checks already run: binary before/after SHA-256 assertions, Oracle revision/clean-tree and dependency checks, exactly one bounded dump with complete capture, leased-note whitespace/newline/fence inspection. No build/test/control run.
- Proposed research-checkpoint commit: `research: qualify Oracle returned callback and retained tick output`.
- Shared-record deltas left for primary/curator: record clean provider formation and observed retained tick; mark the original two-call budget exhausted; preserve H OPEN at the explicit generalized-use/fresh-ID/call-output/check bridge. No task/index/authority/theory-status file edited.
