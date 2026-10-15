# Playground hygiene: bounded adversarial observations

Date: 2026-10-15
Status: frozen, independently reviewed research characterization; no theorem or implementation gate closed
Review: fresh M2 `compiler_referee`, no findings in the bounded semantic claims;
no Oracle execution or complete source hygiene was certified.
Baseline: `e9790f96f154ef0ddf67cb45aa26a569148569d7`
Branch: `research/simple-sub-intrusion`
Method: source mutations through the existing debug playground; independent of the constructive proof lane

## Objective, authority, and exact premise

Attempt to falsify preservation of effects and absence of unauthorized capture
using annotated computation/callback, outside-arm, and binding/block discriminants.
The controlling selected behavior is annotation integration §§1 and 1.1:
contravariant `[signal]` grants local subtraction permission, accepts compatible
additional `write` effects, and leaves those additional effects outward.
Directional protection §2.1 fixes the omitted-callback/block expectation.
Top-level inference principles §§1, 3, and 4 govern inference and safety.
Compose release's “Scope of the operation” preserves the contribution and other
scopes. Its already successful compose fixtures were read and not rerun here.

These are native source-admission/constraint-solve observations. The playground
does not execute a VM, print principal schemes, or implement Catch subtraction.
A successful solve does not establish that a Catch returned `1`, consumed a
request, preserved the correct residual, or avoided unauthorized capture.
Existing direct/omitted/outside-arm observations were reused from
`2026-10-15-hygiene-example-baseline.md`; old raw-template reachability and
extra identity-fiber investigations were not repeated.

## Results

Each row is one sequential child execution, ordinary mode, no intrusion/scoped
flags. Exit 1 is classified by its actual diagnostic, not as a runtime result.

| ID | Source discriminator | Exit | Observed result |
| --- | --- | ---: | --- |
| 01 | Annotated callback, user source | 1 | Unsupported candidate source |
| 02 | Annotated computation, user source | 0 | Solved; answer value graph contains IntPositive |
| 03 | 01 with pure answer requirement | 1 | Unsupported candidate source |
| 04 | Computation with write/signal expression statements | 1 | Lowering unavailable: StructuralProjection |
| 05 | 02 with pure answer requirement | 1 | One IncompatibleEffect |
| 06 | 05, arm emits signal independently | 1 | Two IncompatibleEffect reports |
| 07 | Additional write via operation application | 1 | IncompatibleEffect at inner signal invocation |
| 08 | 07 with `[write]` answer requirement | 1 | Same inner-invocation conflict |
| 09 | 02 inside block; only final bound Name required pure | 0 | Solved |
| 10 | 09 with whole block required pure | 1 | One IncompatibleEffect |
| 11 | Grouped mixed-effect expression-statement block | 1 | StructuralProjection |
| 12 | 11 with unannotated identity relay | 1 | StructuralProjection |
| 13 | Mixed-effect function body with expression statement | 1 | StructuralProjection |
| 14 | 13 with unannotated identity relay | 1 | StructuralProjection |
| 15 | Mixed-effect block using local binding for write | 0 | Solved under `[signal]` computation annotation |
| 16 | 15 with unannotated identity relay | 0 | Solved |

No soundness counterexample was found. Case 05 exposes the already documented
subtraction completeness gap. It is not an unauthorized-capture counterexample.
Case 06 retains both an incoming and an outside-arm same-family contribution
as distinct incompatible operands under a pure requirement; no removal is
established. Cases 09/10 distinguish the pure bound-value lookup from effects
of initializing the enclosing block, without establishing correct handling.

Case 15 is a useful admitted extra-effect input: the computation annotation
does not reject this `[signal, write]` source. It does not show that only
`write` remains after Catch. Case 07 cannot diagnose an annotation input cap:
the conflict occurs while computing an operation argument, before such an
interpretation is justified. Cases 11–14 share a lowering obstruction also
present in unannotated controls; the local-binding mutation in 15/16 solves.
No assertion about the semantic validity of expression statements follows.
Callback permission remains unobservable because 01/03 are unsupported.

## Complete sources and exact execution recipe

The following deterministic construction specifies every byte of all 16
executed sources, including failed probes. The original run used this command
array for each generated path, with `capture_output=True`, `text=True`, and
`timeout=10` in Python `subprocess.run`:

```text
target/debug/yu-playground /tmp/yulang-hygiene-falsifier-20261015/ID-NAME.yu
```

No expected type, effect set, or model-produced oracle answer was fed into the
solver beyond the displayed source annotations. The recipe reconstructs inputs
only; it does not launch another process wave.

```python
from pathlib import Path
root = Path('/tmp/yulang-hygiene-falsifier-20261015')
P = 'act signal:\n    our ping: () -> int\n\n'
W0 = 'act write:\n    our emit: () -> int\n\n'
W1 = 'act write:\n    our emit: int -> int\n\n'
R = ('my relay(thunk: [signal] int) = catch thunk {\n'
     '    signal::ping(), _ -> 1,\n    v -> v\n}\n')
C = ('my relay(cb: () -> [signal] int) = catch cb() {\n'
     '    signal::ping(), _ -> 1,\n    v -> v\n}\n')
I = 'my relay thunk = thunk\n'
G = 'my both x = { write::emit(); signal::ping() }\n'
B = ('my program = {\n    my answer = relay signal::ping();\n'
     '    answer as [] int\n}\n')
A = '({ my ignored = write::emit(); signal::ping() })'
cases = {
 '01-annotated-callback': P+C+'my answer = relay signal::ping\n',
 '02-annotated-computation': P+R+'my answer = relay signal::ping()\n',
 '03-annotated-callback-pure': P+C+'my answer: [] int = relay signal::ping\n',
 '04-annotated-computation-write':
     P+W0+R+'my answer = relay { write::emit(); signal::ping() }\n',
 '05-annotated-computation-pure':
     P+R+'my answer: [] int = relay signal::ping()\n',
 '06-annotated-computation-outside-arm':
     P+R.replace('_ -> 1,', '_ -> signal::ping(),')
     +'my answer: [] int = relay signal::ping()\n',
 '07-annotated-computation-write-apply':
     P+W1+R+'my answer = relay (write::emit(signal::ping()))\n',
 '08-annotated-computation-write-residual':
     P+W1+R+'my answer: [write] int = relay (write::emit(signal::ping()))\n',
 '09-annotated-computation-binding': P+R+B,
 '10-annotated-computation-block-pure':
     P+R+B.replace('my program =', 'my program: [] int ='),
 '11-computation-mixed-block':
     P+W0+R+'my answer = relay ({ write::emit(); signal::ping() })\n',
 '12-unannotated-mixed-block':
     P+W0+I+'my answer = relay ({ write::emit(); signal::ping() })\n',
 '13-computation-mixed-body': P+W0+R+G+'my answer = relay (both 1)\n',
 '14-unannotated-mixed-body': P+W0+I+G+'my answer = relay (both 1)\n',
 '15-computation-mixed-let': P+W0+R+'my answer = relay '+A+'\n',
 '16-unannotated-mixed-let': P+W0+I+'my answer = relay '+A+'\n',
}
for name, source in cases.items():
    assert len(source.encode()) <= 2048
    (root / (name + '.yu')).write_text(source)
```

For a compact admitted source illustrating the extra-effect observation (15):

```yu
act signal:
    our ping: () -> int

act write:
    our emit: () -> int

my relay(thunk: [signal] int) = catch thunk {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay ({ my ignored = write::emit(); signal::ping() })
```

This source is minimized only to the shown discriminants, not proven globally
minimal. It solves; the pure-output variant of this exact source was not run.

## Oracle independence, coverage, resources, and stop

No Oracle execution or Oracle-route search ran in this lane. Semantic targets
come from the named user-approved records. All observations share the existing
native parser, lowering, solver, and renderer; they are not independent
implementations or proof of their source rules. Pure annotations are observational
constraints, with their own implementation trusted only as reported behavior.

Coverage: 16 explicitly listed deterministic sources, no random seeds or
enumeration range. Mutations changed callback/computation position, pure root,
independent arm emission, additional effect, local binding, or block observation.
The repeated unsupported callback variants were not extended further. No alias,
returned-function, recursive, polymorphic-effect, nested-polarity, fresh-use,
handler-runtime, or complete scoped-compose claim was checked.

Budget consumed: 16/16 sequential playground processes; each timeout 10 seconds;
maximum source 233 bytes; summed rounded process wall times 0.140 seconds;
largest stdout 1430 bytes. All processes returned without timeout or signal.
Peak RSS/CPU time were not measured. Initial host observation: 20 logical CPUs,
about 25 GiB available RAM. Zero Cargo commands, tests, builds, benchmark samples,
parallel probe processes, or Git mutations. Stop: assigned process budget.
Scratch `.yu`, `.out`, `.err`, and `results.json` files remain under the unique
directory above; they are not commit artifacts.

Recommended next action: use case 15 as an admitted integration discriminator
when source-owned Catch subtraction exists, checking a `write` residual and
rejection of a pure result; first supply the callback annotation owner/consumer
bridge rather than issuing more unsupported callback probes.

## Frozen dependency snapshot and commit packet

Exact leased path: `notes/progress/2026-10-15-playground-hygiene-adversarial-observations.md`.
No other repository path changed by this worker. Baseline is the SHA above;
dependency files remained unchanged during this lane. SHA-256:

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679  notes/design/2026-10-15-compose-scoped-effect-release.md
f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
41ea13e42d184e630954ac74954a24b92428acb924c26efc565dceec932168de  tools/inference-playground/src/main.rs
a5564766c4b257f1bf51089a603e9bb23930c95f17047b0ab892fd3edd39c3db  tools/inference-playground/src/lib.rs
ff9bbd6f0fb48200dcf691602547ab4020d0013e2b007b2493a2cc9a06293bed  target/debug/yu-playground (untracked build artifact, not for commit)
```

Claim/review status: bounded observation, independently reviewed by a fresh
`compiler_referee` with no findings; no original proof gate closes.
Checks already run: 16 bounded source executions, exact recipe/input equality,
dependency hashes, note fences/line budget/whitespace. No required shared record
is changed by this worker. Primary/curator retains any task/theory/index delta;
no gate closure follows. Proposed one-line research-checkpoint commit message:
`research: record bounded source hygiene adversarial observations`.
