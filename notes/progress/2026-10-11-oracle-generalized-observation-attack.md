# Oracle generalized nested-effect observation: three bounded source runs

Date: 2026-10-11
Status: frozen, unreviewed research characterization; original H remains OPEN
Claim class: executed source qualification and bounded exported observation, not a hygiene theorem or counterexample
Yulang3 baseline supplied by primary: `35e88c8113c9c6516e260170503bea753e4ede6`
Oracle revision verified by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: `notes/progress/2026-10-11-oracle-generalized-observation-attack.md`
Method: leaf-only serial Oracle execution; no delegation or Git operations

## Objective, authority and exact premises

Characterize whether the frozen nested Function discriminator survives export
as a latent observation, and whether deleting its inner concrete row or delayed
second application changes that observation. This complements constructive
proof work; no transition-assuming checker is used.

The original statement is H in
[Oracle global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. It quantifies over every successfully lowered source program and
composed-negative concrete annotation occurrence, original scope/binders,
actual copy/use and actual call/output route. It requires subtraction confined
to the exact attachment instance, independent same-family retention, connected
symbolic tails, current/future lower checking and correlated lineage through
copying/generalization. Incorrect lowers require authentic rejection and safe
nonpublication. This experiment does not narrow any quantifier. Its target is
the exact generalization/compaction/pruning/finalization/root-POP bridge in §5,
using the discriminator frozen in
[nested scheme falsification](2026-10-11-oracle-effect-nested-scheme-falsification.md)
§§1,3.

Selected meaning comes from
[annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, with the withdrawn callback output in §6 unused, and
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Oracle's `spec/2026-05-31-effect-variable-subtractable.md`, sections
“Annotation lowering”, “Filter” and “Compact / finalize”, distinguish negative
concrete allowance, check activation and principal projection. A specification
statement that a filter was checked is not evidence that every relevant source
path actually discharged it. No new annotation meaning is adopted.

Execution hypotheses: the exact stdin bytes below, the executable hash below,
normal dump completion and the primary's pinned executable/source identity.
The leaf verified the executable bytes before and after the runs, but did not
independently reconstruct the build or checkout revision. Static interpretation
of printed stack syntax is conditional on that supplied source/binary
correspondence. The experiment itself needs no assumed solver transition rules.

## Exact commands and complete observations

All commands ran from `/home/momota1029/rust/yulang` in Bash, strictly serially.
`printf` and `ulimit` are shell builtins. Each Oracle run used `timeout 20s` and
`ulimit -v 2097152` (2 GiB virtual address space). There were no temporary source
or log files. The stderr process substitution tags each line if present;
`ORACLE_STATUS` is a wrapper report copied from `PIPESTATUS[1]`, not Oracle
stdout. Every run had empty stderr and Oracle status 0. Shell wrapper status was
also 0. No help invocation, build, test, alternate executable probe or fourth
Oracle run occurred.

### A. Frozen nested Function and second call

```sh
ulimit -v 2097152
printf '%s\n' 'pub act tick:' '    pub ping: () -> ()' 'my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()' | timeout 20s /tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly 2> >(while IFS= read -r line; do printf 'STDERR: %s\n' "$line"; done)
oracle_status=${PIPESTATUS[1]}
printf 'ORACLE_STATUS: %s\n' "$oracle_status"
```

Complete Oracle stdout:

```text
roots d0:tick d2:f
pub d0:tick mod {
}
my d2:f: (() -> ['a] () -> ['a & [tick; 'b]] ()) -> ['b#0[tick], 'a] () = e5:(fn p0:d3:cb -> e4:(e2:(e0:r0:cb->d3:cb e1:()) e3:()))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d3:cb arg
}
```

This establishes acceptance of the exact candidate text by this dump route;
the syntax/resolution uncertainty of the earlier static packet is removed for
this source. The expression dump retains both applications. It does not expose
the complete intermediate annotation tree, solved graph or lower-check table.

### B. Delete only the inner concrete row

```sh
ulimit -v 2097152
printf '%s\n' 'pub act tick:' '    pub ping: () -> ()' 'my f(cb:(() -> (() -> ()))) = (cb ()) ()' | timeout 20s /tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly 2> >(while IFS= read -r line; do printf 'STDERR: %s\n' "$line"; done)
oracle_status=${PIPESTATUS[1]}
printf 'ORACLE_STATUS: %s\n' "$oracle_status"
```

Complete Oracle stdout:

```text
roots d0:tick d2:f
pub d0:tick mod {
}
my d2:f: (() -> ['a] () -> ['a] ()) -> ['a] () = e5:(fn p0:d3:cb -> e4:(e2:(e0:r0:cb->d3:cb e1:()) e3:()))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d3:cb arg
}
```

### C. Delete only the second call

```sh
ulimit -v 2097152
printf '%s\n' 'pub act tick:' '    pub ping: () -> ()' 'my f(cb:(() -> (() -> [tick] ()))) = cb ()' | timeout 20s /tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly 2> >(while IFS= read -r line; do printf 'STDERR: %s\n' "$line"; done)
oracle_status=${PIPESTATUS[1]}
printf 'ORACLE_STATUS: %s\n' "$oracle_status"
```

Complete Oracle stdout:

```text
roots d0:tick d2:f
pub d0:tick mod {
}
my d2:f: (() -> ['a] () -> [tick; 'b] ()) -> ['a] () -> ['b#0[tick]] () = e3:(fn p0:d3:cb -> e2:(e0:r0:cb->d3:cb e1:()))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d3:cb arg
}
```

## Discriminating result and its limits

**Bounded characterization.** A and C retain a visible weighted residual
`'b#0[tick]`. In C it is the returned Function's result effect; in A it occurs
in f's result effect alongside `'a`. B removes that weighted residual and the
nested concrete row while retaining the two application nodes. Keeping the
declaration in B controls for the mere presence of the resolved family name.
These are two deletion mutations, not an enumeration or a claim of globally
shortest source.

The formatter owners support the literal structural reading:
`crates/poly/src/dump/type_format/formatter.rs:480–505` obtains Function
result-effect text from its actual result-effect port;
`crates/poly/src/dump/type_format.rs:591–598` places it after that Function's
arrow. `formatter.rs:1337–1365` emits a `#id[...]` suffix for one nonempty
stack entry, excludes filters/floors and the quantified-root POP sentinel,
and prints nonzero pops beside a nonempty stack. Under supplied source/binary
correspondence, the observed `#0[tick]` therefore represents a retained stack
entry with a tick payload and no printed nonzero POP count. `#0` is a rendered
occurrence name; it is not an independently observed raw source SubtractId.
The formatter deliberately hides pure `u32::MAX` quantifier POPs
(`type_format.rs:600–606`); these dumps do not establish their absence.

**Candidate interpretation, not established semantics.** The observations are
consistent with carrying an inner latent residual through publication and
exposing it on the second application's output route. They rule out the
stronger operational hypothesis that this exact annotation has no surviving
exported weighted observation at either location. They do not decide whether
the original check is already discharged, reconstructed from a Row contract,
or correctly activated for every later provider lower. A retained PUSH and a
discharged static check may coexist; these alternatives are not exclusive.

**No genuine counterexample to H.** No callback provider is supplied, no effect
operation is invoked, and no independently attached same-family contribution
is present. `tick.ping` is declaration-only and remains `<missing>`. There is
no actual future external use of generalized f, rejected lower, symbolic source
tail, handler or fresh-use comparison. Inferred `'a`/`'b` are visible; their
full correlated constraint meanings are not reconstructed. A green dump proves
neither successor correctness nor Oracle universal hygiene, soundness or
principality.

**First missing semantic premise.** Connect the original nested occurrence's
source-generated receiver/stack identity and checks to this exported weighted
residual and its actual instantiated delayed-call consumer. Establish from the
generalizer/collector/finalizer and restored constraints that every erased
check is discharged or sufficiently represented for later concrete lowers,
and that the retained entry authorizes only its exact attachment while an
independent tick contribution survives. Printed `#0` alone supplies neither
that identity bridge nor the check/consumer bridge. This is still §5's owning
source premise; another output-only toy probe would leave it untouched.

## Independence, coverage, failure conditions and resources

The oracle is the actual pinned prebuilt Oracle executable, independent of a
new worker-authored transition model. It is also the implementation whose
preservation claim is under examination, so it cannot independently certify its
own correctness. Authority fixes the intended property separately; the three
runs share the same executable, declaration and normal dump path. The two
mutations change one named discriminator each. No random seed, numeric search
range or brute-force cases were used: coverage is exactly A, B and C once each.

A parse/type error, timeout, signal or unsupported dump would have prevented
claiming publication qualification; none occurred. The first-run syntax stop
condition therefore did not apply. No rejection-path inference is available.

Budget consumed: 3/3 Oracle invocations, no overlapping Oracle processes, each
bounded by 20 seconds and 2 GiB address space. All three tool calls completed in
their immediate 0.1-second response window, well inside the 120-second
experiment envelope. The tool's tiny reported `wall_time_seconds` fields do
not measure child execution reliably; no precise process wall/CPU or maximum
RSS was collected. Aggregate resource measurements and total reasoning wall
time are unknown. No timeout, truncation of executable output, additional
measurement sample, build, Cargo/test process or temporary file occurred.
Some initial combined static captures were truncated; only named H/§5,
discriminator, authority and formatter sections ground the conclusions here.
This is not an exhaustive source audit.

Recommended next action: assign the source identity/check bridge at the actual
generalization and instantiation owners for C's retained inner residual, using
A as its second-call consumer control. Any instrumentation needs a separate
explicit lease; keep H and production gates OPEN.

## Frozen dependency hashes

SHA-256. Oracle paths start at `/tmp/yulang2-oracle-read/`; repository paths are
relative to the Yulang3 worktree. No dependency was edited by this leaf. The
binary and both frozen input notes were rehashed after the runs and remained
unchanged. Baseline equality and integration remain primary-owned.

| Dependency | SHA-256 |
| --- | --- |
| Oracle `target/debug/yulang` | `0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-effect-nested-scheme-falsification.md` | `fd6cb9ea14adb8bbe873d118dae3e52bf498696d9caf37be2155c346e6b86ecb` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| Oracle `spec/2026-05-31-effect-variable-subtractable.md` | `fbd9588b489dbc6b987c5e7a11d1d3f1bdc696be3bed605e5dcac849f42cda7a` |
| Oracle `crates/poly/src/dump/type_format/formatter.rs` | `10ef65e06243dff901d83e37bde22b99065c05dc92a31872fb8179397c3c2265` |
| Oracle `crates/poly/src/dump/type_format.rs` | `49800841ea8059b007076b8018076baa91ae275c76f3f07eb24a57341fe35bd7` |

## Commit packet

- Exact leased/change path: `notes/progress/2026-10-11-oracle-generalized-observation-attack.md`; writes stop at handoff.
- Baseline SHA: `35e88c8113c9c6516e260170503bea753e4ede6`; Oracle revision `a58eefc31e22141574b6f20c6a5748151c6d79f1` supplied/verified by primary.
- Changed dependency hashes: none authored; rechecked binary and frozen input notes unchanged. Snapshot hashes above; no Git operation by this leaf.
- Review status: frozen, unreviewed, research-only characterization. No self-certification, independent review, H closure or implementation authority claimed.
- Checks already run: three exact serial bounded Oracle dumps (all exit 0, stderr empty), targeted authority/formatter reads and dependency hashes; leased-note trailing-whitespace/fence inspection. No builds/tests.
- Proposed one-line checkpoint commit: `research: characterize nested Oracle effect publication with deletion controls`.
- Shared-record deltas left for primary/curator: qualify the exact nested source as accepted by the pinned dump; record retained exported weighted residual and second-call location discrimination; retain the source identity/check/generalization bridge and original H as OPEN. No shared task/index/authority/question-board records changed.
