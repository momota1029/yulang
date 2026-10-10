# Symbolic whole-argument selective-owner construction attempt

Date: 2026-10-11. Status: frozen, unreviewed, research-only.
Producer: `/root/source_owner_construction`; execution evidence supplied by the
primary. Claim class: bounded failed source construction and a constructor
discriminant. No all-source impossibility theorem or restoration-R closure.
Baseline: `9577b9dd578f2a995b9b9fd1df0d60b081523681`, branch
`research/simple-sub-intrusion`. Exclusive write lease: this note.

## Objective and exact source

Construct one authentic positive extrusion pair `(C,S)` that qualifies in one
physical SCC while its corresponding positive tail pair `(T',T)` does not.
Governing sources are contextual-attachment-admission design §§3.1–5 and
parent-copy-scc-intrusion, Selected operation and compiler responsibility.
Selected attachment grouping, scope identity, annotation polarity, residual
lineage and actual parent/copy equality remain fixed. The research-lab,
design-authority, git-concurrency rules and yulang-proofs skill were read.
Constructive theorem work and independent review remain separate primary-owned
lanes; this producer neither delegated nor certified this output.

The prior local-annotation probe uses a different Local scope and does not
reuse formal X. The prior whole Function annotation repeats `[E,'t]` in its
argument, producing a known tail-return edge. This attempt instead uses a
distinct symbolic callback-result tail `'u` in that whole argument:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int): ((int -> ['u] int) -> ['x] int) -> [E, 'x] int = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb }; bridge }
```

This is one distinct candidate root. It is a deliberate source variation,
not a source minimization or randomized mutation campaign.

## Constructor discriminant and bounded execution

The constructor argument is conditional on successful parser/lowering and
the normal action schedule. `candidate_local_annotation` selects the actual
Local(bridge) scope. `candidate_formal_effect_variable` keys rows by exact
`(scope,name)`, so whole annotation `'x` can reuse the formal result X, while
`'u` differs from `'t`. Function recursion preserves variance in results and
reverses it in arguments. The nested callback result therefore has composed
positive variance; its symbolic row supplies paired Support/Allowance ports
with its actual U tail. It does not directly reconstruct the prior annotation
view whose tail was T under the repeated `[E,'t]` spelling. These statements
follow the constructors at candidate_effect.rs:987,844–864,1212–1436; they do
not rule out other propagated or restored paths back to T.

The primary executed the exact source through `make_session(text)`,
`root(&session,"left")`, and
`execute_candidate_source_root(&owner).unwrap()`. The helper asserts empty
structural recoveries and runs ordinary HIR lowering, collection, graph start
and source actions. The complete root finished without panic and with zero
solver errors. No solver rows, parent records, bounds or manual constraints
were injected. The temporary observer was after root execution and before
any unrelated host constraints.

The actual positive parent records and pair membership were inspected in the
same completed-root physical snapshot:

| Pair | Actual record / levels | Copy reaches parent | Parent reaches copy | Same SCC |
| --- | --- | --- | --- | --- |
| Owner C/S | copy62, parent25, Positive,target1; levels1/2 | false | true | false |
| Tail T'/T | copy61, parent23, Positive,target1; levels1/2 | false | true | false |

S is the original negative receiver of Allowance0, whose tail is T23; the
paired positive interface alone is not S. C and T' are actual retained
extrusion copies, identified from parent records rather than matching IDs or
levels. C62 reaches its own copied tail61 but cannot reach original S25.

Relevant physical bounds supplied by the primary are:

| Row | Direct lowers | Direct uppers | Exact lowers | Exact uppers |
| --- | --- | --- | --- | --- |
| S25 | 30,55,27 | 62 | Support0, Bottom | Allowance0 |
| C62 | 30,55 | — | Support2, Bottom, Support9, Bottom | Allowance2 |
| T23 | 56 | 61 | — | Allowance0, Allowance3 |
| T'61 | 56 | — | — | Allowance2 |

The table records literal bound lists, including repeated Bottom entries.
It does not invent reverse parent edges. Physical adjacency follows current
representatives, actual direct Effect lower/upper rows and retained
Support/Allowance-to-tail edges. Parent provenance and capture incidence
contribute no graph edge. The primary tested mutual reachability; complete
SCC member lists were not supplied to this producer.

The source removes one known tail-return shortcut, but still supplies no
`C62 → … → S25` continuation. The new original lower27 on S is absent from
C's direct lowers in this final snapshot. This is a concrete failed
construction, not a claim that no future source continuation can reach that
original lower or S. No selective owner equality, unchanged-owner restoration,
omitted ordered fiber or complete replay/diagnostic rescue failure is observed.
R remains open.

## Commands, oracle boundary and resources

Two sequential GDB launches preceded the successful primary probe. Both used
an in-memory transformation of the frozen runner
`/tmp/yulang-bridge-return-annotation-selective-route-20261010/run.py`, replacing
only its source string and binary locator. No scratch file was written.
The trace omitted raw row dumps; the intended terminal observer was still
candidate_effect.rs:1879, immediately after the ordinary root call.

1. Fresh debug0 binary `target/debug/deps/yu_solver-04d5fc765d8541b0` lacked
   function/source symbols. The make_session breakpoint never installed; the
   original host test passed unchanged. Candidate bytes were not injected.
   Returncode1, wall0.323331s, peak67392KiB, user/system0.179199/0.064121s.
2. Fresh debuginfo1 binary `target/debug/deps/yu_solver-6960c7ec27aa0919`
   exposed make_session and source lines but omitted `text`, `action` and
   `session` variables. Input register writes were attempted; candidate input
   identity and root/SCC state could not be verified. The action observer
   stopped on its missing local. Returncode1, wall0.555926s, peak165844KiB,
   user/system0.499667/0.050050s. This is instrumentation failure, not a
   candidate source failure or host-test completion.

Each launch used one CPU affinity, a1.5GiB address-space limit, CPU55s,
timeout45s and outer timeout50s. The stale historical source-HIR binary was
excluded because candidate_context.rs and lib.rs had changed at the pinned
baseline. After these two failures, the method changed to an authorized
primary-owned in-module observer; no third equivalent debugger probe ran.

The primary supplied this exact build/execution command:

```sh
timeout 120s taskset -c 0 bash -c 'ulimit -v 1572864; RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 cargo test -p yu-solver --lib --features shadow-apply-candidate temporary_primary_selective_owner_source_probe -- --nocapture --test-threads=1'
```

The temporary source probe passed, test time0.05s and build time4s. The primary
reported one CPU,1.5GiB cap and no concurrent build; peak memory and total
user/system times for that command were not supplied. The temporary test was
primary-owned and is excluded from this research lease/checkpoint. Its binary
digest was `2d472fc0ce42aa11dd80d795a00d9465b26064714d5229b3871a059503a48a81`.

Execution coverage is one authentic complete source root. No seeds/ranges,
external Oracle, supplied transition model, broad suite, performance samples,
source induction, rollback/retry, publication theorem or restoration theorem
was checked. The SCC observer shares the compiler's inspected physical-edge
contract; it independently reads actual constructed bounds relative to a toy
transition checker, but it is not an independent oracle for those source rules
or their semantic correctness. Primary-supplied execution and producer static
analysis are joint evidence, not independent review. Static reading/report
wall time and memory were unmeasured.

## Dependencies and next construction hinge

The execution uses the queued-relation repair at pinned HEAD. The governing
design hashes are unchanged:

```text
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc contextual-attachment-admission-design.md
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e parent-copy-scc-intrusion.md
79f9f6ea27874d803a27cc1edfee000e4c95390b940936a781253583e947c14b candidate_context.rs
78e2400a5e69a2718fe17f243f82fa232f59fd199fdaf7b5e27212e11b0a4791 lib.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e candidate_effect.rs (baseline; temporary primary test excluded)
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0 candidate_source.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11 candidate_scheme.rs
02135a9533f33c0f877456595741ce05b07ea1d37510f3debea8931c513ebe99 frozen runner
```

No dependency was changed by this producer. The primary's temporary cfg(test)
observer is a distinct, explicitly primary-owned execution artifact and must
be removed before integration. No production transition was changed for this
experiment. Source/HIR/parser and owning constructors were read against HEAD;
the retained historical observer's binary was not substituted as evidence.

Recommended next action: investigate an actual source-produced distinct-tail
Allowance on an older row reachable from C, with a continuation to original S
that survives negative copying. That is the missing constructor premise
localized by the prior audit and this successful bounded source execution.
Another repeated whole-argument annotation cannot resolve it merely by
changing the known tail-return shortcut. No semantic restriction is proposed.

Commit packet: exact leased path
`notes/progress/2026-10-10-source-owner-construction-search.md`; baseline
`9577b9dd578f2a995b9b9fd1df0d60b081523681`; changed dependency hashes none by
producer; frozen, unreviewed, research-only bounded failed construction.
Checks already run: governing/prior-route/constructor reads, narrow baseline
diff and hashes, two failed bounded GDB instrumentations, one primary-supplied
successful ordinary source-root probe and same-snapshot pair reachability.
Proposed checkpoint message: `research: record symbolic argument owner construction gap`.
Shared-record deltas intentionally left for primary/curator: retain this
one-source exclusion, distinguish instrumentation failures from the successful
source run, keep R open and all-source impossibility unproved. No shared
task/index/authority/question-board path or Git state was modified by producer.
