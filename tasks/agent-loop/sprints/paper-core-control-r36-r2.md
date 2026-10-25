# Sprint PAPER-CORE-CONTROL-20261026/r36 — revision 2 fallback repair

Status: READY; fresh worker receipt and Luna's committed RUNNING/cache acknowledgement required before checker work.
Branch: `research/simple-sub-intrusion`
Baseline: `658f69056` (R36/r1 first-check failure frozen; no theorem certified)
Parent contract: `tasks/agent-loop/sprints/paper-core-control-r36.md`, SHA-256 `e3427e6f06bc49e20d9f43a40c2dacbc764337acfe0ee98f0377845c0f0be784`.

## Fixed goal and version boundary

Continue the unchanged bounded R36 ordinary-let-control proof from the parent
contract. Preserve its original theorem, quantifiers, syntax, semantics,
non-goals, dependencies, source domain and resource envelope. This revision
repairs only the failed elaboration in `controlStep_evidence`; it is not a new
attempt to prove or broaden the parent claim.

The r1 failure was the generic fallback `change (PaperCoreStep.step _).map ...`:
Lean could not determine the wildcard head for 19 unsupported constructors after
R35's partial step reduced to `none`. The complete r1 source, diagnostics,
handoff and `.lake/R36Audit.lean` remain immutable at r1's frozen snapshot.

## Sole authorized proof repair

In `controlStep_evidence`, replace the generic successful-delegate fallback with
explicit handling of only R35-supported head constructors: `force`, `unionCase`,
`unroll`, `field`, and `lookup`. For each named head, use the corresponding
`Option.map_eq_some_iff` evidence to establish the `.delegate` successor. If
useful, add a private helper whose inputs are an explicitly named supported head
and its mapped-success equation.

For every other unsupported computation constructor, simplify `controlStep` and
`PaperCoreStep.step` and derive contradiction from `none = some s'`. Preserve
the existing let-push and return-pop priority, state and typed-stack judgments,
shared `D/Xi/Γ`, erasure, `PaperLetContextStep`, preservation and simulation
statements. Do not modify R35 or any frozen input. Stop at the first failed
checker command; preserve full output and do not retry under r2.

The parent contract remains authoritative for all other proof obligations,
coverage, falsifiers, source locators and open gates. The original manuscript
one-step preservation/display simulation, current-port/residual-graph bridge,
omitted frames, source/native, inference A/B and production remain OPEN.
`NO_SAFE_CODE_SLICE`; no compiler changes or tests.

## Frozen inputs

All dependency hashes and toolchain pins are inherited unchanged from the parent
contract: manuscript `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`,
`PaperExecutionSyntax.lean` `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`,
`PaperExecutionTypingSubstitution.lean` `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`,
`PaperTermSubstitution.lean` `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`,
R35 `PaperCoreStep.lean` `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`,
R35 handoff `05cacac3b1536ff53eea589e71536cac2b5d34bbd1b71ef48e195a1aeb0eb128`,
R35 review `5212dd2f014f5868d13aee909dfa794e530fedd872a8dc137081aa8d675364a5`,
and boundary reference `CoreControlBridge.lean` `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a`.
The r1 frozen source baseline is `7ce8fb1c4a3cafe2738723af3dea6e6df11b4d227f1151761941fdb38df7ca95`.

## Exact leases and resources

A fresh registered `lean_prover` receives these exact write leases only after
Luna commits the live receipt/cache acknowledgement:

- `notes/theory/lean/YulangClosure/PaperCoreControl.lean` (continue r1 candidate)
- `notes/theory/lean/.lake/R36AuditR2.lean` (distinct from frozen r1 scratch)
- `notes/theory/lean/.lake/build` (single cache writer)
- `tasks/agent-loop/inbox/paper-core-control-r36-r2-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-core-control-r36-r2.md`

Luna owns `tasks/agent-loop/current.json`,
`tasks/agent-loop/inbox/paper-core-control-r36-r2-primary-verification.txt`,
and the exact lease handoff. A fresh non-author `spec_auditor` receives only
`tasks/agent-loop/inbox/paper-core-control-r36-r2-review.md` after proof, checker
and cache writers stop. No overlapping writers or descendants. Frozen r1 files
remain frozen and are not reopened.

Before checker work, the worker must report actual identity/session, effective
model and effort (UNKNOWN if unavailable), frozen dependency hashes, cache and
process status, and wait for Luna's committed RUNNING/cache acknowledgement. Use
pinned Lean 4.35.0 in `notes/theory/lean`, build only
`+YulangClosure.PaperCoreControl`, then run `.lake/R36AuditR2.lean` with
`lake env lean -j1 -M1024`. Audit every theorem declaration's full type and
axioms using the Yulang skill's generator/validator. No full build, tests, Rust,
network, dependency/config edits or unrelated checker commands.

Carry forward the original R36 envelope without reset: total 1800 active seconds,
14 native invocations and 180 checker seconds. r1 charged 3/10 worker calls,
0.524371738 checker seconds and conservatively at least 250 active seconds.
Remaining total is at most 1550 active seconds, 11 native calls and
179.475628262 checker seconds; worker allowance at most 7 native calls and
119.475628262 checker seconds, primary allowance at most 4 calls and 60 checker
seconds. If remaining aggregate time or capacity cannot be established, stop.
The sequential independent source-only reviewer receives at most 180 active
seconds and no checker/cache/Git/write access. Eight UNKNOWN reservations remain
quarantined. No production or implementation authority is granted.
