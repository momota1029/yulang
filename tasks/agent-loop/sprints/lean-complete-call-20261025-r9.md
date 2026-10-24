# LEAN-COMPLETE-CALL-20261025/r9 — checked Call execution adequacy

Status: **FROZEN** by Luna. Fresh total cap: 6,600 seconds; no earlier grant
carries over. Branch `research/simple-sub-intrusion`; baseline commit
`8656445efaadb63bb7919e0ef0155e7630a9748f`, pushed before this contract.
Contract SHA-256 is recorded in `tasks/agent-loop/current.json`. This is a
formalization sprint under accepted Yulang semantics; it authorizes no compiler
or production change.

## Original goal and bounded outcome

The unchanged parent is complete Lean proofs of Yulang semantics and type
inference under `notes/theory/lean`, with reviewed milestones committed and
pushed by Luna. Original inference A/B, the r8 Call A/B claims, full
source/native correspondence, principality, termination, and production gates
remain OPEN. R9 establishes checked execution adequacy needed before those Call
proofs can proceed; it does not replace or weaken their claims.

R8 remains CHECK_FAILED/UNACCEPTED. Its implementation cap is charged, and its
first pinned `CoreSyntax.lean` invocation failed after 3.578s. Exact artifact
hashes and the diagnostic receipt are archived in
`tasks/agent-loop/sprints/lean-complete-call-20261025-r8-outcome.md`, SHA-256
`83961c24d5c87e49248475180287272ae21066671bbcf3164e0cdd68037f4a12`. No
dependent module was checked; no proof or review ran. R8 P/Q/B and review
allocations were unissued and are not transferred to r9.

### Governing source and fixed execution order

Use `docs/yulang-operational-type-safety-ja.tex`, especially its raw
computation/value/force rules at lines 303–333, Call entry and adapter rules at
362–400, actual error/Bad behavior at 490–493, and the complete Call View at
1245–1246; retain the other governing sections pinned by r8 (145–245,
535–602, 1029–1044). Also use `rules/design-authority.md`. Candidate V1–V7
claims are not premises.

Preserve the original Call order: allocate one fresh receiver and enter its
Scope; peel wrappers outermost-to-innermost using that owner; retain each
argument adapter inside its delayed `Delay(let z <- Force t in a(z))`; attach
the source lambda receipt before first force; Value entry forces the received
carrier while Computation entry substitutes it without forcing; execute body
and declared-result consumer; run pending result adapters inner-to-outer under
the complete Call View; on normal return leave Scope and retain returned Views
and latent code. Preserve actual Req/Fail paths wherever admitted syntax can
reach them, event-time observations, operation instance, value payload,
response-typed continuation, metadata/world operations, and the arbitrary
literal Control suffix. Failure keeps its reason and only the source's
existing cleanup relation.

## R8 source-coverage obstruction carried into r9

The r8 formal grammar admits `TypedCall.ValueTyped.original` at a thunk type,
including `.original (.delay (.ret .unit))`; computation typing also admits
forcing that value. However, the frozen `CallControlStep` relation covers
`.force (.delay body)` in TypedCall syntax and has no step for
`.force (.original (.delay body))`. A typed View wrapper may also surround a
thunk without a corresponding force transition. These are source/formal
coverage gaps, not checked runtime counterexamples or semantic refutations.
R9 must include each source-required step, or report the exact missing
source-provided metadata/input as an obstruction. Do not invent a force rule,
View port, observation policy, or cleanup policy.

The Call-specific relation need not embed into the existing `Control.Step`.
It does need its own independently justified start/successor coverage and a
substantive `Bad` argument. A state type with no `bad` constructor or a typing
index that excludes `Bad` by definition is not execution adequacy.

## Exact propositions

### S — `call_step_erasure` (`CallSimulation.lean`)

Define an explicit erasure/observation of each represented Call configuration
to the independently defined raw Call machine. Prove forward simulation for
every actual `CallControlStep`: an actual Call step corresponds to the
source-prescribed raw execution step(s), preserving the actual substitution,
mode, world transition, metadata required to resume, and literal independently
typed suffix. Include start, embedded Original execution, typed and
View-wrapped thunk force, Req/Fail, ordinary Ret, adapters and Scope. If a
metadata-only source transition stutters in the raw projection, name and prove
the exact stuttering simulation relation. Do not define erasure by assuming
the desired transition or erase information needed by the next raw step.

The raw relation is not assumed from S and S does not prove successor
completeness. The declaration and all helper signatures are frozen in this
module and handoff.

### C — `call_raw_successor_coverage` (`CallCoverage.lean`)

For every represented typed Call configuration and every successor in the
independently defined raw Call relation, use canonical forms and inversion of
the actual typing derivations to construct a corresponding actual Call
successor or the exact typed Ret/Req/Fail handoff, retaining metadata, world,
result type and arbitrary literal suffix. Classify **every** raw successor,
including malformed-operation `Bad` constructors. Show a raw Bad successor
cannot arise from the substantive typed image premises; do not make the raw
relation depend on Call typing or define it from the already-typed Call
successor relation.

Together S and C establish source-to-formal execution adequacy for this bounded
Call representation. An omitted source rule, unattached View/port input,
uncertain world operation, or inability to prove one raw-successor case is an
exact OPEN obstruction; it cannot be covered by narrowing admitted syntax or
assuming same-body safety.

## Frozen dependency component

Luna revalidates the complete direct/transitive component at dispatch, after
implementation freeze, before proof dispatch, and before review. The r8
candidate hashes below are the pinned r9 inputs. Changed non-leased files
return to Luna; workers never enlarge leases.

| Input | SHA-256 |
|---|---|
| `AGENTS.md` | `69e24ca7bc987f0fa646145751e966f740f6774ef357082078a20030c50c89ae` |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/design/2026-10-16-goal-driven-sprints.md` | `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e` |
| `.agents/skills/yulang-sprint/SKILL.md` | `b6f4a50703928020607edebe1c8b138fb98a0378220f00b7c190dba9fc068515` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md` | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` (r8 candidate) | `c6330ad1cf8a17b0a35f9928af82478830113f4afeb423042f74e84b0ece1916` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` (r8 candidate) | `1cff4497661aec68c384871f0eac0e32c34166d9ea489667791d21ce67d988d1` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` (r8 candidate) | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| R6 accepted outcome | `b6def9a2c248ccbd7a8bda1cba9489b6dab84abd8a9131f0b24ce573e0eefd4a` |
| R7 failed outcome | `892aff9b3005cf6620802555924767968ea4db63914687493f197d3e1c0afa37` |
| R8 failed outcome | `83961c24d5c87e49248475180287272ae21066671bbcf3164e0cdd68037f4a12` |

Pinned Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). One Lean
process at a time, `-j1 -M1024`, maximum 120 seconds per invocation.

## Exact assignments and resources

All r9 stages are fresh; r7/r8 grants remain charged and cannot be carried.
The first issued stage is only the implementation assignment. Proof lanes S/C
start in parallel only after implementation stops, Luna verifies the full
representation dependency component, and the raw relation and typed/raw
interfaces are frozen.

### Implementation — Luna/high, maximum 1,800s

Exact write leases:

- `notes/theory/lean/YulangClosure/CoreSyntax.lean`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean`
- `notes/theory/lean/YulangClosure/CoreExecution.lean`
- `notes/theory/lean/YulangClosure/ControlSyntax.lean`
- `notes/theory/lean/YulangClosure/ControlTyping.lean`
- `notes/theory/lean/YulangClosure/ControlComposition.lean`
- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
- `notes/theory/lean/YulangClosure/CallExecution.lean`
- handoff only: `tasks/agent-loop/inbox/20261025-lean-call-execution-implementation-r9.md`

Repair current syntax/name/elaboration failures and add the source-required
embedded-Original and View-wrapped thunk force cases. Define a raw Call
execution relation with genuine malformed-operation `Bad` behavior that is
independent of Call typing and the typed Call transition relation. Provide
explicit start/successor constructors, actual substitution, Req/Fail, world and
suffix data, and formal erasure/typed-image interfaces for S/C. Preserve all
accepted source order and r6 public statements. Stop on missing source
metadata, any unresolved semantic choice, or a changed non-leased dependency.
Do not run Lean, tests, Cargo, native commands or Git; Luna owns checks. Freeze
one coherent interface/handoff and stop before verification.

### S — Sol/high, maximum 1,200s

Exact paths: `notes/theory/lean/YulangClosure/CallSimulation.lean` and handoff
only `tasks/agent-loop/inbox/20261025-lean-call-simulation-r9.md`.

Prove `call_step_erasure`: every actual Call successor forward-simulates under
the independent raw Call relation, retaining actual substitution and all
source-relevant world/metadata/suffix distinctions. Freeze exact declarations
and dependency hashes. No raw transition may be assumed from S.

### C — Sol/high, maximum 1,800s

Exact paths: `notes/theory/lean/YulangClosure/CallCoverage.lean` and handoff
only `tasks/agent-loop/inbox/20261025-lean-call-coverage-r9.md`.

Prove `call_raw_successor_coverage` by canonical forms and inversion for every
raw successor from a typed represented state. Cover malformed-operation Bad
rules substantively, all embedded/View-wrapped thunk forms, Req/Fail and exact
typed handoffs. Do not derive raw semantics from the typed Call relation or
weaken the source domain. Freeze exact declarations and dependencies.

### Staged total and stop policy

Fresh r9 total: 6,600s — implementation 1,800; S 1,200; C 1,800; Luna checks
and integration 900; fresh independent review 900. Astra 0. Only
implementation starts first; S/C may run together after the exact seam above.
Maximum two new authors concurrently. Do not issue or spend r8 P/Q/B grants
inside r9. Three old UNKNOWN reservations remain quarantined and consume
capacity; no lease is reclaimed. An unissued stage is not RUNNING or charged.

## Checks, review, source boundary, and Git

Luna checks the repaired modules in dependency order, then `CallExecution.lean`,
`CallSimulation.lean`, `CallCoverage.lean`, all changed direct/transitive
dependencies, and `YulangClosure.lean`. One invocation at a time, pinned
toolchain and limits above, at most 900 seconds of the primary grant. Stop on
the first failed check and retain its exact diagnostics. No tests, Cargo or
native builds. `python3 tools/agent_sprint.py check` is workflow validation
only.

After all authors stop and the reviewed target/dependencies are immutable, a
fresh isolated `compiler_referee` checks source correspondence, independence of
raw semantics from typing, all actual successors, embedded and View-wrapped
thunk cases, genuine malformed-force `Bad`, typed-image successor lifting,
forward simulation, Req/Fail, substitution, world, metadata, arbitrary literal
suffix, old r6 statements, proof holes/axioms/escapes. Authors cannot review
their own outputs. Acceptance requires all blocking/major findings closed on
checked bytes.

Only Luna edits `YulangClosure.lean`, this contract, `current.json`, outcome and
review records; only Luna stages explicit accepted paths, commits and performs
ordinary push. An unaccepted result may be preserved only as a labeled research
checkpoint. No force-push, blanket staging, hidden premises, semantic weakening
or production promotion. Full decorated-plan authenticity, effect hygiene,
frontend and native correspondence, original A/B, principality, termination,
and parent closure stay OPEN.

Next dispatcher consultation: material source obstruction/counterexample,
dependency/authority/lease/resource change, the S/C integration seam, combined
review, r9 outcome, or parent-goal replanning. Routine lemmas and checks remain
inside this frozen contract.
