# Original actual future-invocation observation packet r4

Owner: `/root/checking_semantics_route_r4`.
Primary: `/root`; integration, fresh review, Git, and publication remain primary-owned.

## Scope, clock, and frozen inputs

Authorized start: 2026-10-26 14:34:45 UTC.
Hard deadline: 2026-10-26 15:04:45 UTC.
Budget: 1800 seconds, at most 16 focused checks, each at most 120 seconds;
one CPU/thread, Lean `-j1 -M1024`, aggregate process-group RSS at most 1280 MiB.
Six focused invocations used. No descendants, Git, Rust, dependency/config
mutation, shared-status edits, or existing-core edits.

Exact repository write scope:

- `notes/theory/lean/YulangClosure/OriginalFunctionFuture.lean`
- `notes/theory/2026-10-26-original-function-future.md`
- `tasks/agent-loop/inbox/20261026-original-function-future-r4.md`

Exact scratch/cache scope:
`/workspace/scratch/f98087c7ac1a/function-future-r4/`.
The initial input-manifest.json pinned all 14 source/config inputs before check
1. Every invocation retained an actual full source/config snapshot and hashes,
including all failed attempts. Native caches were private to this packet.
The original code baseline supplied by primary was
`4c5fff3b2addbbea61a110865cb9273d10c9f97d` plus frozen admission
`77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7`.
The primary subsequently confirmed that exact admission module independently
accepted and published at `99f18bdc54df8057f5a6d5d4bec5dc449336c234`;
none of this packet's pinned input bytes changed.

Governing AGENTS, sprint rules, Lean proof skill, and actual source authority
were read. authority-manifest.json and authority/ retain their exact hashes and
contents. Main semantic authority is SG §§3.2(4), 3.3/L3/L5; selected contextual
Function membership; call-input realization §§2, 3.2, 4.1. No adjacent candidate
was silently substituted for that selected source scope.

## Constructed roots and exact source application

All names below are under `YulangClosure.OriginalFunctionFuture`.

- `invocation_event_fields`: all ten actual Event coordinate equations, with
  current history/configuration from raw invocation and six dynamic maps using
  the entire original fixedFrames prefix.
- `invocation_child_preserves_prefix`, `decode_actual_invocation`, and
  `invocation_child_active`: exact original Environment.extend readback,
  preservation of prior Shared/runtime frames and entry paths, retained
  CallOwner/descriptors, and active complete input independent of descriptor.
- `admitted_checked_observation`: actual enclosing-goal admission plus actual
  finite registered observation Checking yields complete observation transport
  at the raw invocation's computed event and recovers the same callable/root
  and complete target domain.
- `function_observation_child_at_actual_event`: direct application of the
  finite Checking.function observation-child premise to its actual candidate.

The main result is parametric in Inputs, GuardRegistry/Declarations,
RuntimeReadout, LocalAdmissions, and PortReadout. It uses the previously
accepted registered proof kernel and its full finite recursor. It does not
assume whole KernelSound, all future GoalMeaning, whole FunctionShape, phase
equality, or target-domain invariance. No token or eventReadback premise is
needed for the actual raw candidate. The true original declaration
interpretations and unconstructed raw source registration remain explicit
parent obligations; this packet is not a new full original Kernel instance.

The EventDiscriminator namespace gives nonempty, distinct event-sensitive
domains. `current_goal_meaning` proves the entire current domain GoalMeaning
for arbitrary ports; `later_raw_is_goal_admitted` supplies an actual future
candidate. `later_domain_inclusion_fails` and
`future_input_excluded_by_current_guard` identify the missing future domain
premise. History/current/eta/witness change while fiber/eta0 stay fixed.
`same_static_scope_does_not_force_event_readback` separately demonstrates the
missing dynamic EventField ownership using a mismatched witness. This is a
finite formal-interface discriminator, not a source-program counterexample.

The complete 20-root inventory is in required-roots.json. Complete types and
per-origin dependencies are in 06-census.log, full-types-and-axioms.txt, and
origins.json; axioms.json contains every named originating constant.

## Exact first residual and next owner

The existing domain stateClause adds `input.event = state.assignment.event`.
It therefore cannot supply D_checked subset D_source at a later incoming
GoalAdmitted event. The existing value reading quantifies arbitrary Event
probes, even unrelated fiber/eta0, while RuntimeReadout preserves both.
Same static scope does not construct the other current event fields either.

Next construct the original SG §3.3 Event/EventField telescope for every
independent Initial/Response/raw Resume/FutureUse, including eta, actual current
witness, authority, dictionary, scope, incidence, current configuration, and
original Shared/EventProof dependencies. Derive RuntimeReadout coordinate
readback and target-own view registration from those constructor-owned fields,
then prove coverage of the full original event domain. Do not store generic
all-event readback or future safety as a new registration field.

Only after that construction, coordinate the domain and value readings with
that source-owned lawful event telescope. Dropping the current-event equality
alone or guarding only by fiber/eta0 is insufficient. This proposal does not
authorize core changes and was not implemented. Current results remain valid;
hereditary Function registration, future guard/capture suppliers, full source
registration, and general recursive L4 remain open. No closure compatibility
or boundary-transitivity shortcut is used.

## Native execution and complete origin audit

Resolved native toolchain:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
versions.log records Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake 5.0.0-src+eb6cafb.

Focused command wrapper:

```text
python3 /workspace/scratch/f98087c7ac1a/function-future-r4/run.py module OriginalFunctionFuture
python3 /workspace/scratch/f98087c7ac1a/function-future-r4/run.py census FunctionFutureAudit.lean
```

It runs the pinned native `lake --no-cache build +YulangClosure.OriginalFunctionFuture`
or `lake --no-cache env lean -j1 -M1024 FunctionFutureAudit.lean` in the isolated
project. The project retained its original config/hash. One CPU affinity,
LEAN_NUM_THREADS=1, deadline, process-group RSS, exact commands, snapshots,
exit status, and log hashes are recorded in checks.json.

| Check | Result | Evidence |
| --- | --- | --- |
| 1 | Failure, 0.108 s | Restricted native Lake installation lookup failed before compilation. |
| 2 | Failure, 35.210 s | Built the entire imported cone; finite model needed explicit History numeral types, id reduction, and binder-equality proof. |
| 3 | Failure, 1.017 s | Remaining numeral branch and definitional id reduction exposed. |
| 4 | Pass, 1.018 s | Constructive module and finite discriminator compile. |
| 5 | Pass, 1.126 s | Final exact bytes, including full GoalMeaning/guard discriminator. |
| 6 | Pass, 1.125 s | Complete origin/type/axiom census and all required roots. |

Every failure and its exact source snapshot is retained. No timeout or resource
limit was exceeded. Peak aggregate RSS was 1,156,329,472 bytes in check 6.
The final census contains 39 originating declarations, including 24 theorem
constants; all 20 authored theorem roots exist as theorem constants. Every
origin, including generated constants, received full `#check @...`,
`#print axioms`, and collectAxioms inspection. No project axiom or disallowed
axiom occurred. Actual union is propext and Quot.sound: 15 originating
constants depend on propext and 5 on Quot.sound; 0 on Classical.choice.
The exact universe-annotated printed names remain in the report.

06-census.log: 75,684 bytes, SHA-256
`dcf6fca0929e9d09ee2672014c1473e5681394b201623b78b2ddb51d6671b417`.
The delivered file contains no sorry, admit, project axiom, native_decide,
unsafe declaration, or kernel bypass.

## Author freeze and review boundary

Code frozen 2026-10-26 14:48:27.772447 UTC after check 5:
`e90f98aa00597cf46089f2152b492ab98b21b0ab5350276410b622931439c99f`,
20,701 bytes. Check 6 consumed those exact bytes. The artifact manifest records
the final code, note, handoff, complete audit, manifests, and all retained logs.
No checker or writer is left running at final handoff. This is an author
construction/checking receipt, not independent acceptance. A fresh nonauthor
review and primary integration are required before publication.
