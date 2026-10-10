# Packet 1 source readiness falsification

Date: 2026-10-10
Status: unreviewed static source characterization and conditional control-flow
derivation; no full readiness, certificate, or gate closure
Pinned baseline: `3a0bcb240896669718042dd0ee1cc5c89e9723d5`
Exclusive lease: this file only; complementary researcher leaf, no delegation

## Objective and result

Attack the source-reachability premise left open by
`2026-10-10-retained-input-indistinguishability-proof.md`: two legal observation
states for the same original component with equal complete retained input but
different readiness. Method: inspect actual source action construction,
execution, graph capture, and retained-input call sites. No detached model or
source execution was used.

No such pair is established. The immediate blocker is precise: the pinned
source has **no live call to `State::retained_input`**, hence no existing
source certificate-query observation boundary to which the pair can be tied.
Search of `crates/yu-solver/src` finds calls only in
`candidate_context_tests.rs`. The method at `candidate_context.rs:392–396`
explicitly identifies its consumer as a later packet. It always returns
`Incomplete`, appending readiness and dependent-observation gaps at :539–542.
Here “complete retained input” can mean equality of the full borrowed semantic
content; it cannot mean two current `InputCompleteness::Complete` results.

A narrower source-grounded result does follow. At the initial staged capture
in `execute_candidate_graph_plan`, every member schedule has successfully
returned. That boundary cannot contain two states differing in whether one of
those schedules remains unfinished. This resolves only the source-action
barrier, not the §5 completeness of a generated Effect circuit. Extending this
invariant to every `capture_candidate_graph` call is false as a control-flow
claim: local-use captures execute inside a member schedule.

## Authority and fixed hypotheses

Governing authority is
`notes/design/2026-10-10-contextual-attachment-admission-design.md` §§4–7:
actual construction and transport duties (§4), complete circuit/dependent
observation evidence and transactional late-edge invalidation (§5), and the
two approved shapes with later admission exclusions (§6). The accepted §3.1
attachment-set grouping and the retraction of the callback's former result
remain fixed. No readiness definition, source restriction, count cap, or
annotation meaning is selected by this note.

For the conditional source barrier, fix one collected source plan and one
definition SCC `C` in the native execution, with its ordered original member
identities, scopes, and roots unchanged. Assume:

1. Candidate graph mode and `candidate_source.active` are true, and execution
   enters through native `InferenceSession::execute`.
2. Collection and the SCC plan's member/identity lookups are valid; all relevant
   calls return normally with `Ok`, without panic or process termination.
3. Execution is the synchronous control flow shown in the pinned source; no
   external mutation, test injection, or reentrant direct call changes it.
4. The observation is specifically the initial staged member capture at
   `candidate_scheme.rs:730–737`, not a nested/local/use-time capture.

Define `SourceSchedulesDone(C)` as the event that loose actions and every
action in every original member schedule of `C` have returned successfully in
this invocation. This is a bounded executor predicate, **not** the design's
full certificate readiness predicate `Ready_R`.

## Derivation from the actual owner

`lib.rs:10242–10253` selects source mode, executes loose actions with `?`, then
executes the SCC plan. `run_candidate` executes before final observation
finishing (:10265–10278). Loose/root executors at
`candidate_source.rs:537–547` extract actions, call the synchronous action
loop, restore the same vector, and return its result. The loop at :549–576
visits each action in order, uses `?` on each fallible dispatch, and returns
`Ok(())` only after the loop ends.

Induct on the action index: entry to the next index follows successful return
of the current dispatch; reaching loop exit establishes successful return of
all actions. Induct on the member index in `candidate_scheme.rs:718–722`:
each next member follows successful return of the prior root executor. The
staged capture loop is textually after this whole loop (:730), and every
failure propagates out before reaching it. Therefore every state at that
initial capture satisfies `SourceSchedulesDone(C)`. Any two states in this
restricted observation domain have the same value `true` for this predicate,
regardless of retained-input equality. No input-fiber readiness impossibility
follows for this restricted predicate/domain.

The publication assignments to `state.graphs` occur only after all staged
captures and byte accounting succeed (:739–750). This supplies a control-flow
ordering witness, not a §5 circuit certificate or withdrawal implementation.

The schedules are restored even on `Err`. Consequently schedule vector
nonemptiness is neither a completion flag nor a remaining-action frontier.
`active_roots` and `active_uses` are installed before source execution
(:707–716) and cleared after graph installation (:753–754); membership alone
also cannot distinguish “currently executing” from “all members returned.”

`constrain_live_item_with_inferred_entry` separately drains the current typed
worklist and settles dirty intrusion before its loop exit
(`lib.rs:11837–11846`, :12100–12105). This is evidence for that synchronous
constraint call only. This audit does not prove that every source action
submits all logically required replay, filter, or residual duties. In
particular, action completion and a drained queue cannot establish completeness
of transitions not yet implemented or not submitted.

## Source control-flow falsifier for a broader shortcut

The attempted stronger assertion “every graph capture happens after all
member schedules finish” fails at an actual source dispatch seam:

```text
emit_candidate_source: source local name -> Action::Local
execute_candidate_actions: Action::Local -> route_candidate_local
route_candidate_local: with_route_transaction -> capture_candidate_graph
return to action loop -> remaining source actions -> root executor return
```

Exact locators: action emission `candidate_source.rs:362`, dispatch :570,
local-use capture `candidate_scheme.rs:1117–1128`. The latter explicitly
describes a use-time observation of a live scheme, without a promise that its
anchors are fully solved. After expression traversal, the planner appends the
root Annotation or Link (:452–473); a local-name action therefore precedes
that final source action in such a schedule. This is a real source-owned
control path, not an invented transition table.

This falsifies the universal capture-order shortcut. It is **not** a minimized
executed source fixture, nor the required equal-input/different-`Ready_R` pair.
The later root action can change retained contents, and a pending action alone
does not prove a readiness difference for the same Effect component. The
existing rich input's contexts, origins, all views/parents, sharing, and IDs
must remain equal to use the prior indistinguishability result. None were
discarded to fabricate a witness here.

Incoming definition uses provide another distinct capture site:
`candidate_scheme.rs:784–800` first requires an installed target graph, then
recaptures its live root. In source mode, later components still execute their
own schedules after initial installation (:689, :756). The initial barrier
does not establish absence of future dependencies or permission to keep
earlier observations after a dependency-changing route.

## Evidence still missing at the boundary

| Needed fact | Retained/native evidence and remaining premise |
| --- | --- |
| Authenticated observation phase | The executor knows the initial member barrier by control flow. `retained_input(&self, roots, views, parents)` has no producer/phase argument (:393–395). No live consumer transports that control fact into a readiness claim. |
| Complete generated circuit | Definition SCC iteration is not an Effect-circuit SCC certificate. Retained evidence follows relation/dependency/context incidences independently of solver/SCC edges (:406–407); it proves closure of stored references, not that all required producers ran. |
| Exactly either approved count relation | §5 requires identity seeds, complete recursive operators, attachments, sharing, filters, and all dependent observations. `ContextExpr` and `Dependency` retain syntax/incidences (:80–159), while nonidentity operations and Function-port dependencies can report `InertOperation` (:424–426, :494). Their retention cannot recognize a complete generated circuit by itself. |
| Filter/transport obligations discharged | The API always appends `FilterObligationsUnavailable`; some retained transport reasons additionally require lifecycle authentication (:515–525). Successful reference validation is insufficient. |
| Complete dependent observations and late-edge handling | The API always appends `DependentObservationsUnavailable`. No input field identifies the certificate's full dependent memo/publication set, withdrawal, exact recertification, private deferral, and rollback/retry generation required by §5. Existing intrusion `completed`, `generation`, and `dirty` (`candidate_intrusion.rs:16–18`) are real state but are not thereby the selected circuit certificate lifecycle. |

The exact missing premise for the full source question is an authenticated
observation domain and readiness condition tied to the generated Effect
component, together with either a reachable equality witness or an invariant
that makes that full condition constant on each complete retained-input fiber.
This source barrier is sufficient for the named source-action condition only.
It does not supply evidence sufficient to recognize either approved circuit.

Under `rules/compiler-engineering.md`'s obligation economy, safe certification
and invalidation are A (correctness); reconstructing the executor's completed
member position from graph shape would be D (discarded construction evidence).
Recognition and correct dependent observations remain real §5 obligations.
No gate is retired or weakened. There was one source-trace attempt and no
repeated toy probes. Stop condition is reached: further equality searching
cannot target a live query site because that site is absent at this baseline.

## Checks, coverage, and frozen dependencies

Commands used: bounded `cat`/`sed`/`nl` source reads; `rg -n` for
`retained_input`, capture sites, source executors, and gap variants in
`crates/yu-solver/src`; `sha256sum` over the nine dependencies below. Call-site
search found seven retained-input test invocations and zero production
invocations. No tests, builds, compiler/Oracle/source runs, executable models,
mutations, random seeds, benchmark samples, or broad formatting ran. The
search envelope is the native owners and direct call sites named above, not
all HIR generation or every downstream diagnostic/publication owner.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-retained-input-indistinguishability-proof.md` | `175370d4d736b1f289ac356bf68302043c769560b55ad5e2a48bf9651008a1a4` |
| `notes/progress/2026-10-10-retained-circuit-evidence-boundary.md` | `61bb53c7c67b0adf49da5472c7fe2fcc2cbc3cbe5cf43a4527620f5195d600b6` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |

These hashes pin inspected bytes; all nine were unchanged on handoff recheck. This
leaf changed no dependency. Compared with the historical indistinguishability
note, `candidate_context.rs` has a different hash, so its older content bridge
must not be treated as a proof over these bytes without delta validation.

Oracle independence: there is no experimental oracle. Source control flow is
the evidence rather than an assumed transition checker. The derivation shares
native Rust synchronous/`?` execution semantics, valid collection, and the
explicit hypotheses above. No independent reviewer ran on this artifact.
CPU/RSS and total task wall time were not measured; the packet supplied no
numerical wall/RAM allocation. Shell reads/hashes were short, sequential
lightweight processes; heavyweight process count is zero, children zero.

Workflow deviation: startup used read-only `git rev-parse HEAD` and
`git status --short` despite the no-Git packet. HEAD matched the pinned SHA;
no Git mutation occurred. The primary was notified. Subsequent work used
file reads/hashes only. Unrelated pending question files were untouched.

Recommended next action: have the owning Packet 1 implementation/proof lane
fix the exact certificate observation site and authenticate its source barrier,
then prove generated Effect-circuit and dependent-observation completeness
there. Carry the local/use-time exceptions into that packet; do not infer
full readiness from capture or queue quiescence.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-10-packet1-source-readiness-falsifier.md`.
- Baseline SHA: `3a0bcb240896669718042dd0ee1cc5c89e9723d5`.
- Dependency hashes: table above; no dependency changed by this leaf.
- Review status: frozen unreviewed research; conditional source barrier only.
- Checks already run: static source/call-site inspection and dependency hashes;
  no tests/builds/source runs; final dependency/whitespace inspection at handoff.
- Proposed checkpoint message: `research: bound Packet 1 source readiness by capture phase`.
- Shared-record deltas left for primary/curator: record the initial staged
  source-action barrier separately from full Effect-circuit readiness; retain
  the absence of a live certificate query and local/use-time capture exceptions.
  `tasks/current.md`, `tasks/research-lab.md`, design/index/theory records,
  production source, and question bundles were not edited.
