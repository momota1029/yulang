# Sprint PAPER-HEAP-OBSERVATION-20261026/r59 — finite graph observation to Force

Status: PRIMARY-AUTHORIZED CANDIDATE; work begins only after this contract and
current state are committed. Branch `yulang3`, baseline
`4eb348f7ebf53509ae701c6b0434041a90f8f573`.

## Original parent and exact outcome

The unchanged parent is the paper's execution type-safety claim and its
recursive graph/value-observation component, especially
`docs/yulang-operational-type-safety-ja.tex` §§3 and 3.8, lines 252–326,
488–500, and 981–990. The paper uses immutable finite heap `H`, graph typing
`Xi`, graph-reference observation, type-application normalization, and a
separate Force/Delay step. Its guard condition is required for terminating
one-node observation. Whole-language execution safety, graph guardedness,
source/native correspondence, type-inference A/B and production remain OPEN.

This sprint proves one exact finite path: (1) a successful first-match heap
lookup of a typed graph reference returns a payload with the same graph type;
(2) finite observations may dereference graph references and reduce type beta
only at the root or in a type-application function position; (3) every such
finite path preserves the represented paper value typing; and (4) if the
observed Force operand is a typed `delay body`, the existing Force/Delay
`PaperCoreStep` yields a body with the same result type. Apply this after
`PaperTypes.FreshHeap.finite_allocation` to its exact allocated heap and graph.

Use `PaperValueTyped`, `PaperComputationTyped`, `HeapPayloadTyped`,
`PaperTypes.FreshHeap.allocate`, `PaperTypeBetaExecution.typeBetaValue`, and
`PaperCoreStep` unchanged. Define an inductive observation relation that
faithfully records the paper operations above; do not add observations inside
data constructors, lambdas, delays, metadata, or type arguments. A graph-read
step must use the actual `lookupHeap` result and first-match semantics. A
type-application function-context step must preserve the same substituted
result type. A type-beta step must be the existing accepted operation.

The finite-path hypothesis is explicit. This theorem does not prove that every
heap path terminates or satisfies the paper guard. In particular, preserve
R29's self-alias example and demonstrate that the finite relation can loop;
do not claim normalization, termination, cycle freedom, completeness of
observation, or the original heap-typing theorem.

## Method, success evidence, and falsifiers

Construct `PaperHeapObservation.lean` with these public results:

1. `heapLookup_payloadTyped`: successful heap lookup plus `HeapPayloadTyped` yields a payload typing at
   exactly the graph-reference type (use equality of the two successful
   first-match graph lookups).
2. `observationStep_preservation`: one allowed observation step preserves `PaperValueTyped`, including
   type-application function position and accepted type beta.
3. `observationTrace_preservation`: induction over the actual finite observation trace preserves typing.
4. `force_observation_preservation`: a typed `force source` whose finite operand observation reaches
   `.delay body` gives a typed intermediate `.force (.delay body)` and the
   existing `PaperCoreStep` result `body` typed at the original result type.
5. `allocated_force_observation`: consume `finite_allocation`'s actual
   hypotheses and uses its resulting graph and heap; no independent heap or
   graph witness is substituted.
6. `selfAlias_observation_loop`: show why the relation does not
   imply termination. Duplicate IDs, first-match collisions, a mismatched
   lookup type, and beta at a non-redex are explicit falsifiers or excluded
   cases.

Check the focused module and every public declaration's full type and axiom
list. Reject `sorryAx`, project axioms, unsupported standard axioms, changed
dependencies, and any theorem whose assumptions already contain the desired
result. Fresh independent M1 review must be CLEAN before root import/integration.
The source lane reports exact constructors/consumers and whether any approved
Rust edit is supported; no code change is assumed.

If an external proof artifact arrives during the sprint, preserve its original
bytes and provenance as a separate immutable input. Check its complete claim,
source scope, direct dependency hashes, public theorem types and full axiom
reports before using it. A same-path/different-bytes arrival stops integration;
never overwrite either artifact or silently fold an external claim into this
module.

## Frozen inputs

All hashes below were read from the clean baseline above and must be rechecked
before work and at freeze:

```text
a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b  docs/yulang-operational-type-safety-ja.tex
e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932  notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41  notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
b0ff39ad89fcb83559cca3147ae55fa7e7f6c31c1b130ec9cd7608e33d1f696e  notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f  notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9  notes/theory/lean/YulangClosure/PaperCoreStep.lean
7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925  notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean
0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8  notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean
d6523cba7a7b68871f56d359168f37d83bef27fa8ae2081777094e794b3cbea7  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-adjudication.md
2611315d23588db8b02f8644bc9d8c495e388566659037e59f3b3501b49e25b1  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-review.md
5c693fedf8e98a471bdf5f6712e49ca0146a0f97957acfb946732fc54dc5f60c  tasks/agent-loop/sprints/paper-type-beta-execution-r58-outcome.md
059cb2de4cdc8c1e746628f485f445671a927c13f82cef8bbf8defb6c0bbe39c  tasks/agent-loop/inbox/paper-type-beta-r58-review.md
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
231a6cccb03efee4a2dc2fd3e8fb70e85ec2f9eb960492e04e39ae7163dc4ec1  notes/theory/lean/README.md
6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907  tools/inference-playground/src/runtime/program.rs
b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e  tools/inference-playground/src/runtime/machine.rs
```

R29 is accepted only as finite allocation plus `HeapPayloadTyped`; R58 is
accepted only for represented type-beta preservation. Both boundaries are
immutable inputs. No new semantic decision, source restriction, compiler
implementation authority, or production/cutover authority is granted.

## Continuing lanes and exact leases

* Constructive proof lane: one registered `lean_prover`, no descendants.
  Isolated checkout: `/tmp/yulang-r59-heap-observation`. Exact write lease:
  `notes/theory/lean/YulangClosure/PaperHeapObservation.lean`,
  `notes/theory/lean/.lake/R59Audit.lean`, its dedicated `.lake/build`,
  `tasks/agent-loop/inbox/paper-heap-observation-r59-worker-checks.txt`, and
  `tasks/agent-loop/inbox/paper-heap-observation-r59.md`. No root import,
  shared source, dependency, manifest, test, Rust, Git or network writes.
* Complementary source lane: one `researcher`, read-only on the two pinned Rust
  owners and governing paper; exact write lease only
  `tasks/agent-loop/inbox/paper-heap-observation-r59-source.md`. Establish the
  source constructors and heap/cell consumers, compare them with this exact
  paper path, search for a real source-to-paper bridge, and falsify an unjustified
  immutable-heap identification. Do not propose semantic changes or edit code.
* Primary owns this contract, `current.json`, isolated checkout/setup, exact
  verification receipt `tasks/agent-loop/inbox/paper-heap-observation-r59-primary.md`,
  review adjudication/outcome, root import, staging, commit and push.
* Fresh `compiler_referee` after both writers stop, zero checker calls, 180
  active seconds. Read-only review; primary records its returned receipt at
  `tasks/agent-loop/inbox/paper-heap-observation-r59-review.md`.

The worker freezes before review. Reviewer checks input hashes, theorem types,
all observation constructors, allocation composition, source-claim boundary,
complete audited output and the self-alias loop. Any blocking/major issue
blocks integration; batch repairs only after adjudication.

## Resources and stop conditions

Total sprint cap 1800 active seconds; reserve 180 seconds for integration.
Proof worker: 600 seconds, 8 literal checker calls, 90 checker seconds.
Researcher: 240 seconds, zero build/test/checker calls. Primary: 600 seconds,
4 literal checker calls, 90 checker seconds. Fresh reviewer: 180 seconds,
zero checker calls. Total assigned work including review is at most 1620
seconds. No carryover. At most one heavy Lean process, `-j1 -M1024`, one thread.

Each Lean lane resolves native Lake read-only, verifies both Lake and
`env lean --version` against Lean 4.35.0, then builds only
`+YulangClosure.PaperHeapObservation` and audits all public declarations.
Primary repeats the focused build and complete audit on frozen bytes. No
default/full build, tests, Cargo, runtime probes, `lake update`, installation,
or dependency changes. Stop on changed pin, more than two diagnosed proof
construction failures, first failed primary verification, audit/axiom mismatch,
unclear observation authority, timeout/resource cap, writer uncertainty, or
session end. Preserve every failed source and output; no same-command retry.

After CLEAN review, primary integrates only the new module and one leading
import into `YulangClosure.lean`, then verifies the exact root delta and the
focused result, updates the compact history/outcome, inspects the full outbound
range, commits and non-forced pushes if upstream remains compatible. Parent
graph guardedness, actual source heap realization, full executor preservation,
inference A/B and production remain OPEN.
