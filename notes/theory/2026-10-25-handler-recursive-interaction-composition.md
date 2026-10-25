# Combined recursive allocation and external interaction

Status: primary composition candidate; source allocation and saved-entry composition
now have a shared Lean module. No independent review or full parent-theorem
closure is claimed.

## Joined results

`HandlerGraphRecInteraction.lean` imports both frozen lanes. It proves the six-sort
reference map commutes with recursive-name closure, identifies `mapOld` with the
actual reference map, and constructs the exact immutable embedding for
`Recursive.allocate`. The source-allocation wrappers derive new-graph typing
from source RHS derivations and old captures, and derive the allocation guard
from the old guard plus the finite fresh-cycle criterion.

The interaction composition is quantified over arbitrary finite RHS families,
old reference types, current runs, arenas and saved entries. `run_source_extension`
uses a source-constructed allocation as an actual Run extension. The saved-entry
invariant derives typing for every transported entry. `run_source_answer_old`
then answers any selected old entry with a reference to a source-allocated node,
using the extended graph's reference type and deriving graph well-typedness from
the source RHS. It proves typing and progress for every execution prefix using
the actual guard of that allocated graph.

The primary Lean runner records all attempts, including the initial namespace
syntax failure, subsequent proof repairs, and the final passing module. The
current combined module passes Lean with no warning. The failed attempts are
preserved in the verification JSONL; they are not evidence for theorem failure
or acceptance beyond the final frozen source and its passing receipt.

## Remaining join obligation

The primary added a concrete joined trace: it publishes the original root
request, answers with a handler-bearing value obtained by actual source
allocation, follows six raw steps to a later root request, publishes that
request, performs a second actual source allocation, transports both saved
entries, and reuses the original entry with a reference to the first allocated
value. Lean checks the continuation endpoint directly. The source RHS in this
trace is handler-bearing but does not itself refer to its recursive name. The
same module also types a genuine self-referential handler-bearing source RHS,
derives its actual source allocation typing and finite guard, and answers the
original published entry using that allocated recursive callback. It also
derives typing and progress for every finite internal prefix after that answer.
The trace to the later request, second allocation and reuse is currently proved
only for the first, non-self-referential callback; combining the recursive
response with that exact continuation endpoint remains open. The sprint remains
partial against its stronger
concrete-trace contract; no endpoint equality is assumed.

## Application to the original paper obligation

The pinned paper `docs/yulang-operational-type-safety-ja.tex:978` states
immutable graph extension from actual simultaneous source RHS substitution;
lines1140–1164 require arbitrary finite internal steps, independently typed
external responses, fresh extensions and repeated continuation resumption.
This joined construction applies the generic source allocation and saved-entry
invariant to that grammar. Paper lines146–201 additionally contain tuples,
sequences, records, nominal constructors, type abstraction/application, roll,
explicit continuation values, mapop, rec instructions and templates. Those
omitted forms remain obligations. Rec source admissibility rejects cycles
consisting only of transparent aliases/evidence; the fresh-cycle test is an
explicit source graph premise rather than an assumed terminating recursive
computation.

## Source/native boundaries and scope

Primary inspected the pinned native owners during this sprint:

- `tools/inference-playground/src/runtime/machine.rs:2500` (`begin_local`)
  reserves a `None` cell, may add its recursive binder, and evaluates actual
  initializers in sequential block order. The mathematical simultaneous family
  is not thereby a native store snapshot or a proven whole-block supplier.
- `machine.rs:600` (`resume_host_write`) matches the current stopped request and
  handle/operation, then rejects `saved.resumed`. This one-use host interface
  does not supply the theory's repeated arbitrary saved-entry answers.
- `machine.rs:1913` (`enter_template`) follows concrete Hole/Bind/etc. nodes,
  carries control/view/owner information, and executes actual saved frames.
  `continuation.rs:13` stores declaration/original event and explicit Bind,
  Owner, ForwardHandler and View template nodes. Mapping these native states
  remains an independent correspondence obligation.
- `machine.rs:1097` (`CatchReturn`) validates installation and searches actual
  value arms. The previously recorded empty-value-arm semantic mismatch remains
  open; this sprint does not identify the two machines.

NO_SAFE_CODE_SLICE for dependent production changes. This packet is authorized
implementation-independent constructive theory. Full paper forms, recursive
types, polymorphism, metadata/Grant/owner adequacy, native memory and scheduler,
and original Simple-sub A/B claims remain OPEN. No compiler or runtime edits.

## Verification and review

The source modules are frozen for the current review snapshot. The primary
runner verified each module serially with the pinned dependency and input hashes.
The explicit declaration query and its axiom output are recorded separately.
Independent reviewers must check the author lanes and this join. The review
reports must mark the missing concrete joined trace accurately. CLEAN review of
this partial packet would be insufficient to claim the original parent theorem
complete, which remains OPEN.
