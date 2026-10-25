# SOURCE-GENERATED-INTERACTION-20261025 / independent proof review revision 1

Verdict: **CLEAN for the frozen source-generated research-history theorem and its recovered trace application; conditional application to the original paper parent.** No blocking mathematical or scope-conformance defect found. This verdict does not close full-paper safety, native correspondence, production, or original Simple-sub A/B.

## Identity, authority and frozen inputs

Reviewer `/root/isolated_proof_review_01a17247`, fresh nonauthor, assigned by parent
`01a17247-73d1-7663-9c3b-ff5b5b9c2ef1` through the supported task delivery.
Requested model/effort `gpt-6-astra/medium`; observed model/effort UNKNOWN/UNKNOWN.
No contribution to proof construction or repair, no descendants. Exclusive root:
`/tmp/yulang-source-interaction-01a17247-20261025`; assigned branch
`codex/source-interaction-01a17247-20261025`, baseline
`0132d07ca7e149b59f529469d1479a1c8cfa577a` (contract identity, no Git command run).
Only write lease: this report. Root AGENTS and pre-sprint hard invariants,
current state/README, both contracts, relevant authority and sprint rules,
research-core design and original paper obligations were inspected.

Byte hashes independently recomputed:

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SourceGeneratedInteraction.lean` | `16952fef6ea505cce0d7f8afa6bf39cd3609119626f7857d6beaa88737c5b003` |
| Original stopped author handoff `tasks/agent-loop/inbox/20261025-source-generated-interaction-r1.md` | `44e6d5f6cac0baa175261425df0e21a25d31bda48a920f103a9e527359e67317` |
| r1 contract | `013fe582ead230d29fbaa4ab6d977f7b2af3df8cac0db5b5f8efed381fee32c2` |
| r2-isolated contract | `a6c497c11995ebf6ec0078c3890c58f875fbcae6ce0335c28a4213e267241ca8` |
| isolation inventory | `87b1c2ba4343a11bcfa3439e286454aeda08bed14ff87f726fe5a55872ef77db` |
| Verification JSONL exact first three lines, including terminal newlines | `f1854b0b2fabc84b0ed221b641c170afd19a87ff3f758709acc50c0ad24dd4b2` |

All 15 direct r1 table pins match, including the paper, accepted recovery
outcome and recovery ledger. Additionally, all 151 distinct nongenerated input
paths collected from the seven recovery-ledger rows exist and match their
recorded hashes. The accepted 59-module chain is reused, not independently
reproved here. Current source/object inputs recorded by the third row match.
The primary runner changed between module and query calls; each call records
its own hash and stable before/after inputs. This is not a proof dependency
mutation. Original source provenance is
`7eb9d792f6093a0b82be85e2a751732febede649d9a4a2ae25eda0bd1d14d8d2`.
A diff of the first two embedded sources confirms that the primary changed
only references to `secondTypes` / `secondArena` to `RecursiveTrace.*` in the
recovered namespace. The frozen handoff describes the original unchecked
candidate; the checked repair is attributed to the primary coauthor.

## Mathematical audit

1. **Domain and quantifiers — CLEAN.** `SourceGeneratedInteraction.lean:20–51`
   defines finite inductive histories with arbitrary `B R : Type`, not finite
   reference sorts. Each new family alone is `Fin n`; neither positivity nor
   nonemptiness is required. At n=0 all family-indexed premises are vacuous;
   the sum embedding and finite guard construction remain valid. Internal steps,
   root publication and answers are the existing raw relations. Allocation is
   exactly `allocate graph (sourceFresh capture rhs)`, with `joinTy`, mapped
   current term, and the entire mapped arena. There is no endpoint typing or
   final guard premise hidden in a constructor.

2. **Local source conditions — CLEAN, explicit residual premises.** Lines39–41
   require all RHS derivations in the simultaneous `sourceContext nu env`,
   independently typed old captures, and `FreshNoCycle` of the actual closed
   fresh values. `HandlerGraphRecAllocation.lean:542,608,664–675,792` uses a
   recursive-name prefix, simultaneous name closing, lifted old captures and
   substitution; `HandlerGraphRecInteraction.lean:98–143` supplies the actual
   immutable embedding and extension typing. Fresh node typing is derived from
   these source derivations, not assumed as an unrelated well-typed endpoint.
   Source realization of these premises for native executions remains open.

3. **Guard induction — CLEAN.** Lines82–93 derive Nonempty of an actual guard
   from only the initial guard. Every allocation consumes its local cycle
   premise via `sourceExtension_guarded`, `allocationGuard`, then
   `FiniteGuardDecision.allocateFiniteGuard` (lines274–280). The latter uses
   `guardOfNoCycle` and computed finite height/rank, together with the original
   graph certificate; old nodes cannot acquire fresh edges. `allocation_guard_iff`
   (RecAllocation:786 and FiniteGuardDecision:323) confirms the local cycle
   condition is exact for this construction under the initial guard, not an
   arbitrary stronger sufficient condition. Prop-to-Prop elimination of History
   and Nonempty is legitimate; consumers also conclude Prop. No choice or
   caller-supplied final-guard oracle is used. The initial guard explicitly
   includes a finite rank ceiling even when its reference type is infinite;
   the theorem does not assert that every arbitrary well-typed graph has one.

4. **Exact erasure and all records — CLEAN.** Lines59–77 prove Run erasure and
   graph typing simultaneously. Each induction case preserves the same graph,
   current computation and list. The allocation case uses the real source
   embedding; every arena entry is mapped, with no filtering or newest-only
   restriction. Lines97–103 apply `run_invariant` to preserve the original
   result type and every member. Lines171–184 reuse reached-root provenance and
   its immutable embedding Chain with exact code/payload transport. The stated
   origin is an existing Run origin; this theorem does not claim a stronger
   History-typed origin witness.

5. **Responses, prefixes and outcomes — CLEAN.** History.answer requires exact
   `Answer` plus independently established response typing. Answer's defining
   equality in `HandlerGraphInteraction.lean:72–74` is equality of the complete
   operation instance, not only its numeric ID. Answers keep the arena and
   permit repeated use of any member. Lines143–151 construct the second answer
   from the first, and arbitrary finite repetition is expressible directly by
   History.answer. Lines155–167 additionally quantify over each independently
   typed response in an arbitrary finite family; this family theorem supplies
   per-response prefixes, not a separate batch-execution trace. Lines107–129
   derive safety and the exact four alternatives for every finite raw prefix
   after every represented history. `internal_prefix` includes the zero prefix.
   The same original `result` is retained. Terminal requests are actual outer
   requests, not requests hidden under handlers.

6. **Recovered application — CLEAN.** Lines193–252 reconstruct the actual
   op73 answer, self-recursive allocation, six raw transitions exposing op75,
   root publication, second source allocation, reuse of the older op73 entry,
   and another op75 request. Both arena entries persist. The whole-lambda binder
   equation is the dependency's `whole_source_closure` (RecursiveTrace:29–36),
   not an assumed endpoint. `every_prefix_safe` / `every_prefix_four` consume
   `oldGraphGuard` and the generic induction, with no `secondGraph_guard`
   premise. The concrete example uses a singleton recursive family and empty
   outer capture context; it is not evidence of all native capture layouts or
   an unbounded recurrence theorem. The generic result above retains arbitrary
   typed capture contexts and finite families.

## Verification evidence audit

No Lean, build, test, native execution, or verification runner was executed by
this reviewer. Read-only Python was used for byte hashes, JSON inspection and
embedded source comparison; an initial `python` invocation was unavailable and
performed no action, then `python3` was used.

Frozen row1 retains the real ambiguity failure (exit1), including its temporary
`sorry` warning; its output objects are MISSING. Row2 checks repaired bytes,
exit0, no warnings/stdout/stderr. Row3 checks 23 explicit matching #check / #print
axioms pairs, exit0, no warnings/stderr, with 23 complete reported closures.
Every reported axiom belongs to `{propext, Quot.sound}`; no `sorryAx` or
`Classical.choice` appears. Row2's generated olean hash
`c84017413621a39d53c26bbae96206b447f72f1d497e89fed24325413d6784d0`
is exactly row3's imported olean pin and matches the present object. The ilean
also matches its module output pin. All three calls record stable inputs.
Recorded total Lean time is 3.416548452 seconds. These are primary execution
receipts; the independent semantic verdict comes from the source audit above.
Any appended Cargo/native rows are outside this review.

## Original-parent application and remaining owners

The immutable-extension lemma at `docs/yulang-operational-type-safety-ja.tex:980`
and `thm:safety` at line1140 require the original broader grammar and execution
scope. This result supplies the generic finite interaction induction, including
derived graph guards, for the explicit source-generated research-machine
subdomain. It genuinely removes the need to supply a final guard separately
for each such history. It does not replace broader Run with History or assert
that arbitrary typed extensions are guarded.

- **SGI-NATIVE-1 — OPEN, primary/source-native intake.** Establish that accepted
  source execution and replay inhabit this History, including actual recursive
  binder/cell identity, environment capture realization, closure/RHS typing,
  response representation and local guard evidence. Native owners include
  begin_local, Frame::Local, Lambda capture, lookup and EnterTemplate. A native
  probe can distinguish behaviors but cannot establish the general relation.
- **Full-paper graph/source forms — OPEN, primary/full-paper proof intake.**
  Cover the omitted paper syntax/metadata/effects/polymorphic instances and its
  general fresh-extension contract, preserving the original quantifiers.
  Initial graph typing, closed initial term typing and initial guard remain
  explicit assumptions here; each local RHS/capture/cycle premise must be
  supplied at its genuine source owner.
- **Production and original Simple-sub A/B — OPEN, primary semantic/inference
  owners.** No inference rule, compiler source, expected output or production
  authority was changed or certified. The new theorem alone does not settle
  these gates.

No repair request is required for the frozen proof. Integration/adjudication
and status promotion remain the primary's responsibility.

## STOP and resource receipt

Grant450 active seconds, no renewal. Exact pre-clock startup duration was not
recorded; do not invent an exact total or refund unobserved budget. First sampled
UTC was2026-10-25T09:21:37.666520+00:00. Report freeze UTC: 2026-10-25T09:22:52.249973+00:00.
Elapsed between recorded clock samples: 74.583 seconds; reserve the
full450-second grant conservatively. Work completed within the grant.
Three substantive stages: contracts/hash/provenance audit; mathematical and
parent-scope audit; verification-receipt audit and frozen report.

STOPPED after this single report write. No processes remain from this reviewer,
no asynchronous process was launched, no descendants exist, no scratch was
created, no Git operation was run, and no file outside the exclusive report
lease was modified. Every shell command had the explicit isolated workdir.
