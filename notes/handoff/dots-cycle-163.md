# dots cycle163: finite coverage, ledger settlement, and conditional consumer resumption

## Scope and result (intermediate; verification/publication ledger below)

I21 Evidence lane only. I26 actual Settled guard/Step/Stable definitions remain unchanged.
V5 remains **8/14 open**; this is not general progress, completeness, principal typing,
termination, or a complete `evidenceNode`/`generatedChildren` proof.

The additions separate three claims rather than conflating semantic Evidence with
recorded packet settlement:

1. For arbitrary roles, registry, tracked state, root and finite selected dictionary,
   `PacketCoverage` means that each selected descendant has an actual recorded
   packet with the exact selected children. It implies Discharged of the root.
   Parent packet membership plus finite classified child dictionaries and their
   coverage implies PacketSettled. An already trusted input ledger, producer input
   entry and actual output-entry membership then imply a trusted output ledger.
   Reachability and semantic Evidence are not substituted for journal coverage.
2. `AliasCoverage` permits the same certificate at a recorded aliased site, with
   both sites present and actual Alias connectivity. Exact coverage implies alias
   coverage. This is not arbitrary alias rewriting of packet children.
3. Actual I26 reachability and root Stable, ordinary Extension of every historical
   packet context, explicit finite structural/history coverage, and a classified
   finite dictionary imply Evidence in every final model. Historical replay and
   finite syntax derive the selected Joint obligations and generated descendants;
   neither child Evidence nor a conclusion-shaped JointClosure is assumed.
   Coverage and ordinary-growth restrictions remain genuine assumptions. Inconsistent
   final contexts make the all-model claim vacuous; existence is not asserted.
4. A genuinely enabled, novel, guarded terminal child install discharges that child.
   If a recorded producer's other children were already discharged, it settles the
   producer, derives its recorded output trust from the old trusted input ledger,
   and supports actual consumer readback. A two-step theorem then installs the
   consumer only with explicit Generated, ordinary Installable, novelty and old
   packet guard. Those preconditions have not been manufactured from Evidence.

These are useful restricted bridges, not a claim that Stable implies PacketCoverage.
A full concrete nonterminal producer with genuinely fresh output followed by a
previously blocked generated consumer's successful installation remains open.
The reserved terminal output fixture alone is not that example.

## Recovery and authorization

Scheduled start 2026-11-13T10:27:19Z; work started 10:27Z. Hard deadline11:22:19Z.
Fresh integration head: 50a82661793b0a5b3739f0dd7136676826acd75a.
Prior public cycle162 final: 1ac6c0cbc8aeddafe9c94011a66eed71fd483eca.
Standing orders, inbox, AGENTS, previous report and completed heartbeat reread.
Prior writer stopped; no overlapping writer to the same publication branch.
Existing worktree retained; integration already an ancestor. New modules only;
Yulang.lean imports appended. Root Audit/README, existing semantic modules, spec,
notes/plan and Lake configuration are unchanged.

## Verification and resource limits

Lean4.35.0. Initial direct trust0 checks and public axiom audits passed for the
core exact/alias settlement, consumer-resume, and finite-coverage modules.
A focused Lake invocation was interrupted during shared-cache rebuild under
memory pressure; it is NOT reported as PASS. Some new cached oleans disappeared
and subsequent import checks failed until regenerated. Fixture elaboration also
exposed namespace shadowing/implicit finite-index inference mistakes; corrected
source requires final isolated replay below. No interrupted/empty log is a PASS.

A dedicated workspace cache with symlinked unchanged dependencies is used for
final sequential trust0 recompilation of every new source. New output objects
replace their own cache links, never shared cache targets. Public type/axiom checks
and an all-declaration dependency gate are recorded below when complete.
Only propext/Classical.choice/Quot.sound are permitted. Full repository build,
root Audit and full verify-lean are intentionally not run per standing orders;
reviewer must perform whole-repository verification. Diff-only verification is
reported separately from a build.

Yulang2 x-oracle read; no new live Yulang2 CLI test and no assertion that old
Yulang2 implements I26 rules. Usage quota unknown.

## Next bounded work

- Construct and validate the genuinely fresh-output nonterminal producer/terminal
  child/consumer execution prefix, including novelty and Generated certificates.
- Relate current finite syntax/history coverage to a broader actual I26 fragment
  without assuming JointClosure or child Evidence.
- Handle descriptor-changing reobservation explicitly; ordinary packet-context
  Extension does not cover it.

## Publication and final evidence

Pending below. Only work/dots-main is authorized. All intermediate checkpoints
must be fetched and compared to the fixed local source tree; heartbeat-only
changes are separated from source comparisons.

## Independent review boundaries

Read-only second reviews found no soundness blocker. Consumer resumption remains
a sufficient contract: ExplainedRead explicitly requires current Head and semantic
entailment from the stated fact list. It has not been proved that the new output
alone supplies every consumer read. The theorem permits already-settled producers;
it does not assert a strict before/after change without a prior-not-settled fact.
The exact-recorded positive fixture is terminal; alias coverage has no nontrivial
positive alias fixture this cycle. The recursive finite-coverage application has
an explicit current model and nonempty journal, so its semantic Evidence claim is
nonvacuous, but still does not imply packet settlement.
