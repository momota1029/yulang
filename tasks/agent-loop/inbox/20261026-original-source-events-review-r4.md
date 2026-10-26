# OriginalSourceEvents: independent review r4

Verdict: **REPAIR REQUIRED. The frozen packet is not accepted.**

Two findings require repair: a generic constructor-route collision, and an
incomplete scratch declaration census. The primary was notified immediately
and instructed this review to stop after retaining the clean discriminator
evidence. No publication or integration acceptance is supplied here. Remaining
construction correspondence has not been adjudicated as complete merely
because the module builds.

Reviewer: `/root/function_future_review_r4`, independent nonauthor generic
proof-role fallback. Applicable AGENTS/base/proof rules, the
`yulang-lean-proofs` skill and generic role instructions were followed. No
descendants or model override; effective model/effort settings are UNKNOWN.
Only this receipt and the assigned
`/workspace/scratch/f98087c7ac1a/source-events-review-r4/` were written. No
repository source/core/configuration/import/author metadata/Git/shared-status
change was made. `/root` remains the sole adjudicator and publisher.

The review began at 2026-10-26 15:38:14 UTC under a 1200-second budget, with
at most three focused 120-second bundles. All three were used and have stopped.
The new disjoint native termination and WorldReadout work was not imported.

## Exact rejected freeze

The author records construction baseline `5428c5e62`; the primary supplied
review integration baseline `efa0e4453`. Acceptance of the following exact
bytes was requested, and is withheld:

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `b5a4b389414826666b65c14ed247189ee3b65334dad14f36562531314a78c3f6` |
| `notes/theory/2026-10-26-original-source-events.md` | `b9ac11a79d32192ec0e3d17716174e42bfa6e90d0fab1f85fc94fee03da927db` |
| `tasks/agent-loop/inbox/20261026-original-source-events-r4.md` | `c2660a362cd8561ee1aacfa4c98e73d8aa76c954e4a33e1ef1596f46b1abb14d` |
| `source-events-r4/freeze.json` | `bbbb36eb541980033766ecda670e92627623b8269d2557457f3f09c437c22ee3` |

All 274 producer artifact hashes, all three outputs and ten frozen dependency
source hashes were verified. The full rejected source, note, producer receipt
and freeze were copied unchanged to the review's `frozen-author/` snapshot.
The independent project contains the exact 11-module recursive source closure
and three unchanged configuration files, with an initially empty build cache.
The independent input manifest preserves all 14 hashes.

## Finding F1 — blocking generic owner/entry identity collision

Affected definitions: `owners`, `forestOwners`, `entries`, `forestEntries`,
and their downstream use by `actualKey`, `recordKey`, assignments and source
owner registration. All unqualified names here are under
`YulangClosure.OriginalSourceEvents`.

The forest walk gives the head its current route and the next sibling
`route ++ [1]`. A `RuleTree.choice` also gives its right child
`route ++ [1]`. These two different constructor positions therefore share
the same route. This is not just equality of raw Site coordinates: with the
same binder and enclosing scope, the entire generated Owner is identical.

The clean independent Lean discriminator uses:

```lean
def binder : Binder := ⟨7, .invocation, 0⟩
def leaf : RuleTree := .rule .lit 0 [] [] .nil
def eventNode : RuleTree := .forallE binder leaf
def collidingForest : RuleForest :=
  .cons (.choice 0 leaf eventNode) (.cons eventNode .nil)

theorem different_forest_positions_same_owner :
    forestOwners [] [] collidingForest =
      [owner [1] [] binder .actualEvent,
       owner [1] [] binder .actualEvent] := rfl
```

Wrapping this forest in a `.rule .sequence` produces two complete identical
owners at `[0,1]`, also proved by `rfl`. An analogous forest containing two
actual `.parameterEntry` nodes, with explicit `sourceFormalRole` and
`receiptFormation` atoms, produces `[registration, registration]` at route
`[1]`. Thus both owner and parameter-entry inventories have the defect.

The same Owner and the same supplied origin, parent path, occurrence and raw
operands necessarily produce the same `actualKey` and `recordKey`. An assignment
indexed by that key cannot distinguish these intended distinct occurrences.
`different_routes_different_keys` does not address this case: its prerequisite
of different routes is exactly what the walk fails to construct.

The accepted scope explicitly claimed complete routes for every existing
RuleTree constructor. The present `sourceRules` image appears not to emit
`.choice`, so this discriminator is a generic rule-tree counterexample, not
an original source program or a Yulang unsoundness proof. That narrower current
source image does not establish the requested generic route identity property.
The author's two-closure duplicate-Site example covers a different arrangement
and does not expose the choice-right/next-sibling collision.

Required repair: use an unambiguous path convention consistently in both
walks, preserve source scopes and actual Lambda/receipt/Return positions, and
prove generic route separation plus no duplicate routes for both inventories.
The primary's proposed convention reserves 0 for tree descent/choice-left,
1 for forest-tail advance, 2 for retained evidence and 3 for choice-right.
This review does not certify the proposal before its implementation and proof.
A regression for this concrete collision must accompany the generic invariant.
No source-image narrowing or Site-uniqueness premise may replace that repair.

## Finding F2 — scratch census omits generated private declarations

The producer audit enumerates imported module declarations by actual origin,
but its separate scratch loop tests only `EventsProbe.isPrefixOf name`.
That test excludes generated declarations whose full names begin with
`_private`, even when they originate in the scratch audit module.

The independent review reran the exact author audit and appended a second
enumeration of **every current-module declaration** using
`env.getModuleIdxFor? name == none`. The namespace-filtered 49 constants / 17
theorems were reproduced; the complete current-module count is **52 constants /
19 theorems**. The three additional declarations, printed with the independent
audit module's private prefix, are:

- `_private.ReviewCompleteAudit.0.YulangClosure.OriginalSource.sourceRules.match_4.eq_1`
- `_private.ReviewCompleteAudit.0.YulangClosure.OriginalSource.sourceRules.match_4.eq_2`
- `_private.ReviewCompleteAudit.0.YulangClosure.OriginalSource.sourceRules.match_4.splitter`

The first two are generated equation theorems; the third is a generated
splitter. All three have complete printed types and **no axiom dependencies**.
This is a completeness failure in the author evidence, not evidence of an
unexpected axiom or a false kernel theorem. The corresponding author-side
private names use its own audit-module prefix.

Required repair: enumerate the complete current module by origin, including
private/generated declarations outside the main namespace; retain the original
49/17 claim and the corrected 52/19 observation; publish the repaired packet's
actual new count and all full types/axioms. A namespace prefix is insufficient.

## Independent execution and complete retained evidence

The actual tools were pinned native Lean 4.35.0,
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. The bounded reviewer wrapper used one CPU/thread,
`-j1 -M1024`, at most 120 seconds per complete bundle and 1280 MiB aggregate
process-group RSS, with exclusive project/cache/TMPDIR ownership. The current
module was rebuilt from an empty reviewer cache; no author olean was reused.

| Review bundle | Actual outcome |
| --- | --- |
| 01 | Native Lake version succeeded; ordinary sandbox `lake env lean --version` failed installation detection before Lean verification. Full log retained. |
| 02 | Permitted escalation of the same bounded wrapper; fresh module build passed in 42.995479 seconds. The scratch discriminator's appended audit counters lacked explicit Nat annotations, so that probe command exited 1. The earlier discriminator proof declarations themselves produced no errors, but the command is not recorded as a pass. |
| 03 | After adding only the scratch counter Nat annotations, the complete bundle passed in 11.226884 seconds, peak group RSS 1175592960 bytes. The collision probe and complete origin/current-module audit both exited 0. |

No toolchain, installation, source or dependency workaround was used. The
failed normal startup and reviewer audit failure retain their original source
snapshots, logs and receipts. No fourth bundle was run.

| Clean evidence | SHA-256 |
| --- | --- |
| Fresh module build, `attempt02/03.log` | `0b4ecfab48572ad62fc899219507b2ed0d4e8a09497462dd48e2d87d69baf7c1` |
| Collision and scope-erasure scratch probe, `attempt03/04.log` | `a2d2a7e3f6c347b9b1f593084ded26cfbdec4e45a1bdba88c1ced6af94fed4c4` |
| Full module plus namespace-filtered and complete current-module audit, `attempt03/05.log` | `8981f7207aadf035a17bd29763b32e6a179ba6e688b4847d91c06baf4fe90b72` |

All 678 originating module constants, 180 theorem constants and 40 required
fully qualified roots were reproduced. Every complete module type/axiom block
and each of the author's 49 named scratch records exactly matches the frozen
author output. The complete current-module inventory adds the three omitted
private records. Three private originating declarations and the generated
`OriginalSourceEnvironment.put.eq_1` outside the principal namespace remain
included in the module census. No declaration was dropped to adjust a count.

Actual transitive axiom-set counts over the 678 module constants are: no
dependencies 593; `propext` 71; `propext` plus `Quot.sound` 4; all three accepted
standard axioms 10. Among the author's 49 scratch records the corresponding
counts are 38,7,0,4; the three newly exposed private records have no dependencies.
All records reject `sorryAx`, reduction bypasses and unapproved axioms.

The independent discriminator has 12 constants, including five theorems.
The three route/entry collision theorems depend on `propext`; the other nine
declarations have no axiom dependencies. The two additional scratch equations
expose erasure of an arbitrary Owner's telescope from each key constructor.
This receipt does not infer a separate semantic impossibility result from
those arbitrary-owner equations; F1 already holds with identical scopes.

The review also retains parser diagnostics. One header parser initially
rejected a legitimate wrapped universe suffix. The first scratch-count guard
exposed F2. A later reviewer assertion incorrectly expected direct `rfl`
discriminators to have empty transitive axiom sets; the actual `propext`
dependencies above replace that assumption. No Lean proof changed to alter
those dependencies. Original scripts/error records remain alongside the
corrected complete records and `verification.json`.

## Scope and handoff

The review read the actual 796-line module, note, producer handoff, source
Lambda/parameter/receipt/suffix construction, relevant RuntimeReadout and
Decoded Shared/runtime consumers, signature catalogue interfaces, SG §3.3/§5.2,
Call-input realization §§2–4 and selected contextual membership authority.
The source evidence retains the distinction between runtime EventField and
per-description EventProof, and requires initializer/rebind Shared evidence.
The two findings above concern the requested constructor/audit scope directly.

No full original independently admitted semantic Initial/Response/Resume/
FutureUse coverage, event-domain/value interpretation, global readout,
Outcome-to-retained-output link, full PhiW, Function soundness, KernelSound,
source cases, replacement, general L4 or native inference correspondence is
accepted by this receipt. A clean kernel build does not settle those obligations.
Further semantic review of the rejected bytes stops here, as directed by the
primary. Repair requires a new frozen packet and a new review budget.

The final private `artifact-manifest.json` records this receipt, the exact
rejected inputs, producer freeze/artifact hashes, all three reviewer attempts,
complete type/axiom records and retained failures. `stopped.json` follows it
to avoid a self-referential hash. All reviewer-owned writes and processes stop
after that freeze. A subsequently authorized author repair is a separate packet;
it does not alter this rejected snapshot or receive acceptance from this review.
