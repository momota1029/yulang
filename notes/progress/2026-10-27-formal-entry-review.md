# Independent review: formal admission and actual Force entry

Date: 2026-10-27. Reviewer: `/root/principality`, not an author of either target.
Verdict: **ACCEPT the stated local constructions.** No blocking, major or minor
proof defect found within the acceptance boundary below. Original whole
soundness, Effect hygiene, principality and inference termination remain OPEN.

## Frozen targets and inspected scope

| Target | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `notes/theory/lean/YulangClosure/OriginalForcedParameter.lean` | `d16a45c459ea78b0f583ebd34d7a442d7247b55358ff6d990e3416c3d841aedf` |

Both hashes matched before and after review. All 524 + 148 source lines were
read, including every definition and proof. The source checks used SG
`2026-10-08-source-generalize-definition-and-proof.md` §§3.1–3.3,
`2026-10-08-call-semantic-input-realization.md` §§2–3, and the original
Entry-Value/Entry-Retained construction. The dependency review followed
`Parameter`/`FormalAssignment`/`Telescope`, the actual Lambda/Build tree,
`DataAdmitted`/`GoalDataAdmitted`, `PhiCar`/`PhiT`, the value-only relative
operator, and `bindEvent`/`bind_phiW` through the native `bindValue` constructor.

## Findings

**Formal declaration ownership is explicit and noncircular.** `Introduction`
retains the actual parameter, route and its entire typed ambient telescope.
`selection` reads the `FormalAssignment` at those prior values; no invocation,
returned argument, successful checking proof, or semantic membership is an
input. The source-selected entry mode chooses a Descriptor for Value and an
Interface for retained Computation. Both description-frame producer equations
refer to the existing respective source constructors.

`ViewPacket` references this selected introduction as a type index and carries
the independent view, assignment and proof-witness fields. Its encoding does
not overwrite a Desc or Interface declaration. That is consistent with SG's
separate Desc and ViewLogic ownership in this **local interpretation**. It is
not a completeness or conservativity theorem for every previously supplied
opaque `LocalAdmissions` interpretation.

**The actual Build is consumed at the proper telescope.**
`actual_build_selects_formal` uses `build_entry`, which reconstructs the genuine
source rule from the supplied Build solution and peels the original annotation
wrapper. It obtains Description and ViewLogic before the universal invocation,
then each invocation's actual receipt and entered body. The contract equality
is proved from admission inversion and decoder equations; it is not an input.
`actual_build_from_whole_telescope` supplies the corresponding initial decoder
by replaying the same full typed telescope. `Prior` retains independent
publication, anchor, event-path, name, replay and initializer data; the theorem
constructs an environment rather than resetting an existing one.

**Actual events do not overwrite the selected formal contract.** The proof
checks every runtime payload constructor, plus the Shared constructor. Source
admission and goal-indexed checking admission remain distinct, and the order of
their kernel wrappers is correct. The explicit unchanged-runtime-admission
theorems retain the original checked challenge domains and independent receipt,
Return, response, rigid-operation and one-shot premises. EventProof admission
is also unchanged. Value entry retains Return/rebind followed by Shared;
retained Computation entry uses its own Shared route without inserting Force.

**Actual Force supplies the two recursive bind premises.**
`meaning_force_return_fields` unfolds the same carrier's `PhiCar`, then the
actual observation's `PhiT`. It derives force incidence, the world at that
observation, the returned row's event equality, and the returned value's
membership. These are not independent hypotheses. The Background version
uses its own relative fixed point: the carrier/trace/world branches cannot be
value holes, and no completed `Checking` result is cast into Background.

The two `bind_after_force_return_*` theorems feed these derived facts to the
existing native bind proof. The bound row is the actual raw returned value and
root at the actual observation event. `bindValue` appends that value cell and
extends the actual selected lexical parent; `bindEvent` retains its full
current world and the existing Shared strategy. Compatibility is used to
transport both old installed objects and the new returned field to the one
post-bind event. No completed post-bind world is assumed.

## Acceptance boundary

These limitations are explicit inputs or exclusions, not findings requiring a
proof repair:

- `actual_build_*` assumes satisfaction of the actual generated Build; it does
  not construct a solution or prove native inference success.
- The typed prior telescope preserves all supplied frames but does not itself
  authenticate every enclosing source route, event-parent incidence or native
  history. A full global assembly still needs that owning correspondence.
- `localAdmissions` is attached to one selected introduction. The flat Binder
  API does not encode its occurrence route. The module correctly exhibits
  this limitation in `distinct_routes_same_flat_binder` and
  `no_erased_owner_singleton_admission`; it does not claim simultaneous
  route-aware kernel assembly for all equal-site introductions.
- The Force theorems assume genuine whole-carrier membership, the actual
  demand and force relation, and the independent `traceForm = pureReturn`
  readout. They derive world/value membership from those premises; they do not
  prove that Force returns, construct the complete original Force relation,
  or discard pending/diverging observations.
- The native bind retains explicit finite-vector, saved-reference bounds,
  selected-parent lookup, post-bind compatibility, coherence and world guards.
  None is converted into an unconditional truth.
- The bind theorem's `descriptor` is still a parameter. Its equality with the
  original FormalAdmission selection, and the corresponding actual Return
  readout at that descriptor, need the source/Force correspondence. These two
  modules do not alone compose into the whole source-owned formal-entry law.
- No full complete-Call certificate, arbitrary W/Z declaration, foreign-kernel
  embedding, source/native equivalence, principal ordering, or whole-language
  theorem is established.

## Independent verification

The parent freshly built both targets and owns the cache. This reviewer used
one direct pinned Lean invocation, with no build and no `-o`, to inspect all
**39 authored theorem types and their complete transitive axiom sets**. Each
audited declaration was checked to have theorem kind. The command exited 0
without warnings:

```sh
timeout 120 env LEAN_NUM_THREADS=1 \
  /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 --root=/tmp/yulang-principality-formal-review \
  /tmp/yulang-principality-formal-review/Audit.lean
```

The imported parent-built objects use pinned Lean 4.35.0. Root owns the full
generated/private declaration census; this review does not duplicate or claim
that larger audit.

| Complete axiom set | Authored theorem count |
| --- | ---: |
| none | 13 |
| propext | 16 |
| propext, Quot.sound | 6 |
| propext, Classical.choice, Quot.sound | 4 |

The four choice-dependent roots are `actual_build_selects_formal`,
`actual_build_from_whole_telescope`, `value_entry_body_keeps_contract`, and
`computation_entry_body_keeps_contract`. `meaning_force_return_fields` uses no
axioms; its Background counterpart uses propext; both final force/bind theorems
use propext and Quot.sound. No project axiom, `sorryAx`, unchecked native
evaluation or kernel bypass was found.

| Review evidence | SHA-256 |
| --- | --- |
| `/tmp/yulang-principality-formal-review/Audit.lean` | `f5067cd28f29f0fb1bb3174e634ae8e939ac28617839882bbd7f709823a7aa74` |
| `/tmp/yulang-principality-formal-review/review.log` | `bbfeed98dcaa836285ac8b37297ac55b0f6ab09e42c2ca4e32de9c47f26eb07d` |

No target, compiler, configuration, cache, Git or shared status was modified.
Only this leased review note and the two named scratch audit files were
written. **Review writes stopped; no checker or descendant remains running.**
