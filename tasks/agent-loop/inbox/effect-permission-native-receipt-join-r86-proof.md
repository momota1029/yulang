# R86 proof handoff — revision 1, FROZEN

Author/worker: `/root/r86_proof`. Claim class: **constructed but unchecked
conditional finite receipt relation and interface obstruction**. No Lean
acceptance, printed kernel type, axiom audit, independent acceptance, Rust
execution, exhaustive source extraction or original A/B closure is claimed.

## Authority, inputs and exact outputs

Packet: `NATIVE-RECEIPT-JOIN/20261031-R86`, original admission supplied as
`d07c1ca90`; contract baseline `a44adf1f2fda99f896debf11b5f58c207728b030`.
Contract SHA-256: `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`.
Initial input manifest SHA: `e94dfb586a42052073620809ec17936c9c78e3025e017a1ffedea89c2df8debc`.
Amendment 01 was notified by primary at `799cfef81` and read; it changes
source-lane read scope only. Current manifest: 9,762 bytes,
`511553a67c35cd9c9adf90230eae422f8418a12ffe952fb5223266a6f76d0377`.

Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md,
design-authority, inference top-level principles, current.json/README, the
fixed packet, Lean skill and sources/execution references, exact R57/R84/R85
definitions, R85 proof/outcome, original parent/correction, and relevant pinned
reader/producer sections. All original manifest file pins and prior-evidence
file hashes were verified by read-only Python hashing, exit 0. Accepted R84/R85
stdin dependencies were additionally reconstructed and hash-verified in memory.
No new semantic authority is inferred from research drafts or prior receipts.

Only writes:

- `notes/theory/lean/YulangClosure/NativeReceiptJoinR86.lean`: **24,130 bytes**,
  SHA-256 `ecad50df44c8db31d8836212a220eacba564aec22c59a3ee3cdcb6e7e96688d6`.
- This handoff, `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-proof.md`.

No root import, dependency, toolchain, lockfile, compiler, test, shared status,
question, scratch, generated output, cache, target or environment path was written.

## Source claim and correspondence

Original claim: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5–7, SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
Current correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md`
§§2–6, SHA `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
Quantifiers remain every supported original source, lawful finite construction
history and actual retained extrusion occurrence, with its actual origin,
receiver and polarity pairs. Preserve original lexical/type/event scopes,
recursive sharing, generalization/use, complete Call/effects/hygiene and one
joint source-admissible strategy/witness. Qualification is the fixed
Value-birth-level induced graph SCC rule. No source constructor or language
feature is removed by this finite, syntax-independent receipt packet.

Immediate original parent: `YulangClosure.OccurrenceQualifiedConsumerR66.Root`,
including the unchanged Incidence and BeforeAncestry requirements. Its R84
construction requires `YulangClosure.ConstructedPhysicalRootR84.Primitive`;
the receipt relation does not manufacture those premises.

Pinned dependencies:

| Dependency | SHA-256 |
| --- | --- |
| `ProviderNativeContextR57.lean` | `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63` |
| `ConstructedPhysicalRootR84.lean` | `5d8ad6429906cdf971dbb9ee44841223c1fcc28e6591e1a75d1f453ea4eac13d` |
| `NativeRootPremisesR85.lean` | `1677d965ba2afa01ff07951325d1026f2da2fef97b19cc37cc8ef1490fecedcc` |

Source mapping: candidate_context.rs:2284–2295 clones the full receipt and
updates only completed; :2301–2340 joins a unique full-inventory completion;
:3038–3095 joins within explicit origin/completion cuts and requires pending
false; :3183–3218 instead requires the Origin-attached receipt itself complete.
candidate_receiver.rs:3980–4020 checks pending attachment plus a separate clone;
:1896–1945 requires pointer-identical attached completed evidence for Internal.
The producer completion vector is not that attached pointer.

`NonCompletionFields` enumerates every unchanged R57 non-bit field: state,
originIndex, createdSeed, selectedRelation, cause, slot, taskLower, taskUpper,
incoming and replay. `completeClone` updates only completed. Native Rust also
has drain_index and a replay-ack payload that R57 does not represent; native
task/cause branding and pointer identity are not authenticated by this model.
There is no claim that these omitted payload equations were proved. Endpoint
constructors, arbitrary source/term types, incoming/replay values, every Origin,
relation competitor and every retained list index remain available.

## Constructed theorem surface and exact hypotheses

Every following name has prefix `YulangClosure.NativeReceiptJoinR86.`.
Exact source signatures/proof terms are in the frozen candidate; **printed
types and all 36 axiom lists are NOT_RUN**. Definitions/structures, including
IndexedJoin and WindowJoin, are not presented as proved concrete instances.

`IndexedJoin n cs occurrence lower upper` contains two original indexed reads,
the exact attached-pending equation, checked Guards, completed-clone equality,
and full-inventory singleton equations. `WindowJoin n cs w ...` retains the
same original physical lists/indices, validates all four cuts, and uses only
cut-local singleton equations. Neither is assumed equivalent to Root.

| Theorem names | Inputs and conclusion |
| --- | --- |
| `completeClone_fields` | Every receipt p has all ten non-bit fields equal to completeClone p |
| `fields_and_completed_determine_clone` | For arbitrary p,c, NonCompletionFields p c and c.completed=true imply c=completeClone p |
| `singletonIndex_empty`, `singletonIndex_multiple` | Empty list or any i::j::rest computes none, even i=j |
| `singletonIndex_unique` | Two exact singleton equations on the same index list imply equality of selected indices |
| `completionIndices_single_clone`, `completionIndices_duplicate_clone` | Singleton clone computes [0]; duplicate identical clones compute [0,1] |
| `completion_index_read` | Membership of index in the computed completion candidates implies cs[index]?=some (completeClone p) |
| `completion_index_unique` | A computed singleton candidate equation plus candidate membership implies the selected index equality |
| `readJoin_missing_origin`, `readJoin_ambiguous_origin` | Computed empty or ≥2 Origin index candidates imply readJoin=none |
| `readJoin_missing_attachment` | Singleton Origin equation, exact indexed Origin read and drain=none imply rejection |
| `readJoin_missing_completion`, `readJoin_ambiguous_completion` | Singleton Origin equation, indexed read and attachment, plus empty/≥2 matching completion indices, imply rejection |
| `readJoin_bad_guards` | Both singleton/indexed reads and attachment, plus negated explicit Guards, imply rejection |
| `readJoin_accepts` | Both computed singleton equations, exact Origin/attachment/completed-clone indexed reads and Guards imply readJoin.isSome=true |
| `joined_fields`, `joined_flags` | Any IndexedJoin supplies ten non-bit field equalities and pending=false/completion=true |
| `joined_records_distinct`, `joined_completion_not_attached` | The two joined receipts differ; the completion is not attached to that retained Origin |
| `joined_replacement_not_at_origin_index` | Original n.origins[j.originIndex]? cannot equal the same Origin updated with the completed attachment |
| `joined_R57_rootDrain`, `joined_R57_completed_false` | Given the distinct, explicit R57 originRead n j.origin.relation=some j.origin equation, rootDrain reads pending and R57 completed=false |
| `joined_origin_blocks_R84_primitive` | Any IndexedJoin and arbitrary original source/inventory/request/incidence/index/Records d with d.origin=j.origin imply ¬R84.Primitive on the unchanged n |
| `reachable_join_still_blocks_R84` | For every R85 Reachable base p and any join, every unchanged R84 Primitive on p.native is blocked via the existing R85 theorem |
| `readJoinInCuts_invalid` | Negated exact ValidCuts rejects |
| `readJoinInCuts_ambiguous_origin`, `readJoinInCuts_ambiguous_completion` | ≥2 matching indices in the corresponding checked window reject, with exact indexed Origin/attachment equations for the latter |
| `readJoinInCuts_accepts` | ValidCuts, both cut-local singleton equations, original indexed reads/attachment, completed clone and Guards imply isSome=true |
| `window_join_fields` | Any WindowJoin supplies all ten non-bit equalities |
| `window_origin_index_unique`, `window_completion_index_unique` | Candidate membership within that same window implies equality to its selected index |
| `window_join_completion_not_attached` | A window completion is not attached to its retained Origin |
| `window_origin_blocks_R84_primitive` | Any WindowJoin and original Records d with d.origin=j.origin imply ¬R84.Primitive on the same n |
| `origin_competitor_retained_in_cuts`, `completion_competitor_retained_in_cuts` | Every full candidate index inside the explicit respective window remains a window candidate |

Guards checks occurrence, origin index, created/selected relation identity,
cause occurrence, cause slot, task endpoints and pending=false. No incoming
or replay value is discarded or required to be none: complete-clone equality
preserves them. These are finite checked data equations, not Root, source
exhaustiveness, relation-ID uniqueness or a typing definition. The uncut
pending reader corresponds to the full-window case of the in-cuts shape;
it is not claimed identical to checked_source_drain's acceptance of other
attached-bit values. Arbitrary cut-window checking is separately represented.

## Parent application and first remaining premise

The first failed same-record equation is R84's
`d.origin.drain = some d.drain` together with `d.drain.completed = true`.
On the actual joined Origin, its attachment is pending with completed=false;
Option injection identifies d.drain with that pending record. Using the
completion instead violates the attachment equation. Updating the Origin
violates the original indexed read, proved separately; no claim is made that
an equal replacement cannot occur elsewhere as a competing Origin.

Thus neither the full-inventory nor cut-window join supplies unchanged R84
Primitive for that Origin. The global Reachable consequence also retains the
entire Native and every arbitrary R84 Records. This is a concrete interface
obstruction, not a refutation of original A/B or a proof that every possible
R66 Root is impossible.

Cut-local occurrence/pair uniqueness does not establish full occurrence/route
uniqueness, and neither establishes R57 state/relation-ID uniqueness. The R57
theorems deliberately expose the latter exact read equation as an additional
conditional premise instead of inventing a global uniqueness law.

First remaining owner/premise: Luna must adjudicate the incompatible native
Internal attached-completion requirement and pending/cloned producer interface.
Any changed consumer needs separate semantic/implementation authority. Native
payload encoding, source transition exhaustiveness, window capture authenticity,
saved-projection pointer ownership, and the distinct selector bridges remain
with primary/source owners. No completion projection is relabeled as Root.

## Proposed exact in-memory audit recipe — NOT EXECUTED

Use the accepted R85 slot-2 stdin exactly: 115,884 bytes,
`bac29ad18bd16e9a5af0422ea4d3416e049a61951d6b1545c8ba35a0548cbc79`.
Its R84 prefix and original/normalized slice hashes were freshly reconstructed
using the first JSON fence of the admitted R84 handoff (339,182 bytes,
`8241f3b7ab3a656c15d114a987159fd33c66f04ae48fc3d82dbda0e4972ed17b`).
The recipe is the unchanged one in the R85 proof handoff: normalize/assemble
the R84 JSON module slices, append stripped current R84 and full_queries,
append newline plus stripped current R85 and its first Lean query fence plus
one trailing newline. Reconstruction matched accepted R84 stdin (103,470 bytes,
`93b365ddf908e223558d166efe7f76a1f5c370a5b1c9080716d0fb0ce92b3df0`) and R85 exactly.

With UTF-8 strings and no newline normalization, append precisely:

```python
strip = lambda s: "\n".join(line for line in s.split("\n")
                            if not line.startswith("import "))
names = re.findall(r"^theorem (\w+)", candidate, re.M)
queries = ("set_option pp.universes true\n"
           "set_option pp.explicit true\n"
           "set_option pp.fullNames true\n")
queries += "".join(
    "#check @YulangClosure.NativeReceiptJoinR86." + name + "\n"
    "#print axioms YulangClosure.NativeReceiptJoinR86." + name + "\n"
    for name in names)
stdin = accepted_R85_slot2_stdin + "\n" + strip(candidate) + "\n" + queries
```

There are exactly 36 names, in frozen candidate source order. Queries: 5,360
bytes, SHA `cdc414fa5196c857de714c425120370b3b15c5f432e1d1c3259ba2d893179995`.
Exact proposed R86 stdin: **145,333 bytes**, SHA-256
`8cddd5e4c4c1fe27469cc488c6e8522213a6275a598adba2b3b1332959ba10c8`.
Every one of the R84/R85 query pairs is retained. Hashing/assembly used only
Python memory; no stdin/scratch/log file was created.

Primary owns fresh review and the separately committed/pushed audit gate.
Proposed executable, not run by leaf:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`,
cwd notes/theory/lean, LEAN_NUM_THREADS=1, timeout ≤120 seconds. Rehash executable
and all dependencies before use. Pin read from lean-toolchain is v4.35.0;
actual executable version, process exit and axiom reports for R86 are NOT_RUN.
The bundled checker is unavailable under this no-build/no-cache/no-scratch
packet, rather than replaced by a weaker acceptance claim. Standalone module
imports are not audited by flattened stdin.

## Evidence, resources and stop

Actual commands: read-only pwd/cat/sed/rg; Python standard-library JSON/slice
parsing and SHA-256 reconstruction; clock lookup; apply_patch solely on the
two leases. All hash/reconstruction assertions exited 0. A read-only candidate
scan found no sorry/admit/project-axiom/native_decide/debug.skipKernelTC token;
this is not a transitive axiom audit. No Lean diagnostic exists because no
Lean invocation was attempted. No invented runtime/model/checker receipt.

Primary audit calls consumed by leaf: **0/2**. No descendants, nested CLI,
Git mutation, compiler/build/test/formatter invocation, generated output or
environment change. CPU/RSS were not measured. Finite leaf budget: 1,400
seconds, no renewal; wall time is below that bound but not independently
profiled. Exact observed model/effort is UNKNOWN to the leaf.

**STOPPED / WRITES STOPPED** immediately after this revision-1 handoff. Candidate
bytes are frozen; further work requires primary intake/reopening. No running
process or generated/scratch-output lease remains. Per primary request, no
further construction is performed after freeze.
