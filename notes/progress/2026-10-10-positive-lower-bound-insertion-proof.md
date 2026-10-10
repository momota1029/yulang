# Positive Effect lower insertion and the shared-Allowance source premise

Date: 2026-10-10
Status: independently reviewed bounded source characterization; conditional source bridge; R remains open
Assigned baseline: `ddbb588d27de14bd31702ad4a3b18c5309e76bcd`
Producer: `/root/proof_bridge`, actual role `prover`; no descendants
Exclusive lease: this note only

## Objective, authority, and frozen statement

Derive the exact direct insertion behavior of `candidate_apply_effect(b,C)`
and identify the additional source premise needed to put its positive lower
on the shared incoming-Allowance owner before restoration saves its opposite
count. This is static branch analysis of actual constructors and consumers,
not an executable probe, proposed invariant, independently established theorem,
or complete proof of the restoration gate.

Authority: contextual attachment/admission design §§3.1, 4, 5. Attachment
identity, resolved member identity, provider identity, residual lineage and
shared contextual inputs remain distinct. No annotation rule, ordinary
inference behavior, restriction, Call meaning or cutover decision changes.

Quantify over every direct invocation in a valid candidate session with the
feature and graph present, allocated endpoint indices and well formed row
representative forests, no external interleaving, and successful operations
through the boundaries explicitly stated below. Let `c` be entry-state
`canonical_effect`, `l=c(b)`, `u=c(C)`, and `L(i)=effect_levels[i]`. The raw
symbols b and C are fixed invocation arguments; neither is assumed to be a
row or a particular parent/copy coordinate. Let `E(x)` mean
`ExtrusionEndpoint::Effect(x)` and `K=BoundKey(E(u),Positive,E(l))`.

The conclusion concerns the direct append owned by this invocation, before
draining enqueued work, rather than every later insertion caused transitively
by it. A physical bound-vector occurrence, a contextual fiber entry, and an
origin entry are separate stored objects. Presence of one does not prove new
insertion of another. Source reachability is an additional quantified premise,
not supplied by the valid-session hypothesis.

Exclusions: API-injected setups as source witnesses, arbitrary ordinary-source
reachability, all-runtime/full-R coverage, solver acceptance, activation or
complete replay merely from storage, effect hygiene closure, complete Call,
soundness/principality closure, tests/builds and probes.

## Exact orientation and physical append

For every successful direct invocation, a newly appended physical positive
lower occurrence with key K exists **if and only if**

```text
u = EffectRow(r), l != u, and
  (l is not an EffectRow
   or (l = EffectRow(a) and L(a) < L(r))).                 (P)
```

Here K's owner and row item are canonical, not the literal raw arguments.
If P holds, exactly one direct positive vector occurrence is appended:
`a` to `effect_bounds[r].direct_lower_rows` for a row lower; otherwise `l`
to `effect_bounds[r].exact_non_variable_lowers`. The statement does not require
the vector to have lacked that item beforehand.

Exhaustive derivation from `candidate_extrusion.rs:726–750`:

| Canonical arguments | Direct result |
| --- | --- |
| `l == u` | Return; no insertion |
| `l=EffectRow(a)`, `u=EffectRow(r)`, `L(r)<=L(a)` | Negative bound owned by a; no positive lower owned by r |
| `l=EffectRow(a)`, `u=EffectRow(r)`, `L(a)<L(r)` | Positive lower a owned by r |
| non-row l, `u=EffectRow(r)` | Positive exact lower l owned by r |
| `l=EffectRow(a)`, non-row u | Negative exact upper u owned by a |
| unequal non-row l and u | Operand check; no direct vector insertion |

These cases partition the endpoint enum (`lib.rs:755–769`); non-row includes
Bottom, Empty, Contribution, Allowance, Support and AnnotationMember. The
formula describes mechanically valid direct calls, not whether every such
non-row pairing is emitted by ordinary inference or is semantically accepted.

`canonical_effect` renames only EffectRow through `effect_rep`
(`lib.rs:11334–11339`, `candidate_intrusion.rs:65–78`). Non-row view/member
IDs are unchanged. Equality and levels are therefore tested after row alias
resolution. Comparing raw IDs or pre-alias levels can predict the wrong side.
`canonical_extrusion` applies the same canonicalization (`:165–170`).

The selected helper canonicalizes owner/item, retains the bound origin/context,
journals the canonical effect owner and unconditionally pushes the item into
the chosen vector (`candidate_extrusion.rs:393–425, 480–523`). There is no
`contains` check in its insertion macro. Context/origin deduplication can
return successfully without adding evidence and still allow this vector push.
Capture registration for a positive bound returns without adding negative
Allowance incidence (`candidate_effect.rs:426–435`). No representative mutation
occurs in this insertion prefix. Opposite replay then enqueues comparisons;
it does not synchronously drain them (`candidate_extrusion.rs:646–690`).

For invocations returning an availability error, P remains necessary for the
direct positive push, and the exact additional condition is that execution
reaches that push: context/origin retention, row journaling, reservation and
capacity accounting must all complete beforehand. An error after the push
does not undo it within `candidate_apply_effect`; an owning route rollback
may later remove it. Consequently `Ok` is a sufficient success envelope for
the iff above, not a necessary condition for a transient physical append.

The unequal non-row branch can enqueue future comparisons through Support
members/tail or an Allowance tail (`candidate_effect.rs:753–826`). This is
not a counterexample to P: those later comparisons have their own invocations
and canonical owners. No indirect drain is included in the direct claim.

## Physical contextual fiber and duplicate suppression

For P and a successful insertion prefix, let R be the exact child relation
constructed by `candidate_context_bound` for K, using the selected origin,
matching retained parent if available, and its post-check context
(`candidate_effect.rs:327–368`, `candidate_context.rs:1870–1911`). Then a
new physical contextual fiber item `(K,R,previous)` is appended if and only
if R is absent from K's linked fiber immediately before `State::attach`.
`attach` scans the complete fiber for that relation and otherwise appends
(`candidate_context.rs:1546–1559`). K alone does not determine R: distinct
contexts/origins can construct distinct relations; equal interned child R can
still acquire additional dependency lineage without another fiber item.

Thus P selects positive insertion intent and, on success, the physical vector
append. P alone does not imply a newly appended contextual fiber. Conversely,
context evidence can be appended before a later reservation error prevents
the vector push. These are different observable boundaries.

The ordinary worklist adds another suppression boundary before direct calls:
context execution precedes memo handling; `pair_is_current` requires the raw
typed pair plus completion of the processing relation at the current equality
generation (`lib.rs:11353–11363,11859–11877`). A duplicate is not applied.
`apply_effect_task` selects the candidate helper only with a candidate graph
(`lib.rs:11576–11585`). Context execution's other direct caller supplies an
Allowance upper, so its direct invocation selects a negative row upper or
an operand check, never P. For an already registered Allowance it retains
origin and replays instead of calling the helper
(`candidate_context.rs:1807–1863`). Enqueueing a pair or retaining a relation
therefore does not establish that the positive insertion call occurred.

## Snapshot ordering and the precise ordinary-source bridge

Negative restoration first inserts its upper, canonicalizes its owner/item,
then reads `candidate_opposite_count(owner,Negative)` exactly once
(`candidate_extrusion.rs:599–616`). That count is the direct-lower length plus
exact-lower length (`:534–556`), independently of fiber counts. Inserting the
negative Allowance does not create a positive lower. A positive occurrence
on the same canonical owner must already survive at this snapshot to make
the count nonzero. Later positive insertions cannot change the saved count;
subsequent live-vector reads and canonicalization remain separate obligations.

The real normal capture/restoration seam is present: expansion of a local
Effect tail captures its incoming negative Allowance incidences
(`candidate_scheme.rs:488–500`), including an older/shared source owner;
freshening transports each captured relation and restores its recorded side
(`:998–1032`). `Action::Local` calls `route_candidate_local`
(`candidate_source.rs:543–573`), which captures/freshens transactionally and
only afterward admits the lookup's Value link (`candidate_scheme.rs:1117–1135`).
That later link cannot furnish an earlier snapshot lower retroactively.

The extra premise, still unproved, is an **actual admitted ordinary HIR
schedule prefix** containing a popped Effect comparison `(b,C)` whose direct
candidate application satisfies P and completes its push, with that positive
occurrence retained on the same canonical owner as the incoming negative
Allowance at its restoration snapshot. The prefix must establish:

1. The true HIR producer, original occurrence/cause and lexical/annotation
   scopes emit the comparison under current approved inference; endpoint
   existence, parent provenance or an injected call is insufficient.
2. Admission actually reaches application after contextual consumption and
   the relation/generation memo test, before the target restoration snapshot.
3. The canonical owner/item at application are those carried to that snapshot;
   if representatives change, actual merge/transport must preserve the lower
   on the snapshot owner. No rollback removes it.
4. For the row alternative, at application `c(b)=EffectRow(a)` and
   `c(C)=EffectRow(r)`, with strict `L(a)<L(r)`; equal representative levels
   select the opposite owner/side.
   For the non-row alternative, an authentic positive operand producer must
   reach C, rather than merely appearing in an Allowance's allowed set.

This is the required bridge for the helper route. Other authentic constructors
(restoration, extrusion copying or qualifying merge) can append a lower
without satisfying P for a contemporaneous ordinary comparison; they require
their own producer/timing bridge. No global necessary source restriction is
inferred from this helper's orientation.

The reviewed shared-Allowance fixture note establishes an authentic shared C1
but records no positive C1 lower at its snapshot. Its copy constructor instead
inserts `I3 + C1`; its propagated comparisons place C1 on younger owners or
give C1 negative uppers. The current characterization explains that failure
without inventing another source program. It neither proves nonreachability
of another prefix nor establishes the later qualifying SCC, exact omission,
and failed replay/diagnostic rescues required for R.

## Stopping point and obligation economy

One direct exhaustive branch derivation was performed; no equivalent probe or
third proof variant was launched. The reduced obstruction is source production
and timing of the surviving lower, not arithmetic, fiber enumeration or another
classification of R. The direct orientation lemma is established within its
stated operational hypotheses; the ordinary-source bridge remains conditional.

The requested existence of a witness prefix is research characterization (C)
until it demonstrates a safety/natural-inference defect; restoration correctness
itself remains required A/B under the governing contract. If repeated source
attempts leave the same premise untouched, inspect the owning HIR comparison
constructor and scheduler before adding reconstruction relations. There is no
evidence here of a discarded fact warranting new metadata, semantic restriction
or changed gate status. This economy audit does not retire or close R.

Next action: primary assigns a bounded source correspondence packet naming one
actual HIR comparison producer and a schedule prefix satisfying items 1–4,
then independently reviews this frozen characterization. No new leaf is launched
by this producer.

## Checks, resources, dependencies, and commit packet

Checks actually performed: bounded `cat`, `sed`, `rg` source/rule/skill reads
and `sha256sum`; static exhaustive branch inspection. The prover ran no Git
command, probe, test, build, measurement, descendant or shared-file write.
The primary separately verified baseline blobs and assigned one reviewer.
Zero heavyweight
processes and zero executable samples; CPU/RAM totals unmeasured. Assignment
budget: at most ten minutes, static shell processes only. Requested ordinary
Sol/high routing; model/effort runtime metadata unavailable, observed unknown.
Role TOML has no model/effort pins; config declares Sol/high subagent defaults.
No Astra assignment or runtime override is claimed.

The assigned baseline is a label supplied by the primary. The producer did not
perform Git/blob reads. During integration, the primary compared every listed
source/design dependency hash with the exact baseline blobs; all matched. No
dependency was changed by this producer.

| Inspected dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| governing contextual attachment design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| prior shared-Allowance restoration trace | `7b8d31ebd4435dd021964b9ea5d2e9b74c463caa0e18edc436e4ce5d32341750` |

- Exact lease/changed path: `notes/progress/2026-10-10-positive-lower-bound-insertion-proof.md`.
- Baseline: `ddbb588d27de14bd31702ad4a3b18c5309e76bcd`.
- Changed dependency hashes: none; every listed hash matches its exact baseline blob.
- Review: independent `compiler_referee` found no blocking or major issue and
  one minor precision issue in the row-level premise. The primary corrected it
  to name canonical representatives; no semantic claim changed. Source
  reachability, restoration completeness and R remain open.
- Already run: static reads, branch derivation, exact baseline blob-hash
  comparison, independent review, and `git diff --check`; no executable check.
- Proposed checkpoint: `research: derive positive effect lower insertion conditions`.
- Shared-record deltas for primary/curator: record P and the distinct physical
  vector/fiber/memo boundaries; retain the source-prefix survival/timing premise
  and R as open. No shared record was edited.
