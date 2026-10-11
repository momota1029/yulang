# Oracle direct return: source inputs to simplification

Date: 2026-10-12
Status: frozen producer source audit; independent review pending; S and H OPEN
Claim class: bounded source characterization and conditional nondeletion facts
Y3 baseline: `52f44a1a2bfe9a39c6780b76b8098795b70ace9e`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this file only; no delegation or Git mutation

## Objective and fixed input boundary

Audit the P→S seam for `my direct(cb: (() -> [tick] ())) = cb`.
The primary accepts reviewed P from
[the projection derivation](../theory/2026-10-12-oracle-direct-return-projection-proof.md):
normal completed native construction/replay admits A's positive callback
Function at the actual returned Y coordinate, and scheme collection visits its
result-Effect stack. P's fresh source slice and completion hypotheses remain
exactly its own. This audit does not reopen projection or strengthen P into a
complete compact-root claim.

Use x for the annotation Effect coordinate and α for its fresh SubtractId.
The family is the resolved nullary tick path, not its display spelling. α
identity, x coordinate identity and family identity are separate facts.
The original [H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md) §1
and its universal source domain remain OPEN. Authority remains annotation
effect hygiene §§1–2 and top-level inference principles §§1–5. No new source
restriction, semantics, metadata or implementation is selected.

Hypotheses of the conditional facts below: pinned bytes, ordinary completed
owner operations and fresh allocation without exhaustion. Where a compact
shape or unchanged occurrence is required, it is stated explicitly; no final
root, substitution list or equivalent-view theorem is assumed.

## Generated local ports and the limits of their completeness

Oracle citations are under `crates/infer/src/` unless marked otherwise.

The returned positive port is `Stack(Var(x), PUSH(α, Set(tick)))`, in A's
positive result Effect (`annotation/constraints.rs:363–389,424–470`). Its
paired negative callback port uses a Set(tick) filter around NegVar(x).
P supplies the actual positive A-at-Y bridge. The direct Function argument
collects c negatively, reaching the paired negative callback Function, so this
local construction supplies both composed signs of x; the enclosing Function
argument reverses the callback result's sign.

For this one formal, `lowering/expr/method_body.rs:65–84` initializes an empty
closed-row table. `annotation/constraints.rs:602–620` allocates x on the first
nonempty closed row and caches it. This local formal has one tick row; generic
closed-row reuse is not evidence that this first x was preexisting. Later
sharing still requires its owning construction, rather than α freshness.

The annotation boundary allocates/registers a stack fact, without calling
`connect_effect_row_lower` at 622–633 on this return path. Fact admission
(`constraints/machine/entry.rs:1831–1862`) updates the subtract table and events;
it does not insert a concrete tick lower into x. Comparing A with its own
negative companion generates the matching result-Effect comparison
(`machine/propagate.rs:257–262`); stack normalization at 11–55 leaves an x→x
comparison, and the equal-coordinate branch at 107–110 adds no bound. These
specific operations therefore supply no positive concrete sibling of x.

Public/erased callable upper construction at `lambda.rs:1284–1303` is separate
from the installed c upper. With no callback application, public argument
selection at 988–1038 falls back to NegVar(c), because `call_erased_used` is
false. An allocated public row or auxiliary ID is not an occurrence in direct's
actual exported return port.

These are local producer exclusions, not a census of all later x bounds.
Definition completion queues SCC work (`body/methods.rs:287–299,402–408`);
`analysis/session/lifecycle.rs:218–221` explicitly does not drain on enqueue.
Global Name uses allocate a use coordinate and queue resolution
(`lowering/name_ref.rs:94–115`). The final collector/prepass snapshot cannot be
identified with the instant this annotation or definition finished merely
because its source contains no body call.

## Merge and stack-floor discriminator

Collection enters the returned stack positively. The candidate weighted
occurrence is x with PUSH α. Negative effect compaction at
`compact/collect/type_nodes.rs:543–562` can instead construct Row(tick, tail)
and visit x in its tail with the outer weight. A concrete negative prefix is
not a positive concrete lower emitted by the annotation.

`compact/merge/entries.rs:288–306` merges Function results positively and
arguments negatively; all Function inputs at a coordinate contribute.
Same-coordinate variables at 124–141 use `parallel_union` when their weights
differ. `poly/src/types.rs:412–420,565–599` recomputes each ID entry using the
intersection of incoming floors, intersects each stack family with that floor,
and discards an Empty stack under an Empty floor.

Consequently a plain unweighted x merged with PUSH(α, Set(tick)) does **not**
supply an Empty floor for α: absence of an entry is not Empty. With no α floor
on either incoming entry, the effective floor is All and the tick stack
survives that merge. An actual intersecting Empty/incompatible floor requires
an α entry carrying it. No such source-produced α floor was established in
this audit. Conversely P does not enumerate every incoming α entry; this
single merge fact does not certify the complete merged weight.

## The negative row prefix alone cannot supply the shared Exact item

Co-occurrence collection ignores stack weights and intersects groups over
all occurrences of a variable (`analysis/occurrence/mod.rs:245–269`; paths
here are actually `compact/analysis/occurrence/...`). For a nonrecursive bare
tail T whose variables include x and whose ordinary type group has no Exact:

1. Row(tick,T) records a row group containing Var(x) and
   Exact(Con(resolved_tick_path,0)) at `occurrence/mod.rs:590–592,634–644`.
2. The same traversal normally visits T at 598, recording `along_group(T)`.
   When T is variable-only, that group contains variables and no Exact.
3. `record_group` intersects those groups. Thus the row prefix's Exact(tick)
   is removed from x's co-occurrence set, regardless of whether this was the
   first or a later occurrence. One such witness suffices for that polarity.

This distinguishes the actual row-tail traversal from treating the prefix as
permanent co-occurrence evidence. Exact(Con(tick,0)) also differs from
Exact(Row([Con(tick,0)])); `ExactKey` is an enum, and the two constructors
are generated at 637–643 and 710–720. Resolved family identity is preserved
in both keys, but key shape matters.

The condition matters: T might itself contain concrete siblings from its
collected bounds; x might be an ignored recursive center; or a subsequent
rewrite might remove the witnessing occurrence. The complete T and recursive
bounds for direct have not been recovered here. No source-qualified sandwich
deletion follows from the negative annotation prefix alone.

## Exact deletion, rewrite and fixed-point conditions

| Owner | Decisive predicate or action |
| --- | --- |
| Polar elimination, `compact/analysis/mod.rs:40–58` | A simplification candidate is mapped to None only if its current variable is not bipolar. Function polarity at `occurrence/mod.rs:120–133` preserves results and reverses arguments. Current levels/non-generic membership also matter (`analysis/mod.rs:506–512`). |
| Co-occurrence union, `occurrence/mod.rs:322–355,429–459` | Mutual same-sign co-occurrence and compatible opposite sets can replace x by another representative. Bipolarity alone does not prohibit replacement. |
| Exact sandwich flattening, `occurrence/mod.rs:359–397` | x must be a candidate and current union representative; both sign tables must share a nonself item. Sorted variable items precede Exact items. A selected Exact marks x for removal. |
| Substitution, `occurrence/substitution.rs:32–50,109–129` | Removal of a representative yields None for its union members. None deletes the entire weighted occurrence, including α; Some preserves its weight before same-target parallel union. Normalization at 256–285 follows later chains, including None. |
| Structural sandwich pass, `sandwich.rs:119–150,270–315` | Liftable kinds are Con, Tuple and Fun. A Row is ConcreteButNotLiftable; a bare variable occurrence yields NoLift. Neither a row alone nor a bare-tail witness justifies a structural lift of x. |
| Floor variable cleanup, `floor.rs:538–556,723–777` | An eligible floor variable can map to None using unipolar/deeper-birth/exact-companion or shared-Exact predicates. The negative-prefix/bare-tail exclusion also defeats that shared-Exact shortcut while the witness survives. |
| Sequencing, `analysis/mod.rs:163–202,213–243` | Collapse intervals, run polar elimination then co-occurrence repeatedly, perform structural sandwiches, then repeat polar/co-occurrence. A surviving first-pass occurrence is insufficient evidence for later passes. |

The final session first applies member simplifications and floor cleanup at
`analysis/session/generalize.rs:421–450`, then alias expansion/ordinary
simplification at 480–487, before stack cleaning. The compact inputs may also
be recomputed in its earlier prepass loop at 51–70. A table calculated from one
raw Function port is not the table of this final consumer.

## First unresolved record and stop

No source-qualified α elimination was established. The local constructors
give no Empty α floor or mandatory shared Exact. Under the explicit additional
premise that the final x views are weighted positive variable-only x and a
negative tick row with a variable-only x tail, with no relevant recursive
center/rewrite change, the prefix traversal precludes an Exact sandwich, the
two signs preclude polar None, and the bare occurrence precludes structural
lifting. This is conditional nondeletion, not S or a full fixed-point theorem.

The minimal unresolved owning artifact is **the complete x incidence slice of
the final compact root supplied to preparation**, including every collected
Function contribution to direct's returned callback result Effect, all α
entries/floors merged at the same coordinate, the negative tail containing x,
recursive-center membership and relevant recursive bounds. Its owners are
`compact_root_for_generalize:580–603`, `compact_lower_bounds_from:898–917`,
Function/variable merging, and final preparation at 421–487. A final x bound
inventory alone is insufficient if another returned Function port contributes
a differently weighted occurrence. The next missing premise is the complete
shape/weight input, before computing deletion verdicts; it is not P's
already accepted A-presence or projection decision.

Smallest discriminating evidence: that complete weighted incidence slice,
with actual levels/birth/non-generic and representative images after collapse
and each fixed-point pass. From it, compute the intersected positive/negative
AlongItem sets and actual None/Some images. Do not substitute guessed groups,
numeric IDs, surface output, family equality or a checker that assumes these
source inputs. No equivalent α observation after deletion is proved here.

Recommended next action: primary assigns the complete source-to-compact x
incidence/weight derivation to its owning construction lane and uses the
bare-tail group intersection as the concrete discriminator. Keep S and H OPEN;
do not repeat an A-presence audit or count this conditional fact as closure.

## Checks, dependencies and commit packet

Static source reads only: bounded rg/nl/sed/cat, read-only revision queries,
and Python SHA-256/pinned-byte comparisons. Twenty-five dependencies matched:
four Y3 inputs and twenty-one Oracle sources. No Oracle invocation, executable
model, test/build, instrumentation, mutation, formatter, child or Git mutation.
Seeds/ranges/samples: none. Some initial combined output was truncated; decisive
branches were reread narrowly. One obsolete session glob returned a missing
path and was replaced by the actual lifecycle owner. At most two lightweight
shell reads overlapped; CPU/RSS and elapsed time were not measured. No numeric
quota was supplied; exhausted invocation and static-only budgets were obeyed.

Oracle source is the operational reference; no independently executable oracle
ran. This lane shares the source bytes and P's accepted premises with the
constructive lane. It is a producer, not an independent reviewer. Unverified:
complete compact incidence, accumulated floor inputs, actual fixed-point images,
S, installed selection, provider/use/output lineage and H. No compiler or shared
record changed. Writes stop at handoff before frozen review.

- Exact lease: `notes/progress/2026-10-12-oracle-direct-return-simplification-audit.md`.
- Baselines: Y3 `52f44a1a2bfe9a39c6780b76b8098795b70ace9e`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency hashes changed: none. P SHA-256 `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7`; H `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1`; occurrence module `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2`; substitution `b6d04c187a870892239db84a16360f700f7efaef4c0ba7b731d1389db31f9bf2`; floor `1999be84afc43bbf7a141480c3a299d36e3913af59b19d9b4ad8d93c596dfb97`. All cited bytes match the pins.
- Review status: frozen producer source characterization; independent review pending; no S/H closure or source-qualified counterexample.
- Checks already run: focused static reads, 25 pinned-byte/hash checks, note newline/fence/whitespace and diff integrity. Zero execution/build/test.
- Proposed checkpoint message: `research: discriminate Oracle direct effect simplification inputs`.
- Shared deltas left for primary/curator: record that a tick row prefix does not supply persistent Exact co-occurrence when its x tail has a variable-only witness; absence of an α entry is not an Empty floor; retain final complete x incidence/weight and fixed-point survival as OPEN. No shared record was edited.
