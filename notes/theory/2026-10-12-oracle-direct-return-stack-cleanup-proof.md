# Oracle direct return: retained stack to installed scheme

Date: 2026-10-12
Status: independently reviewed bounded source-to-export derivation; original H OPEN
Claim class: bounded source-to-export derivation, conditional on accepted P/S
Y3 baseline: `5bb504465075f398247a3899ff31e1fcc6a4c7af`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file only; leaf; no delegation or Git mutation

## Frozen objective, inputs and statement

The primary accepts [P](2026-10-12-oracle-direct-return-projection-proof.md)
conditionally and [S](2026-10-12-oracle-direct-return-simplification-proof.md)
through both simplifier fixed points, with independent S review reporting no
issues. Those accepted dependencies, rather than their older producer-status
headers, fix this packet's starting point. The frozen
[simplification audit](../progress/2026-10-12-oracle-direct-return-simplification-audit.md)
is supporting source evidence. Authority is annotation-effect-hygiene-integration
§§1–2 and top-level-inference-principles §§1–5. No new semantics are selected.

**K.** For every normally completed construction and first scheme export of
the same fresh ordinary module declaration
`my direct(cb: (() -> [tick] ())) = cb` in P/S's constructor slice, before
incoming external uses constrain it, let x and α be its original callback
result-Effect coordinate and annotation SubtractId. Starting at S's actual
simplifier return, the positive returned callback result-Effect occurrence
retains exactly x with weight Pα through stack preparation, selection and
ordinary finalization. The installed scheme quantifies x and α and contains
`Pos::Stack { inner: Pos::Var(x), weight: Pα }` at that same returned callback
result-Effect port. The paired negative callback result-Effect remains
`Neg::Row([Con(resolved_tick_path, [])], Neg::Var(x))`. Here Pα has filter All,
one entry `(α, pops=0, floor=[], stack=[Set(resolved_tick_path, [])])`.

The hypotheses are P/S's successful ordinary annotation/name resolution,
fresh allocation without ID exhaustion, and normal completed native
admission/replay/query and scheme operations. The displayed single formal,
bare local Name body, absent result annotation, absent self application/impl
requirements and absence of incoming external uses are the unchanged bounded
source slice. Its original module scope and formal binder are retained; this
is not a theorem about arbitrary containing scopes or programs.

K proves literal export of this component, rather than an assumed equivalent
view. It asserts membership of x and α in the scheme's two binder lists; it
does not require a complete printed scheme or numeric-ID census. The machine's
registered subtract fact and the scheme's stack entry are separate objects.
No invocation, actual dump, provider choice, downstream activation or fresh-use
renaming is supplied as a premise.

Original [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 retains all
source-program, composed-negative occurrence, original scope/binder, actual
copy/instantiation and actual call/output-route quantifiers, correlated lineage,
independent same-family contributions, retained current/future checks and safe
nonpublication requirements. K does not close H, complete Call, soundness,
principality, or a source-qualified pure-output counterexample.

## 1. Actual prepared root, level and quantification boundary

Oracle citations are relative to `crates/infer/src/` unless marked otherwise.
S supplies the complete x incidence: one positive x/Pα in the returned
callback's result Effect, one unweighted negative x in its tick Row tail,
no recursive centers/bounds, roles or invariant intervals involving x, and
no substitution or sandwich changing x. Each witness refers to that same
original x and α. Weight liveness below is evaluated on these actual locations.

The actual session calls `prepare_alias_expanded_compact_root_with_role_variances`
at `analysis/session/generalize.rs:480–487`, with simplification boundary
root.child and empty non_generic. S covers its returned compact root and both
fixed points. The intervening post-alias dominance lane at 492–512 emits no
constraint for this interval-free root. Stack preparation at 513–518 and final
selection at 544–549 each receive empty non_generic; there is no captured local
scheme to insert an exclusion for x.

The quantification boundary is a different owner. The outer lambda constructor
returns `Computation::value` at `lowering/expr/lambda.rs:954–975`, even though
its body refers to cb. `typing.rs:42–44` sets Evaluation::Value.
`lowering/body/methods.rs:287–298,329–344` passes that computation unchanged
to the commit owner at 387–392, which records FetchValue from its evaluation;
`analysis/session/lifecycle.rs:1062–1064` writes the fetch map before enqueuing
its SCC event. `analysis/session/generalize.rs:767–776` reads that map before
the SCC fallback. `typing.rs:85–103` therefore gives quantification boundary
root (depth 0), rather than the computation boundary root.child.

x's *current* level follows from the source closure, not merely its birth.
`lowering/body/mod.rs:2282–2284` enters the definition child level and creates
public R there. x is then freshly allocated by
`annotation/constraints.rs:602–620`; `arena.rs:34–37,57–60` registers it at
that current level d, with d at least root.child. S's c/Y/O and annotation
closure has every target carrying x at this definition level; its additional
body-child pure Effect contains no x. Lower-bound insertion extrudes to the
target level (`constraints/machine/bounds.rs:645`); upper insertion uses the
source level (830). Extrusion visits nested Function/Stack children (4555–4564,
4595,4612–4621,4646), but `extrude_type_var` returns immediately when x's
level is already at most d (4701–4708). The exported V→R connection also
targets d. Thus no operation in S's closed slice lowers x below d. This proves
`level_of(x)=d>root`; for fresh module lowering from the new arena's root,
d is exactly depth 1. Restoring the arena's current level at
`lowering/body/mod.rs:2365` does not change registered variable levels.

S's compact simplification does not introduce an interval or an alternative x
representative. The interval-free post-alias/post-cleanup lanes add no later
extrusion. `collect_root_free_vars`/`collect_type_free_vars`
(`generalize/core/free_vars.rs:3–8,82–88`) visit the two x occurrences.
`generalize/mod.rs:900–915` selects variables whose current level exceeds the
quantification boundary and which are absent from non_generic. Therefore
**x belongs to the quantifier list at both censuses**. This establishes the
premise missing from the shortcut “retained stack implies quantified stack.”

## 2. Registered fact and stack preparation

The annotation constructor calls `register_stack_facts` at
`annotation/constraints.rs:458–459,593–599`. Its actual declared fact is
`(effect=x, id=α, subtractability=Set(resolved_tick_path, []))`.
`constraints/machine/entry.rs:915–943` records declaration provenance and
enqueues/drains SubtractFact work. The dispatch and recording at 1825–1861
insert it in SubtractTable; `constraints/mod.rs:3427–3464` stores the semantic
fact and an active record. S's normally completed source path therefore gives
the actual fact, rather than assuming registration from a weight alone.

`generalize/mod.rs:805–834` invokes three operations in sequence:

| Operation | Actual decision at x/α |
| --- | --- |
| Unreachable recursive-bound pruning, 815 and 827 | No recursive bounds in S's input; no x occurrence removed. |
| Quantified subtract pruning, 817–826 | x is quantified; its declared fact supplies candidate (x,α). The positive Pα occurrence makes α a live stack ID. |
| Stack cleanup, 828 | α occurs in a covariant location with a nonempty stack; α is not dead. |

For the middle row, `generalize/core/prune.rs:3–36,47–50` reads facts of the
actual quantified variable and restricts candidates to declared IDs. S has no
x-changing substitution from which a distinct fact needs transporting.
`live_subtracts` itself gives no live pair (x,α): its positive test requires
an occurrence *without* α (`prune.rs:358–388`), whereas the sole positive
occurrence carries α. This absence does **not** imply deletion.

The independent guard `live_covariant_stack_ids_in_root_and_roles`
(`generalize/core/stack_ids.rs:3–20,72–99`) starts positively, preserves
Function results and reverses arguments. It reaches the returned callback
result Effect positively and the argument callback result Effect negatively.
`stack_entry_keeps_stack_id_live` at 176–180 tests `!entry.stack.is_empty()`.
The actual `[Set(tick,[])]` entry passes. Hence α is in live_stack_ids, and
`prune.rs:68–74` excludes it from dead_ids regardless of live_subtracts.
The empty non_generic and the fact's Set rather than All are not additional
reasons for retention; the positive live stack is the decisive guard.

Stack cleanup (`prune.rs:605–620`) again removes only all IDs absent from this
positive live set, except declared All IDs. It therefore preserves α/Pα.
Both pruning owners have shared immutable machine access and mutate only
compact weights/structure; neither deletes or transforms the registered fact.
The post-cleanup dominance lane (`session/generalize.rs:523–542`) is again
inactive because this root has no intervals. The prepared image is literally
the same x/Pα and negative x/tick tail.

## 3. Stack-ID selection and final scheme normalization

At `generalize/mod.rs:188`, the plain-negative cleanup can see negative x,
but its positive-entry predicate (`prune.rs:688–727`) rejects Pα: Set(tick)
is not Empty, floor is empty rather than a singleton spent-residual floor,
and pops is 0 rather than u32::MAX. Thus plain negative x supplies no deletion.

The repeated variable census at 189–196 still quantifies x. Stack selection
at 197–198 delegates to `stack_ids.rs:23–49,78–86`, now with the quantifier
set as its variable filter. Both necessary predicates hold: x is quantified
and its positive entry has a nonempty stack. Consequently **α belongs to
stack_quantifiers**. The declared-All extension at `generalize/mod.rs:199–204,
867–887` contributes nothing for α, whose registered fact is Set(tick).
Every α occurrence is accounted for by the selected ID; α is absent from the
stray-ID difference at 207–211. The branch at 212–232 cannot remove α. Other
variable aliases, if represented before S's simplification, do not enter this
Effect coordinate or its selection argument.

The actual export owner is `analysis/session/instantiate.rs:51–82`:
it stores the generalized root in `self.schemes`, obtains ancestors, captures
witnesses, finalizes and writes `Def::Let.scheme`. These are distinct owners;
storing the compact scheme alone is not export.

For this module declaration, registration places its fresh Def::Let in the
module's children (`module_map/mod.rs:300–308,497–522`;
`module_map/finish.rs:231–235`). Its enclosing definitions are modules, not
enclosing value binders. The parent map is constructed from actual children
at `analysis/mod.rs:751–763`; `session/generalize.rs:940–955` filters the
ancestor chain through `self.schemes`. The ordinary quantify operation stores
value definitions, and modules supply no generalized ancestor here. Therefore
the ancestor list is empty, and the loop in
`generalize/simplification.rs:3–14` performs no rewrite. This conclusion is
specific to the original module declaration; it is not an assumption that
arbitrary nested definitions have no ancestor simplifications.

`generalize/mod.rs:837–865` repeats recursive pruning, dead-quantifier
pruning, stack cleanup, empty-entry cleanup and stack selection. The same
actual incidences prove every decision again: x remains free, α remains live
on quantified positive x, and the entry passes none of the removal predicates.
The final unquantified-weight pruner (`prune.rs:165–189`) has no stray α.
No equivalence theorem is needed to replace a deleted port.

`generalize/finalize.rs:3–26,179–187,328–349` clones compact stack weights into
the poly type arena while retaining x and α identities. The nullary resolved
Set has no type argument requiring renaming; zero pops contributes no entry
and composing the sole PUSH recreates Pα (`crates/poly/src/types.rs:350–353,
402–405,523–543`). Structural finalization visits the enclosing positive
Function, its returned positive callback and its result Effect
(`compact/finalize.rs:136–169,415–425,542–548`). That Effect has only x/Pα,
so it does not enter a rowish conversion. `finalize_pos_var` at 586–592 emits
Pos::Var(x), then Pos::Stack with its nonempty weight. Principal normalization
at 837–839 only sets the filter to All, which Pα already has
(`crates/poly/src/types.rs:326–329`); no floor, pop, stack item or ID changes.
The negative companion follows 428–438,560–578,604–610,692–696 to the tick Row
and its unweighted Neg::Var(x) tail. Binder lists are copied directly into
Scheme by `generalize/finalize.rs:19–24`. `set_def_scheme`
(`session/generalize.rs:958–963`) installs exactly that finalized scheme.

The Scheme has no standalone subtract-fact field. The machine fact remains
registered; the exported representation consists of quantified α and its
Set(tick) stack entry on quantified x. This is exact preservation of the
inspected representation, not proof that every future consumer activates that
fact or implements hygienic subtraction.

## 4. Cache boundary and lemma-to-parent mapping

The input compact cache (`analysis/mod.rs:311–314,334–379` and
`session/generalize.rs:580–603`) keys by public root and constraint epoch and
stores/clones the actual compact root and merge constraints. Its shadow only
records hit observations. This packet starts with S's *returned prepared
root*, so it does not infer that root from a cache hit. No cache supplies
quantification: subsequent censuses read actual current levels and registered
facts. Declaration/fact insertion bumps the semantic epoch
(`machine/entry.rs:927–928,1849–1851`). General cache validity for arbitrary
later mutation is not imported as a theorem.

The parent-map cache (`analysis/mod.rs:430–444`) refreshes on definition count,
not on a generalized-scheme hash. In this fresh ordinary source slice the
registered module topology is fixed before first export; there is no
same-count reparenting or AST replacement. A refreshed map, or reuse of the
same immutable topology, gives the module-only ancestors derived above.
The `self.schemes` store at `instantiate.rs:51–52` supplies ancestor roots;
it does not replace the local compact root being finalized. Witness capture
(`generalize/provenance.rs:23–79`) queries projection and returns witness
drafts with incomplete whole-scheme provenance; it does not rewrite the
scheme. K asserts no improvement in that witness completeness.

| Parent seam | K's contribution | Residual obligation |
| --- | --- | --- |
| Accepted P → S | Shared same x/α input; unchanged | Already supplied by accepted P/S; not reproved here. |
| S → ordinary installed scheme | Literal x/Pα and paired negative tick/x survive; x and α quantified | Bounded derivation independently reviewed; H remains OPEN. |
| Installed scheme → fresh use/provider/call/output | No conclusion | Trace actual fresh renaming, binder/provider and complete output consumer. |
| Universal H | No status change | Original contexts, incoming uses, correlated contribution lineage, checks and independent same-family preservation remain OPEN. |
| Compiled cache interface or later whole-program export | No conclusion | Separate normalization/consumer owners, including cache-interface joint simplification, have not been proved by ordinary Def::Let installation. |

All predicates needed for K were obtained at their source/consumer owners;
there is no first missing local owner to disguise as a new hypothesis. Incoming
external constraints may change levels, incidence and consumer schedules; the
first premise for those broader cases is their actual scheme-consumer state,
not another proof of S's retained stack. The economy rule does not authorize
reclassifying H or imposing source restrictions. This packet makes a single
source-directed advance past the prior S boundary and stops there.

## Independent review

An independent `compiler_referee` reviewed this frozen derivation and found no
BLOCKING, major, or minor findings within K's declared conditional scope. The
review checked the actual level/FetchValue boundary, pruning predicates,
quantified positive-stack selection, module ancestor path and installed-scheme
finalization. It checked the nine listed core dependency hashes. It did not
reproduce P/S's 29-file pin comparison or extend K to arbitrary contexts,
fresh-use discharge, actual Call/output, compiled-cache normalization, H,
soundness or principality. Those remain OPEN.

## Checks, resources and commit packet

Completed checks: bounded rg/nl/sed/cat source reads; read-only HEAD queries;
Python SHA-256 and `git show <pin>:<path>` equality for five frozen Y3 inputs
and 24 Oracle files (29/29 matched); leased Markdown newline/fence/whitespace
and link integrity. Initial combined captures were truncated and decisive
owners were reread narrowly. A few guessed source paths were absent and were
replaced with the located owners. These are static correspondence checks,
not execution, a transition checker, testing or independent review.

No Oracle invocation, Cargo/build/test, instrumentation, benchmark, Git
mutation, shared-record edit or delegated worker ran. At most four short
read-only shell processes overlapped; later source reads and hash/integrity
checks used one shell process at a time. Samples/seeds/search ranges: none.
CPU/RSS and elapsed wall time were not instrumented; no numerical quota was
supplied. The zero-execution budget and exclusive file lease were preserved.
Requested normal routing: gpt-6.1-sol/high under the inspected repository
defaults; observed effective model/effort: unknown, with no runtime metadata
available. No Astra or hot-reload claim. Writes stop before independent review.

Frozen input SHA-256 values:

| Input | SHA-256 |
| --- | --- |
| P | `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7` |
| S | `affb7a0fe174c755877fe09bc2633c488b53bc0281ba6cd2082bb7a85aac0535` |
| Simplification audit | `03a41253c461be1209d74b6d6bcf4c2ee84902000ec054f068a233334a53bf41` |
| Oracle generalize/mod.rs | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| Oracle core/prune.rs | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| Oracle core/stack_ids.rs | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| Oracle generalize/finalize.rs | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| Oracle compact/finalize.rs | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| Oracle typing.rs | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |

Next action: primary assigns fresh independent review of K's level/boundary,
pruning predicates and ordinary installed-scheme correspondence, then consumes
the accepted result in the actual fresh-use/provider lane.

- Exact changed/leased path: `notes/theory/2026-10-12-oracle-direct-return-stack-cleanup-proof.md`.
- Baselines: Y3 `5bb504465075f398247a3899ff31e1fcc6a4c7af`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; pinned inputs and owning sources match.
- Review status: frozen producer derivation, independent K review pending; no H or production-gate promotion.
- Checks already run: focused static reads, 29 pinned-byte/hash checks and leased Markdown integrity; zero execution/build/test.
- Proposed checkpoint message: `research: derive direct callback stack retention through scheme export`.
- Shared-record deltas left for primary/curator: record K's bounded literal installed-scheme image and review state; keep H and downstream fresh-use/provider/call/output gates OPEN. `tasks/current.md`, theory maps and design indexes remain primary-owned and unchanged by this leaf.
