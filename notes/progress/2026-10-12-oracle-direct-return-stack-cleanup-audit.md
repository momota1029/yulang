# Oracle direct return: stack cleanup, scheme selection and fresh use

Date: 2026-10-12
Status: frozen producer source characterization; independent review pending; H OPEN
Claim class: bounded source characterization, conditional published-scheme/use image
Y3 packet baseline: `5bb504465075f398247a3899ff31e1fcc6a4c7af`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file only; leaf; no execution, delegation or Git mutation

## Objective and premises

Trace `my direct(cb: (() -> [tick] ())) = cb` from the accepted
[S simplifier result](../theory/2026-10-12-oracle-direct-return-simplification-proof.md)
through the actual stack-cleanup, quantifier-selection, scheme-storage and
fresh-use owners. The primary's packet accepts S as independently reviewed;
this audit does not reproduce S or its accepted conditional
[P projection input](../theory/2026-10-12-oracle-direct-return-projection-proof.md).
The earlier [simplification audit](2026-10-12-oracle-direct-return-simplification-audit.md)
is an input locator, not an additional theorem premise.

Authority is annotation-effect-hygiene-integration §§1–2 and top-level
inference principles §§1–5. The selected meaning of composed-negative `[E]`,
the original H source domain and its occurrence/scope/provider/use/call/output
quantifiers remain fixed. No language meaning or compiler implementation is
selected here.

The exact premises consumed from S are its first fresh public-root collection,
normal completed native construction/replay, no incoming external-use constraints,
one retained positive x occurrence with Pα, one negative x in a tick-row tail,
no recursive bounds, and no role/interval contribution changing that slice.
Pα has filter All, empty floor, zero pops and the singleton stack Set(tick),
where tick is the resolved nullary family. x and α denote the annotation's
original coordinate and ID. Successful ordinary allocation, name resolution
and owner completion remain operational hypotheses.

Two later premises are kept separate: the finalizer's actual ancestor list,
and an actual successful fresh-use event. The bare declaration and S's local
snapshot do not specify either. Results below show the exact image when these
owners receive the derived input; they do not assert a surrounding execution.

## Actual consumer and selection context

Oracle citations are relative to `crates/infer/src/`, except poly citations.
This is the production path, rather than the test-only wrapper at
`generalize/mod.rs:777–783`:

1. `lowering/body/mod.rs:2282–2318,2356–2365` enters a child level, registers
   the public root and uses the named-header-argument constructor.
   `lambda.rs:954–975` returns `Computation::value` for the wrapper.
   `body/methods.rs:287–299,387–408` records FetchValue and enqueues DefFinished;
   `analysis/session/lifecycle.rs:1062–1064` stores this fetch immediately.
2. SCC settlement emits QuantifyComponent before its pending InstantiateUse
   events (`scc.rs:335–352`). The session consumes QuantifyComponent via
   `analysis/session/selection.rs:1107–1119` and `instantiate.rs:14–21`.
3. `analysis/session/generalize.rs:32–33,480–518` passes the prepared
   simplifier output to `prepare_stack_cleaned_alias_expanded_compact_root`,
   with the actual quantification boundary and an empty non_generic set.
   `generalize/mod.rs:160–173` enters the shared cleanup at 805–834.
4. The session's post-alias/post-cleanup dominance scans at 492–542 are
   empty for S's no-interval slice, so neither adds a new x constraint between
   these consumers. At 544–549 it invokes generalize_stack_cleaned_compact_root.

The quantification boundary is not inferred from the compact Function alone:
`analysis/session/generalize.rs:767–776` reads BindingFetch, and
`typing.rs:96–103` maps FetchValue to root. Annotation x is allocated by
`annotation/constraints.rs:615–617`; `arena.rs:34–37,57–60` registers it at the
definition's positive-depth level. In S's isolated slice its only relevant
ports stay at that definition level; S establishes no x extrusion to root.
Cleanup takes an immutable machine and changes no levels. Thus x is free and
has level greater than the actual root boundary. The census at
`generalize/mod.rs:900–915`, with empty non_generic, includes x. Birth level
alone would not establish this conclusion for a different accumulated graph.

## Exact cleanup derivation

| Owner | Derived result on S's input |
| --- | --- |
| Unreachable-recursive cleanup, `core/prune.rs:90–123`, invoked at 815/827 | No recursive bounds exist; neither x occurrence changes. |
| Quantified-subtract pruning, `core/prune.rs:39–77`, invoked at 819 | Annotation registers the declared `(x,α,Set(tick))` fact at `annotation/constraints.rs:593–600`. Regardless of the separate live-subtract predicate, α is in live_covariant_stack_ids, so the dead-ID filter at 71 excludes it. |
| General stack cleanup, `core/prune.rs:605–620`, invoked at 828 | α has a nonempty positive stack; it is in live_ids and cannot enter all_ids minus live_ids. |
| Plain-negative cleanup, `core/prune.rs:630–727`, invoked at 188 | The negative x counterpart exists, but Pα is neither Empty-only, spent-with-single-floor nor instantiated-with-MAX-pops. Set(tick), empty floor and zero pops make all three predicates false. |
| Stack quantifier selection, `core/stack_ids.rs:22–58,84–111,201–205`, invoked at 197–204 | The nested returned callback has composed-positive polarity; x is quantified and its stack is nonempty, hence α is selected. |
| Stray-ID pruning, `generalize/mod.rs:207–233` | α belongs to scheme_ids and cannot be pruned as stray. |

Both ID traversals reverse Function arguments and preserve Function results;
the path `root → outer Function.ret → callback Function.ret_eff` is positive.
This uses the actual returned occurrence from S, not the formal's negative
row prefix. The declared-All fallback at 867–887 does not establish α's
selection: its fact is Set(tick). Quantified x plus its positive stack does.
Neither cleanup nor selection renames x or α. The resulting
GeneralizedCompactRoot has x in quantifiers and α in stack_quantifiers, with
the returned Pα occurrence intact. This bounded source result is established
by direct consumer case analysis under S's stated premises; no original H
closure or general hygiene theorem follows.

A discriminating failure condition is visible without an executable model:
if x were unquantified, the same nonempty Pα would pass 805–834, yet α would
fail the filtered selection at 197–198 and the Set(tick) fact would not rescue
it. Stray-ID pruning would then remove α. This alternate input is a consumer
discriminator, not a source-qualified counterexample to the derived FetchValue
slice or H.

## Published scheme: the remaining context-sensitive seam

`analysis/session/instantiate.rs:51–82` first stores the compact result in
self.schemes, then computes scheme_ancestors_for_current_poly and finalizes
into `poly.defs[direct]`. The ancestor lookup at
`analysis/session/generalize.rs:940–955` follows actual Def children and
retains only ancestors present in self.schemes. `analysis/mod.rs:751–763`
constructs that parent map. This is an operational input, not implied by the
syntax of the displayed declaration.

`generalize/mod.rs:843–864` applies ancestor simplifications **before** its
final quantifier/stack cleanup. `generalize/simplification.rs:3–14,100–108`
can delete x through an ancestor None substitution or merge its weighted
occurrence with another target; ancestor sandwiches can also change its view.
S proves the local simplifier input/output and supplies no actual ancestor
substitution inventory. Therefore the first missing premise for an
unqualified published-scheme claim is the actual ancestor list and its action
on this x/Pα incidence. For a standalone declaration whose chain contains no
generalized Let ancestor, the lookup returns no retained ancestor; this
sufficient placement premise makes the ancestor action the identity. It is
not silently added to S's claim.

Conditional on that identity action, both final cleanup predicates repeat the
same established nondeletion checks; x remains free, α is selected again,
and unquantified-stack pruning cannot remove it. `generalize/finalize.rs:3–27`
copies the quantifier vectors into Scheme, clones weights into the scheme
arena and structurally finalizes. Its stack-weight cloning preserves entry
IDs and the resolved Set(tick); nullary tick needs no argument remapping.
`compact/finalize.rs:415–425,542–548,586–592,711–720,837–839` finalizes the
returned callback's variable-only Effect as
`Pos::Stack { inner: Pos::Var(x), weight: Pα }`. No row constructor is present
at this positive variable-only coordinate, so it takes finalize_pos_type;
the singleton union returns that Stack. principal_stack_weight changes only
the filter to All, which Pα already has (`poly/src/types.rs:326–329`).
`analysis/session/generalize.rs:958–963` stores the resulting Scheme in the
actual Def::Let slot. A formatted scheme is not evidence for any of these
steps; the conclusion follows from the owning constructors.

## Fresh-use representation and stop boundary

Conditional on a successful ordinary, nonimported/nontemplate InstantiateUse
of that stored Scheme, `analysis/session/selection.rs:1050–1080` calls the
production batch at `analysis/session/instantiate.rs:311–335`. Its preparation
reads that Def::Let scheme at 363–366 and selects
instantiate_scheme_with_roles_and_provenance at 448–455, at secondary level.
`instantiate.rs:620–636,732–748,763–785` allocates one fresh image x′ for x
and α′ for α, clones the predicate and wraps its **whole root** with
POP(α′,u32::MAX). The same memoized maps are used by both callback companions
and all stack entries (`788–846,849–901,983–999`). Thus the initial fresh
representation contains:

```text
root: Stack(cloned outer Function, POP(α′, u32::MAX))
root.inner.ret.ret_eff: Stack(Var(x′), PUSH(α′, Set(tick)))
root.inner.arg.ret_eff.tail: NegVar(x′)
```

The last path denotes the negative callback's retained Row(tick) tail. The
outer wrapper and nested push are distinct constructors, not a calculated
cancellation. α is quantified before storage and renamed at fresh use; it is
not lost at either of those bounded boundaries. Fresh-ID allocation and
weight cloning alone do not clone a declared `(x,α)` fact: fresh_subtract only
allocates/memoizes the new ID. No new scope/provider/handler grant follows
from the ID map.

The root is Pos::Stack, so the direct-lower optimization predicate at
`analysis/session/instantiate.rs:717–729` rejects it. Preparation queues its
subtype to NegVar(use_value) at 505–519, and the batch submits it at 332–334.
The next consumer is native stack normalization/admission, followed by the
actual application and returned-callback route. This audit stops before those
operations. It neither proves root-pop discharge at the nested Effect nor
infers purity, a missing concrete lower, provider preservation or H from the
representation. The actual use/call/output envelope is outside S's isolated
declaration snapshot.

Recommended next action: obtain the exact placement/ancestor inventory for
the chosen direct instance, then assign the normalized fresh-use subtype and
actual call/output route as the next source-owned bridge. Preserve these
consumer boundaries rather than running another projection/simplification
probe.

## Checks, resources and commit packet

Static rg/nl/sed/cat reads and read-only Git revision queries only. Python
SHA-256 and `git show <pin>:<path>` comparisons checked five Y3 inputs and
25 Oracle source files; all 30 current byte sequences matched the packet pins.
Observed Y3 HEAD at startup was `2e53d9e9a9ecaf488a4bd04fd18394c4192d3b9e`;
the exact frozen dependencies matched the earlier packet baseline. No
dependency was edited. Some first combined reads truncated; decisive branches
were reread narrowly. Missing guessed module paths were replaced by the
actual owners; no source search/execution outcome is claimed for them.

Decisive dependency SHA-256 values:

| Dependency | SHA-256 |
| --- | --- |
| P | `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7` |
| S | `affb7a0fe174c755877fe09bc2633c488b53bc0281ba6cd2082bb7a85aac0535` |
| simplification audit | `03a41253c461be1209d74b6d6bcf4c2ee84902000ec054f068a233334a53bf41` |
| generalize/mod.rs | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| generalize/core/prune.rs | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| generalize/core/stack_ids.rs | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| compact/finalize.rs | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| instantiate.rs | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |

No Oracle execution, tests/builds, compiler instrumentation, executable model,
mutations, benchmark samples, child or Git mutation. Seeds/ranges: none.
Source is the operational reference; no independent executable oracle ran.
The audit shares pinned source bytes and accepted P/S premises with the proof
lane, and is a producer, not an independent review. At most four lightweight
read processes overlapped initially; subsequent decisive reads used at most
two. CPU/RSS and elapsed time were not measured; no numeric resource quota was
supplied. No heavy process ran. Runtime model/effort metadata: unknown.
Verification is dependency/note integrity, not semantic certification.

Unverified scope: actual ancestor input, actual fresh-use reachability and
normalization/admission, subsequent providers, nested callback application,
output and the original universal H. No compiler/shared record changed.
Writes stop here before frozen review.

- Exact leased path: `notes/progress/2026-10-12-oracle-direct-return-stack-cleanup-audit.md`.
- Baselines: Y3 `5bb504465075f398247a3899ff31e1fcc6a4c7af`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; decisive hashes above.
- Review status: frozen producer characterization; fresh independent review pending; no H or unconditional published-scheme closure.
- Checks already run: focused source/call-context reads; 30 pinned-byte/hash comparisons; leased-note integrity and scoped diff checks. Zero execution/build/test.
- Proposed checkpoint message: `research: trace direct callback stack cleanup and fresh-use image`.
- Shared-record deltas left for primary/curator: record local α retention through GeneralizedCompactRoot, its quantifier dependence on actual FetchValue/level context, conditional stored-scheme retention and consistent fresh x/α maps; preserve ancestor/action and actual normalized use/call/output gates as OPEN. No shared file was edited.
