# Restoration lower-prefix owner audit

Date: 2026-10-13
Status: frozen source derivation; independently reviewed; original disposition gate OPEN
Baseline: `de56edf909ad9b7b329d508e5609831decf191c3`
Branch: `research/simple-sub-intrusion`
Lease: this file only; independent falsification/source producer, not proof reviewer

## Objective and authority

Identify an actual callback that adds a direct lower to a Value owner while
restoring its upper, and examine compensation across its complete authentic
capture. Governing meaning is private candidate suspension contract §4:
install once, save opposite count, reread the live canonical direct/exact
vectors at each index. Top-level inference principles §§1–4 and Authority and
integration govern ordinary inference, efficiency and necessary safety.
No snapshot replacement, eager all-pair solve or registry requirement is proposed.

This audit uses the yulang-proofs source-bridge discipline and reads the supplied
restoration-disposition proof, native bulk-bound coverage, live-index audit and
reentrant-source audit. The constructive lane remains independent. The present
result is a **conditional native-constructor derivation**, not a source-program
counterexample or proof that no accumulated joint disposition exists.

## 1. Equal-level callback exclusion and a different actual producer

`candidate_apply_value` (`candidate_extrusion.rs:808–836`) selects a row/row
comparison `s <= a` as an upper on **s** when `level(a) <= level(s)`.
Only strict `level(s) < level(a)` selects a lower on a. Actual preparation
(`candidate_scheme.rs:1006–1019`) gives every fresh local row the same
`use_level`. Thus merely exchanging argument and result in an all-local,
parent-free equal-level trace cannot reproduce the prior upper-prefix example
as a direct-lower append at the restored row. This statement needs persistent
equal levels and representatives; it says nothing about mixed/shared rows or
subsequent merges.

A distinct owner does append the lower: dispatch of **shared row s <= negative
Function f'**, with `level(s) < level(a')` and f'.result = negative a'.
`lib.rs:12411–12447` negatively extrudes f' to level(s). Function extrusion
visits its result negatively (`candidate_extrusion.rs:224–250`); visiting a'
allocates a lower-level copy c, retains its extrusion parent, and installs
`c <= a'` on a's **positive side** (`:105–123`). Physical insertion maps this
to `ValueLowerRow`, then unconditionally pushes the direct-lower vector
(`:441–487`). This is a real lower-prefix mutation before the child returns.
It is a bulk parent-link insertion, with no immediate replay side effect.

The opposite f' already installed at a' is among the negative selected bounds
copied to c. The rebuilt Function has result c (`:328–355`), and its copied
upper is installed on c through Work::Bound (`:307–327`). This is the actual
possible transport/accumulation disposition to investigate; it is not another
arbitrary shifted-vector fixture.

## 2. Native seed, original construction and hypotheses

Interface hypotheses: a candidate-enabled session with available identities and
storage; genuine collected occurrence/cause IDs and Int/Unit/effect leaf terms;
empty distinct a,t allocated at level 1, shared empty s at level 0; boundary 0,
use level 1; identity contexts and no effect-row/view/attachment inputs.
Use the actual signed Function constructors (`lib.rs:10230–10300`) and
`admit_candidate_value_link` (`candidate_scheme.rs:1334–1342`) with distinct
valid source occurrence slots. No populated Graph or hand-added physical
constraint is supplied.

| Term | Polarity | Argument | Argument effect | Result effect | Result |
|---|---|---|---|---|---|
| g1 | Positive Function | UnitNegative | EmptyEffectNegative | EffectBottomPositive | positive s |
| g2 | Positive Function | IntNegative | EmptyEffectNegative | EffectBottomPositive | positive s |
| f | Negative Function | positive t | EffectBottomPositive | EmptyEffectNegative | negative a |

Admit and drain `g1 <= a`, then `g2 <= a`, then `a <= f`.
The last ordinary replay queues both Function comparisons before their callbacks
run (`candidate_extrusion.rs:763–803`, deferred replay driver). Real Function
ports (`lib.rs:12498–12538`) generate `t <= UnitNegative`, `t <= IntNegative`
and, for both results, `s <= a`. The first result installs s as a direct lower
on a; the second identity relation can reuse that current typed pair.
Replaying the first result's bound queues `s <= f`.

Its negative extrusion creates c at level 0 from a and d at level 0 from t.
The parent writes are `c <= a` on a and `t <= d` on t. Negative copying gives
c an upper fc, where fc.argument = positive d and fc.result = negative c.
The transformed task stores fc as an upper on s. No lower is created on s,c,d.
Relevant original stores are therefore:

```text
a: direct lowers [s,c], exact lowers [g1,g2], exact uppers [f]
t: direct uppers [d], exact uppers [UnitNegative,IntNegative]
c: exact uppers [fc]; no lowers
s: exact uppers [fc]; no lowers
d: no bounds
```

Original intrusion does run after this drain (`lib.rs:12001–12010`). Its
dependency graph follows bounds and Function ports (`candidate_intrusion.rs:
386–472`). The c/fc component reaches c and d but cannot reach a; d cannot
reach t. Thus neither retained parent copy shares an SCC with its original,
so the qualifying merge condition (`:483–493`) does not merge a/c or t/d in
this stated identity seed. This is a source-graph reachability argument, not
an assumption that intrusion is disabled.

No incompatible scalar comparison is generated: t has upper requirements
and no lower. This establishes absence of the displayed constructor's
Int/Unit conflict; it does not establish source acceptance or publication.

## 3. Authentic capture and the complete restoration blocks

Capture from a at boundary 0. Both a and t are local; s,c,d are nonlocal.
Capture follows direct lowers, direct uppers, exact lowers, exact uppers for
each local Value row (`candidate_scheme.rs:577–619`). Nonlocal rows have no
saved owner block (`:572–573`). Each row is expanded once (`:745–779`). The
single-identity-fiber seed yields the complete relevant saved blocks:

```text
a block: s<=a, c<=a, g1<=a, g2<=a, a<=f
t block: t<=d, t<=UnitNegative, t<=IntNegative
s,c,d: no captured owner block
```

Function f's pending expansion discovers t before its row block is processed;
a's complete block still precedes t's. Every captured entry is created by
Capture::bound with its actual BoundKey, relation and evidence snapshot
(`:522–567`). This seed's one-fiber characterization is essential: additional
nonidentity/multiple captured fibers would require recalculating the saved
block, and are outside this derivation.

The two current routes recapture immediately before preparation: DefinitionUse
at `:945–960`, LocalUse at `:1373–1374`. Preparation allocates empty a',t' at
level 1 and shares s,c,d at level 0. The same FreshUse maps f to f' with argument
t' and result a'; g1,g2 remain the original row-free-with-respect-to-local-rows
Function terms because their only row is shared s. In particular f' differs
from f, so the old completed g2<=f pair is not g2<=f'. Each saved entry is
transported and admitted by `begin_candidate_fresh_bound` (`:1221–1266`).

The first four a' restorations find no upper and cause no child. Restoring f'
then saves N=4 with direct lowers [s,c], exact lowers [g1,g2]. Its actual
callback selections are:

1. Index 0 selects s. Negative extrusion of f' at level 0 allocates e1 from
   a' and d1 from t', appending e1 to a'.direct_lower. It creates a negative
   Function fe1 with result e1 and argument d1, installs it as an upper on e1,
   and executes transformed `s <= fe1`.
2. Index 1 selects original c. Its analogous extrusion adds e2 to a' and an
   upper copy on t'; c receives an upper fe2.
3. Index 2 now selects e1, because the current direct length is 4. It adds e3;
   e1 receives an upper fe3.
4. Index 3 selects e2 and adds e4; e2 receives an upper fe4.

The restoration ends at its saved count. It has selected `[s,c,e1,e2]` and
selected neither g1 nor g2. Each selected lower has level 0 and no lower
bounds; each new e has only copied negative uppers. These transformed tasks
therefore generate no Function/Function comparison with g1 or g2. None of the
new copies has a dependency path back to a' or t', so the inspected SCC merge
condition supplies no merge replay in this trace.

There is no later captured a' upper: f' was its last saved entry. Its original
g1/g2 lowers have already been restored. The complete later t' block restores
upper d and upper Unit/Int. t' has no lowers: its callbacks only received
positive extrusion parent uppers. Thus that block also generates no g2<=f'.
The shared rows have no captured owner blocks to run afterward.

This is bounded absence of that **direct endpoint comparison** through the
complete stated FreshUse restoration. It does not prove the absence of a
semantically valid accumulated or joint transported disposition. The shared
s/c copies and newly retained e/fe parent routes are real retained inequalities.

## 4. Exact remaining gate

Actual replay, when selected, constructs the product from both BoundKeys and
both fiber heads, retaining ordered Dependency::Replay
(`candidate_context.rs:2974–3050`). Here g2's mapped lower fiber at a' and f's
mapped upper fiber at a' are admitted, but their endpoint product is not
selected by this restoration, its later saved blocks or the displayed copy
consumers. Original g2<=f completion and copied s<=fe are not by themselves
completion of the joint mapped g2/f incidence. They may contribute to a law
justifying that incidence; such a law is the unresolved original obligation.

The owning remaining premise is therefore the **negative extrusion parent-link
and selected-upper joint disposition**, including original source BoundKeys,
FreshUse input fibers and copy scopes. Endpoint comparison absence does not
refute that law. Scalar transitivity, independent marginal fibers, or equality
of context IDs cannot establish it. No blanket absence claim about all
candidate_context evidence is made.

Parsed/HIR reachability of the three admissions, their intended scopes and
the publication/use boundary remains unestablished. candidate_source Apply
and Lambda planning/dispatch were located (`:394–459,671`) but no same-source
program/action derivation fits this packet's static budget. Failure to finish
that bridge is not evidence that the native seed is source-forbidden.
Complete source coverage, Call, L4, soundness, principality and F5 remain OPEN.

Recommended next action: independently audit this mixed-level construction and
its copy consumers, then assign the joint negative-extrusion parent-link law
to the existing constructive lane. Preserve the original gate and derive
source reachability separately; another equal-level shifted-vector probe
cannot answer this new owner seam.

## Checks, resources and frozen dependencies

Checks: narrow cat/sed/rg source and policy reads, read-only `git rev-parse HEAD`,
direct dependency `git diff --name-only de56edf... -- <listed inputs>` (empty),
SHA-256 dependency hashes. Some combined earlier reads were truncated; the
critical orientation, extrusion, replay, capture, dispatch and SCC sections
were subsequently read narrowly. No tests, builds, probes, measurements,
mutations, seeds/ranges or executable oracle ran. Zero heavy processes; CPU/RSS
and observed runtime model/effort are unknown. Assigned static wall cap: ten
minutes; precise elapsed time was not measured. This note is not independent
review of the constructive artifact. Writes stop with this artifact frozen.

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
bbc54b0624a31569271412269dfec70ce75d4bbfc4fa74f3df64590d732c29d4  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
947981cb10d88ac599fa0cbde72125382393dc73635b6ddfd61fcbeaeb883cd3  notes/theory/2026-10-13-fresh-use-restoration-disposition-proof.md
bc878d17ab42119132b5d3ef1c3f675493068886c172adcaee15cc61b4e0ae46  notes/theory/2026-10-13-native-bulk-bound-coverage.md
b98c41d86c8ef9c5b0ba0430d0f0c18d43fc9f9e9eb42fb7dd85e629ec85822f  notes/progress/2026-10-13-restoration-live-index-pair-audit.md
4a421d701bdbb3ebc5b4bc00b72404d12fc7c04f5d536402e26ebd3da0aad572  notes/progress/2026-10-13-fresh-use-reentrant-source-audit.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-restoration-lower-prefix-owner-audit.md`.
- Baseline SHA: `de56edf909ad9b7b329d508e5609831decf191c3`.
- Changed dependency hashes: none against pinned baseline; prior notes contain
  historical candidate_context hashes, so use the frozen current hash above.
- Review status: frozen unreviewed conditional source derivation; primary owns review.
- Checks already run: narrow static owner/consumer reads, baseline path equality,
  dependency hashes; no execution.
- Proposed commit: `research: identify negative-extrusion restoration lower-prefix owner`.
- Shared-record deltas left to primary/curator: record the strict level condition,
  mixed shared/local negative-copy producer and complete-block endpoint gap;
  retain the original joint-disposition/source/Call/L4/soundness/principality/F5
  gates OPEN. No shared records or compiler files changed.

## Primary review and concrete consumer handoff

One fresh independent compiler-referee reviewed this frozen audit together
with the [bounded temporal coverage proof](../theory/2026-10-13-restoration-temporal-coverage-proof.md).
Both passed with no BLOCKING, major or minor finding. The reviewer checked
the source writes, captured order, negative copies, SCC condition and later
restoration blocks. The primary checked the twelve dependency hashes, local
links, fences and whitespace. No tests, builds, probes or measurements ran.

The actual later `t' <= IntNegative` and earlier `s <= a'` are precisely the
argument and result comparisons of `g2 <= f'`; the two effect-port comparisons
are bottom-to-empty leaves. The absent direct endpoint comparison therefore
supplies no semantic failure. This gives a narrower concrete proof target than
assuming a universal copy law: establish joint per-use transport from the
original `g2 <= f` FunctionPort dependencies to those two authentically captured
child incidences, preserving the two mapped parent fibers, original BoundKeys
and shared FreshUse identity. Existing scalar children alone do not prove that
joint evidence law. The negative-copy route remains available for its own
general obligation.

The primary consumes the actual lower-prefix owner and this child-transport
handoff. Parsed/HIR reachability, accepted publication, joint original evidence,
complete source/Call, soundness/principality and F5 remain OPEN. The preceding
producer packet records its pre-review status; no source restriction or
implementation repair is authorized by this audit.
