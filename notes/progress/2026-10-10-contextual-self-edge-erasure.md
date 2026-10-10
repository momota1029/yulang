# Contextual self-edge erasure: direction, phase, and a universal unit test

Date: 2026-10-10
Status: frozen producer research; unreviewed conditional algebra and source bridge
Baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Scratch: `/workspace/scratch/15155572c47b/self_edge_source/`
Production authority: none; no source restrictions or compiler changes selected

## Result

An equal endpoint is not sufficient for contextual self-edge omission. The
locally decidable, universal transfer test is **empty residual directed context
at an actual mix-normal fact boundary, after retaining the original checks**.
For the exact one-ID natural full-pair algebra, this test is also necessary
among constant weights when every mix-normal incoming context is possible.
On arbitrary raw contexts there is no constant universal replay unit, including
the nominal identity. A semantic epsilon optimization must preserve the real
mix boundary and every consumed-filter event; replacing the whole operational
step by a no-op is not justified by an empty residual label.

The source bridge distinguishing an upper self from a lower self is now exact
at its existing claim boundary: negative extrusion inserts an identity lower
without replay; the retained original local root and later deeper fresh use
then supply the anchored replay which can turn a retained upper PUSH into a
filter-visible positive lower. The explicit contextual constructor and payload
transport are still absent. Singleton symbolic-only Function formal effects
are now accepted; concrete and empty formal rows remain rejected. This updates
the older notes' blanket formal-row rejection without treating the remaining
gate as an authorized restriction.

Governing authority is annotation-effect-hygiene-integration §§1,4–6. Composed
polarity, resolved concrete effects, position-local subtraction, symbolic
connections, independent same-family contributions, and the corrected returned
`int ->` callback layer remain unchanged. Rules design-authority,
orchestration-budget, research-lab, git-concurrency and AGENTS were read. Inputs
include the contextual-self-discharge falsifier/review, upper-self observer/
review, upper-self source-root bridge/review, formal-effect recursive component,
recursive-push source invariant and recursive-push results. This note neither
adds an unproved admission prerequisite nor closes the mixed Effect decision,
full hygiene, soundness/principality or public cutover.

## 1. The actual owners and the current construction boundary

The pinned successor's `candidate_apply_effect` first canonicalizes endpoints,
then drops every equal pair (`candidate_extrusion.rs:675–690`). Otherwise, a
row-to-row comparison stores an upper at its left row when the right level is
no higher; if the right row is deeper it stores a lower there. Thus merely
removing the self guard at equal levels would store an **upper**, not the
positive self lower used by the first reviewed filter falsifier.

`candidate_insert_bound` records the selected side and origins without replay
(:353–490). `candidate_replay_bound` reads opposite bounds and enqueues their
comparison (:595–632); `candidate_restore_bound` inserts and runs comparisons
on the ordinary worklist (:557–591). Negative extrusion snapshots the selected
upper side, allocates a shallower copy, maps the visit, and inserts the opposite
source lower (:89–162). Its direct insertions are not replay calls.

The current constraint representations are endpoint-only: `EffectEndpointKey`
and `TypedPairKey::Effect` (`lib.rs:753–775`), `LiveConstraintTask::Effect`
(:3989–3992), effect `BoundKey` (`candidate_effect.rs:34` and its pair projection
at :262–283), and scheme
`Bound` (`candidate_scheme.rs:79–85`). There is no file named
`candidate_constraints.rs` at this baseline; the owning task/memo structures
are in lib and candidate_effect. Diagnostic origins connect ordinary bounds
and replay tasks, but do not carry ordered attachment context or supply an
attachment/filter producer.

`candidate_source::preflight_formal` now accepts an explicit row exactly when
its concrete list is empty and it has one symbolic variable (:77–81).
`candidate_formal_pair` enforces the same condition and builds paired Function
ports using scoped symbolic Effect coordinates (`candidate_effect.rs:876–913`,
including the effect-port helper immediately after the pair). The new accepted route
preserves symbolic connection. Neither `[io; 'e]` nor `[]` can construct the
PUSH/filter operands below. General annotation Support/Allowance views are
real implemented operands, but they do not constitute this missing contextual
formal constructor and must not be called a replacement merely by matching
their endpoint shapes.

Oracle's actual same-Var drops occur before its Var-pair mix normalization in
`entry.rs:1092–1114`, and again in `propagate.rs:108–110`. Its ordinary Var/Var
retention would store both orientations (:111–133), unlike the successor's
one-sided level routing. The Oracle drop is a source fact; no weight-sensitive
equivalence proof follows from that fact.

## 2. Exact phase-sensitive algebra

Fix one attachment ID, one fixed family, natural counts, and replay filter All.
Write a raw directed context as `W=(p,n,r)`: leading left POP count, active
left PUSH count, and right POP count. The absent entry is `(0,0,0)=I`.
Empty families do not delete entries or active counts. This is the natural
algebra used by the reviewed research observer; Oracle's u32 saturation is an
implementation guard, not an equation in this theorem.

For left pairs define

```text
C((p,n),(q,m)) = (p + max(q-n,0), m + max(n-q,0)).
M(p,n,r) = (p,n,r)                         if r=0 or p+n=0;
          (a,b,0)                         if b>0;
          (0,0,a)                         otherwise,
where (a,b)=C((p,n),(r,0)).
R(U,V) = M(C(U.left,V.left), U.right+V.right).
```

Prefix and right-suffix operations preserve raw context until the actual M
point. Function swap is `(r,0,p)` and drops active left PUSH. These definitions
are pinned Oracle `directed_weight.rs:17–43,138–177,391–410` and
`constraints/mod.rs:3560–3639`, with the fixed-family natural-count abstraction
made explicit. Replay is directed: a lower of weight x against an upper of
weight w produces `R(x,w)`, whereas a self lower of weight w against an upper
of weight y produces `R(w,y)`. Mixing is not associative replay flattening.

A context is mix-normal when `M(W)=W`. M is idempotent: its output either has
zero right count, zero left pair, or was unchanged for one of those reasons.
Every left-only full pair `(p,n,0)` is normal, including `(1,1,0)`; normal does
not mean signed depth, debt-only, or at most one left count.

Oracle's ordinary Row-to-Var bound insertion erases its consumed left filter
but does not generally call M (`bounds.rs:630–650,815–835`). Therefore
**normal stored facts are not a proved global Oracle invariant**. Some
Var-pair canonical keys and replay-produced facts are normal, while wrappers
can create raw contexts before insertion. The criterion below is applied to
an actual normal boundary or retains the M operation; it does not assume every
bound is normalized.

### Theorem A: the maximal universal constant unit on normal inputs

For either direction, the following holds:

```text
(for every mix-normal x, R(x,w)=x) iff w=I;
(for every mix-normal y, R(w,y)=y) iff w=I.
```

This permits raw w in the quantified constant domain. Proof:

1. If `M(w)!=I`, choose input I. Both `R(I,w)` and `R(w,I)` equal `M(w)`,
   which differs from I. The residual active/debt/entry observation separates
   the results even if the family is Empty.
2. If `M(w)=I` and `w!=I`, the definition of M forces
   `w=(0,k,k)` for some positive k. Choose the normal input `D=(1,0,0)`.
   Direct calculation gives `R(D,w)=R(w,D)=(0,0,1)`, unequal to D. The
   distinction is the directed location of the pending POP; swap or left/right
   entry inspection observes it. Thus even "mix(w)=identity" is insufficient
   for a constant self label offered to later normal contexts.
3. If `w=I`, both replay directions are `M(input)`. They equal every normal
   input. This proves sufficiency, necessity and maximality in the stated
   universal constant-weight class.

In particular, a normal nonidentity constant is immediately excluded by input
I. The finite decision is inspection of the actual residual entries and
consumed-filter state, rather than an unbounded path search. Independent IDs
have independent count composition with fixed family per ID. For testing a
unit against I, any surviving ID entry already distinguishes it. The same
zero-entry sufficient rule extends to finitely many IDs; no changing-family
or attachment-identity reconstruction theorem is asserted here.

### Theorem B: there is no universal replay unit on raw inputs

If a constant w preserved every raw input, it would preserve the normal inputs
and Theorem A would force `w=I`. But for raw `X=(0,1,1)` both replay directions
give `R(I,X)=R(X,I)=M(X)=I`, unequal to X. Contradiction.

This is not a pathological large-count example: one PUSH and one right POP
are enough. X has an active left entry which a filter at that raw node can
inspect; M(X) has none. Moving that filter past replay changes an observable
event. Identity cannot be described as a global unit or silently erase M.

## 3. A concrete observational normal form, rather than signed support

The finite-observer alphabet used by the existing research DSL includes exact
active count, left/right pending-debt presence, left-entry presence, identity,
prefix by fixed POP/PUSH counts, suffix, mix, swap, and replay. Under one fixed
ID/family, equality under all finite continuations in this alphabet is exactly
equality of the **raw triple at its named phase**.

Proof of separation for distinct triples A and B:

- If their n coordinates differ, the node's exact active-count observation
  separates them immediately.
- If their n coordinates agree but p differs, prefix by `PUSH_k`, with
  `k=max(p_A,p_B)+1`. The resulting active counts are `n+k-p_A` and
  `n+k-p_B`; they differ.
- If p and n agree but r differs, choose
  `k=p+max(r_A,r_B)+1`, prefix by `PUSH_k`, then perform the actual mix.
  Both have positive active count; the outputs' active counts are
  `n+k-p-r_A` and `n+k-p-r_B`, which differ.

Conversely identical triples give identical evaluation and checks through any
finite syntactic continuation by structural induction. The proof does not
use bounded debt saturation and distinguishes any natural counts. It shows
why matching family support or signed `n-p` cannot justify omission, and why
the phase tag cannot be suppressed. For general changing families, type
arguments, IDs and owner payload, the normal form must additionally retain
those actual typed operands; this note proves neither their reconstructibility
nor a finite global semantic alphabet.

The all-node trace matters. A continuation is recorded as a vector of named
node phases and triples, including the raw nodes where a filter runs. Comparing
only its final M result is weaker. Shared recursive selections must retain one
selection identity across all their occurrences. Neither a support set nor
independently enumerated holes preserves that correlation.

## 4. Local sufficient omission and exact state-dependent redundancy

Theorem A supplies a small **sufficient optimization contract**, not a new
language precondition. At the owning operation:

1. Canonicalize only the underlying row identities, retaining the original
   annotation position and attachment authority.
2. Execute and retain the source-mandated filter/stack checks and persistent
   filter registrations at their original raw node phases. An already checked
   allowance does not discharge a later independent filter.
3. Perform the actual M operation where replay requires it. If the incoming
   data is already normal, M is a no-op; otherwise keep the M transfer even
   when eliminating a physical self adjacency entry.
4. Only when the residual directed context is I, and the remaining transfer
   is normal-input identity, omit the data self edge. Preserve any constraint
   receipt/provenance needed to explain the already executed checks. Empty
   residual context creates no attachment grant.

Here "residual context" means the actual constant descriptor offered to future
replays by the selected representation. Replacing a raw constant w by M(w)
in isolation is not this criterion: Theorem A's balanced `w=(0,k,k)` is a
counterexample to that replacement. An implementation which canonically stores
M(w) at admission is choosing that normalized-label transfer semantics; its
correspondence to retaining the raw constant needs a separate argument. This
note does not supply that argument by calling the constant normalized.

For a least-fixed-point grammar of normal facts, a unit production `X -> X`
adds no fact: deleting it preserves the least solution. This follows directly
by the two inclusions between pre-fixed solutions, or by replacing any finite
use of the unit production by its child. All subsequent deterministic finite
continuations receive the same exact descriptor, so the preceding normal-form
lemma gives their equal observations. Existing/future filters see the same
lowers and the same retained registrations. This includes future lowers,
not merely those present when the edge was considered.

An upper self w has local lower transfer `x -> R(x,w)`. For a particular
completed drop-state grammar and future extension, let L be its exact normal
lower facts at the row. Under monotone unguarded propagation, the exact
**fact-preserving** erasure test is the explicit closure equation

```text
{ R(x,w) : x in L } subseteq L.                 (upper self)
{ R(w,y) : y in U } subseteq U.                 (lower self / upper replay)
```

Use the corresponding exact typed descriptor and owner payload, not just count
support. A lower self also inserts an actual positive lower and exposes its
own left stack to current/future row filters; the second equation alone does
not remove that additional event. It must be matched by retained fact/check
events. If raw facts are involved, replace these displayed normal sets by
phase-tagged raw facts and retain their actual M transfer.

Why the closure equation suffices in its stated monotone fact semantics: the
drop solution already satisfies every old production; closure makes it satisfy
the new self production too. The least keep solution is then contained in the
drop solution. The reverse containment follows from old-production inclusion.
Necessity for *exact fact preservation* follows because the keep solution must
contain each self consequence. This is a calculable algebraic closure test
when an exact finite representation of L/U is supplied. It is stronger than
an arbitrary fixed-program observation test and does not purport to decide
all possible alternate-path redundancy.

To certify open-world omission, apply closure to **every actual future
extension**, including restoration, equality replay and newly registered
filters. If incoming contexts can be arbitrary normal singletons, Theorem A
reduces this universal requirement exactly to w=I. A restricted empty lower
set makes every upper self vacuous today, but does not establish that future
extensions remain empty. Restrictions not established by source construction
are not permitted as new user-visible source exclusions.

There is no proved finite decision here for arbitrary alternate paths,
mixed recursive context languages, correlated copying, changing families and
arbitrary future source extensions. The existing left-only PVASS theorem and
finite mixed observer results keep their own scope; they do not decide language
inclusion/equality for this full class. No undecidability claim for the actual
unguarded language follows from the guarded counter-machine reduction either.
The universal unit theorem closes a local optimization question while leaving
that genuinely different global decision problem explicit.

## 5. The authentic directional source trace and its missing payload

Reuse the independently reviewed source-root bridge, with its existing
conditional contextual premises:

```yulang
act io
my bridge h opaque = {
  my f (a: (int -> [io; 'e] int) -> int)
       (g: (int -> [; 'e] int) -> int) = {
    my ignored = h a;
    1
  };
  my later = {
    my empty (k: int -> [] int) = 1;
    f opaque empty
  };
  later
}
```

This text remains unexecuted. It is not currently admitted, since a's concrete
row and empty's empty row are unsupported formal constructors. Its omitted-row
analogue has the actual owner route, and the accepted symbolic-only g preserves
the shared scoped-tail part of that route. In the structural control, replace
a's `[io; 'e]` by `[; 'e]` and omit the later Empty-demand observer.
`candidate_formal_effect_variable` (:823–839) keys the coordinate by the actual
annotation scope and name; `candidate_formal_effect_port` (:899–906) reuses it
for both nested callback results. Thus shared **named** T, rather than only
the old omitted-row q, now has a current constructor owner. The same directional
Function/extrusion/root trace applies to that symbolic structural control.
It has no P and supplies no kept upper or filter discriminator. No parser,
successful public type or source-minimality result is claimed.

The successor's actual Apply and retained root owners supply these events:

```text
level(h)=1; level(f's original T)=2; installed f boundary=1
h a demand at outer h
  -> negative demand Function's positive argument A
  -> A's positive Function lower
  -> negative nested callback argument
  -> negative callback result Effect T
negative extrusion to 1
  -> fresh C at 1; parent(copy C, original T, negative)
  -> direct insert L_T(C,I), with no opposite replay at that insertion
f's retained negative formal domain still reaches original T
install f's original initializer root, boundary 1
later f Name at use level 2
  -> capture original T and both bound sides, including anchored C
  -> fresh T' at 2; retain C at 1
  -> restore sides and replay L_T'(C,I) against kept U_T'(T',P)
  -> C <: T' @ P
  -> level(C)<level(T') selects L_T'(C,P)
separate symbolic-only g comparison against empty's callback
  -> register Empty on T'
```

Owners are the bridge/review's pinned level/Apply/lambda references,
`candidate_extrusion.rs:89–162,209–233,557–591,679–685`, and
`candidate_scheme.rs:200,418,463–504,737–749,841–864,917–953`.
The original-root traversal is a forward constructor/capture path; parent
metadata is not an inverse semantic edge. The actual parent relation is not
an SCC graph edge (`candidate_intrusion.rs:471–480`). Only an independently
present shared-SCC path permits the selected parent/copy equation. Merge
appends bound sides, changes row representative/level and replays opposite
bounds (:541–592). It neither proves w=I nor merges annotation authority.

For `P=PUSH_i[{io}]=(0,1,0)`, the kept upper's anchored replay creates a
positive lower whose left stack contains io. Empty checks it and rejects.
Drop has only `L_T'(C,I)` and follows C's lower collection; under the reviewed
no-other-rejecting-lower premise it has no corresponding io violation. The
original `{io}` filter remains in both alternatives and permits P. This is the
directional source discriminator for the nonunit; it does not assume a
positive self lower was stored at equal levels.

Oracle `bounds.rs:3213–3255` checks existing positive lowers on a new filter;
:3285–3320 checks future lower insertion. Checking a weighted lower first
checks its active left stack, then its positive endpoint. A duplicate Var
filter registration cannot undo the already observed concrete violation.
Thus reversing Empty registration and weighted-lower insertion still observes
the same keep-only named violation. A concrete or separately attached same-
family lower at C can make drop reject too; such an additional input changes
this named discriminator, not Theorem A's universal counterexample.

The contextual extension still must construct P with the real attachment i,
preserve it through Value/Function traversal and extrusion, capture/freshening,
restore and equality, and implement the filter check. Whole-source SCC/memo
ordering, earlier contradictions, finite completion and failure rollback remain
unverified for that extension. The previously reviewed successful omitted-row
owner derivation does not fabricate this payload. Both original and newly
fresh uses need their own mapped attachment ownership; anchoring the row does
not anchor a local grant globally.

## 6. Fresh use, rollback and evidence boundaries

Current scheme capture retains bound sides and per-use row maps; it remaps
actual general annotation views and contributions (`candidate_scheme.rs:
737–790,841–864`). Current effect-algebra rollback removes owned formal-domain,
annotation-variable, conflict, edge and origin changes and truncates views/
contributions (`candidate_effect.rs:148–187`). Intrusion rollback restores
representatives, generations, completed pairs and memos
(`candidate_intrusion.rs:103–130`). These are actual owner seams; no absent
context/attachment/filter state is thereby journaled automatically. A future
epsilon rule may not retain a "filter already checked" memo after rolling back
its registration or transfer. The criterion is applied within the actual
transaction and fresh-use mapping, with checks/provenance included in rollback.
This is a correspondence requirement for implementing the selected semantics,
not a new restriction on source programs.

One semantic probe ran, with no child, Cargo, compiler, broad test, formatter,
Git mutation, random seed, benchmark or source execution. Reproducible scratch
command:

```sh
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B /workspace/scratch/15155572c47b/self_edge_source/probe.py'
```

It passed 275,801 assertions. Constants w had coordinates 0..8; raw inputs
0..4 checked normal identity/idempotence; separation pairs had coordinates
0..3. The explicit raw identity and balanced-nonzero mutations were checked.
Reported internal wall time was 0.1453 s and maximum RSS 6,656 KiB, within one
30 s / 256 MiB single-process budget. One of two authorized semantic probe
slots was used. The model shares the transcribed algebra; it validates arithmetic
consistency, not source admission or an independent compiler semantics oracle.
The preceding unbounded proofs establish their stated algebraic results.

Ten live source/dependency files matched baseline bytes at the pre-write hash
check; pinned Oracle owners were read from their Git objects. The independent
reviews cited are reviews of prior source traces, not of this note. The note
is frozen at submission and remains unreviewed research. No claim of production
defect, full-context observational quotient, maximal alternate-path decision,
source finiteness, complete mixed decision, Call, hygiene, soundness/principality
or implementation authority is made.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-contextual-self-edge-erasure.md`.
- Baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`; Oracle:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Claim class: conditional universal one-ID full-pair unit/separation theorems;
  state-dependent exact-fact closure criterion; actual source-owner bridge with
  explicit missing contextual payload. Producer-frozen, independently unreviewed.
- Changed production/authority dependencies: none in ten byte comparisons.
- Key successor SHA-256s: extrusion
  `34639c30b21699549772e9d4e27513f8bf9c4db999c11bad28a0fff266cf0a5a`;
  source `8aa0292bf47050ad64f8f5f11de05bef8c10d6200f86b53155cd7fe8c0f1e892`;
  effect `db12ebe60e97b237c0c4bac6ef375bb583347ac1b4dc9881df395f6a4d349b4d`;
  scheme `4fe9d709e5237fb8e767276887cd3cf558cd6069606d67649be6934ac063c863`;
  intrusion `097aa65bfdac125ff1ed61de362e9302de6a1ef2a1ea94fd12ae29e77c8e9b8a`;
  lib `88b11bc3195a38b17017c6f40c42404ed5c1874d0375d64943bfe86019cb751b`;
  authority `ff61df92a84185ef22aecbc6915208fbdee225dc647b51007ea28601e38a70f9`.
- Oracle SHA-256s: directed weight
  `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db`;
  constraints/mod `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392`;
  bounds `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7`;
  propagate `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086`;
  entry `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8`.
- Verification: bounded source/rule/input reads, dependency SHA/live equality,
  one arithmetic probe above, note-only whitespace/hash at handoff.
- Proposed checkpoint message: `research: derive phase-sensitive contextual self-edge unit test`.
- Shared-record deltas intentionally left to primary/curator: record universal
  normal-input I criterion and no raw unit separately from the still missing
  contextual constructor; replace blanket formal-row rejection with the exact
  symbolic-only progress; preserve upper/lower orientation, genuine future
  filter behavior, and global mixed/alternate-path decision boundaries.

Writes stop at this frozen submission.
