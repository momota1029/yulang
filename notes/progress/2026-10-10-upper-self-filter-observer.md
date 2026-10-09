# Upper self retention: negative extrusion and the missing observer

Date: 2026-10-10
Status: frozen, unreviewed research; conditional derivation
Baseline: `566310fa8a1076d5e518af3fb50585005194afdc`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Method: bounded owning-source inspection and explicit state derivation
Production authority: none

## Objective and governing premises

Determine whether the reviewed three-formal fixture's future Empty filter
observes **upper-only** retention of its contextual self candidate, and trace
the primary's specifically requested negative-extrusion continuation. This
does not repeat the reviewed positive-lower discriminator.

Governing language authority is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,4,6:
contravariant concrete annotations permit position-local subtraction;
covariant annotations permit the specified concrete effects; symbolic variables
retain their connection and later concrete checks. The corrected callback
target retains its returned `int ->`. That callback is not exercised here.
The concrete implementation gate's opening paragraphs and “Annotation checking
and publication owner” distinguish immutable annotation support from emitted
contributions and preserve composed polarity, source levels and publication
ownership. Nothing here changes those meanings or supplies a grant from an
allowance. Rules research-lab, design-authority and git-concurrency were read
in full. Shared records and concurrent HIR edits were not changed.

Existing reviewed evidence is the fixture and its independent review:
`2026-10-10-contextual-self-discharge-falsifier{,-review}.md`.
That evidence proves a difference only when retention supplies an ordinary
positive lower `(T+, PUSH_i[{io}])` at T. Its shared-tail and future Empty-demand
owner derivations are reused with their existing limits. Oracle actually drops
the self candidate. No source execution or new admission result is claimed.

Write `P = PUSH_i[{io}]`, `L_T(X,w)` for a positive lower stored at T,
and `U_T(X,w)` for an upper stored at T. The weight notation below is a
**candidate extension assumption**, not a current successor data type.
The candidate currently has endpoint-only bounds and tasks, and rejects the
required explicit formal effect rows (`candidate_effect.rs:845–847`).

## 1. Conditional local non-observation

The reviewed source-shaped fixture is:

```yulang
type io
my separate (f: 'c -> [io; 'e] 'c) (g: 'c -> [; 'e] 'c) (accept: ('c -> [] 'c) -> 'c) = accept g
```

This text was not parsed or executed here. Reuse only the reviewed local
source projection: f's paired annotation supplies a candidate
`T <: T @ P` after registering `{io}`; `accept g` registers Empty on T and
supplies `T <: U` for a distinct empty-row coordinate U. Neither event supplies
an independent positive lower at T. Value coordinates and the empty
annotation's attachment identity remain distinct from T and i.

Explicit hypotheses for the local result:

1. Retention is `U_T(T,P)`, with no corresponding positive self lower.
2. This finite local trace has no positive lower at T and no omitted incoming
   effect contribution, transport step, equality merge or future source use.
3. Filters inspect existing/future positive lowers; installing an upper does
   not independently test its stored context against every row filter.
4. Bound replay compares opposite sides, and no other observer reads stored
   upper metadata in this trace. The observation is the named filter violation,
   not graph serialization, counters, printed schemes or all future behavior.

Under these hypotheses, keep/drop have the same Empty-filter result.
Filter registration reads an empty lower collection. Adding `T <: U` selects
an upper at T at equal levels. Its opposite collection is also empty, so it
does not replay against `U_T(T,P)`. The retained self edge has a row endpoint;
there is no Function child to decompose at this point. This is an induction
over the displayed finite events: each adds only upper/filter state and cannot
create a lower by opposite replay from an empty lower collection.

Owner facts: `candidate_extrusion.rs:675–691` omits current identity pairs and
otherwise chooses the upper at the left row when the right level is no higher;
`:443–458` distinguishes the two row-bound sides; `:506–512,537–548,602–608`
reads only the opposite side. Oracle's filter owner is
`bounds.rs:3213–3255,3285–3315`. These source facts ground the local theorem;
they do not establish hypothesis 3 for a future contextual successor.

Thus this fixture's **reviewed local observer** does not discriminate upper
retention. This is neither full fixture equivalence nor a safe-discharge theorem.

## 2. Negative extrusion supplies a lower, but insertion is not replay

Let T be deeper than the target boundary b. Conditionally suppose a real
negative occurrence of T is reached by ordinary extrusion. The exact current
owner trace is:

```text
before:       U_T(T,P), no lowers at T
visit (T,-,b): allocate C at b; retain parent(copy=C,parent=T,polarity=-)
source link: L_T(C,id)
copy bound:  U_C(C,P)       [only if the contextual payload is transported]
```

`candidate_extrusion.rs:89–122` checks the source level, snapshots the selected
upper side, allocates C, records the parent, and inserts the **opposite** source
side. Therefore negative extrusion really can add a positive lower at original
T. It is incorrect to say that transport can never supply the missing lower.
For a copied self upper, the operation's row map already maps `(T,-,b)` to C;
`:123–162,278–292` therefore copies that selected upper to a C self upper.
Its source-origin entries are transferred separately.

Two distinctions prevent this alone from proving the reviewed filter difference:

- The source-link owner at `:122` calls `candidate_insert_bound`, which records
  origin/side but does not replay the opposite upper. Copied-bound installation
  at `:284` also calls insertion. The actual replay owners are `:595–632` and
  restore `:557–591`. Hence the original `L_T(C,id)` is not automatically
  replaced or supplemented by `L_T(C,P)` during this operation.
- A subsequent Empty filter on original T, under the Oracle-style rule, checks
  the identity-weighted lower C and then C's lowers. The reduced state has no
  lower at C. It does not inspect `U_C(C,P)` merely because it reached C.
  An escaping interface that exposes only negative C likewise has no activated
  weighted positive lower.

This is a bounded owner trace, not a claim that a completed source solve omits
every replay. Additional constraints, recapture or equality can change it.

The source-facing way extrusion could reach negative T is concrete: a positive
escaping Function reverses polarity in its formal parameter; the callback's
result Effect retains that reversed polarity. The four-port traversal is
`candidate_extrusion.rs:209–233`. Ordinary Value solving invokes positive
extrusion of a structured lower at a destination row's level, or negative
extrusion of a structured upper at a source row's level
(`lib.rs:11840–11864`). This identifies a possible owner route. It does not
certify that this exact fixture reaches a deeper original T through an admitted
formal constructor, or that its later exposed interface includes original T
rather than only C.

## 3. Parent/copy equality is conditional on an actual return path

Intrusion traverses both row-bound sides as dependency edges
(`candidate_intrusion.rs:409–432`). In the reduced extrusion state these supply
`T -> C`, `T -> T` and `C -> C`, plus any separately copied empty-upper
dependencies. Assume those latter dependencies do not return to T. There is
then no `C -> T` path.

The retained parent record is explicitly **not** a dependency graph edge
(`:471–480`). Only parents whose original and copy already lie in one computed
SCC are merged. The reduced state therefore does not identify C with T.
If an actual source continuation supplies a return dependency, this conclusion
fails and the equality route must be analyzed anew.

When merging does occur, `:541–566` appends each bound on its original side,
`:568–584` installs the representative and minimum level, and `:588–592`
replays all canonical positive lowers against uppers. The merge can therefore
activate a contextual self upper **if** the contextual representation preserves
its payload through canonicalization and **if** a lower survives to that replay.
Current `canonical_effect` remaps row ordinals only (`lib.rs:11278–11283`);
it proves no context or attachment-owner preservation. Equality must not turn
the local i grant into authority for unrelated siblings.

## 4. Scheme replay exposes the discriminating level partition

Generalization/use is a concrete future owner, not an invented observer.
Local installation records root and boundary (`candidate_scheme.rs:917–925`);
an actual local use captures that live root, freshens, and links the exposed
value to its consumer (`:937–953`). Capture retains bound side (`:468–504`),
and fresh restoration explicitly preserves it (`:841–864`). These operations
do not by themselves prove that the root reaches original T and its lower C.
An interface reaching only the escaping copy C need not reach T; parent
metadata is not an inverse semantic link.

Suppose, additionally, the captured interface really contains
`L_T(C,id)` and `U_T(T,P)`. Restore compares that opposite pair irrespective
of restoration order and offers `C' <: T' @ P`. Two partitions then differ:

| Captured row partition | Ordinary induced owner | Consequence in the reduced state |
| --- | --- | --- |
| Both T and C local, freshened to the same use level | upper at C' | Stores `U_C'(T',P)`; does not supply the weighted positive lower at T' required by the reviewed observer. |
| T local/fresh; C an outer anchor with `level(C) < level(T')` | lower at T' | Can store `L_T'(C,P)`, which is the missing filter-visible operand. |

The first row assumes no additional lower at C' and no registered parent pair
for the fresh rows. Freshening's row-map loop `:737–749` allocates/maps rows;
it does not recreate the old extrusion-parent record. A two-row dependency
cycle alone is not sufficient for this parent-specific equality operation.

The second row follows exactly the level comparison in
`candidate_extrusion.rs:679–685`. Scheme locality is
`candidate_scheme.rs:200`, with canonical use-time rechecking at `:739–745`.
The possible partition is `level(C) <= boundary < level(T)` and a deeper
fresh use. It is a candidate source premise, not a demonstrated interface of
the three-formal fixture.

Under that second partition, context-preserving replay, and the reviewed
current/future lower filter rule, a minimal conditional activation witness is:

```text
keep: restore L_T'(C,id) together with U_T'(T',P)
      => C <: T' @ P => L_T'(C,P)
drop: restore only L_T'(C,id)
future observation: Empty on T'; C has no other positive lowers
```

Keep checks the active `{io}` in P and rejects; drop follows C's empty lower
collection and has no such violation. Original `{io}` permits P. The state
uses two row identities, one nonempty attachment and one filter observation;
there is no cyclic expansion or count search. This is a conditional witness
schema, **not a minimized admitted source counterexample**. It also does not
decide whether a rejection caused by retaining annotation attachment evidence
is correct for the selected language.

## 5. Exact remaining source and payload dependencies

The missing observation certificate must establish all of the following in one
actual source route:

1. A negative extrusion caller reaches deeper original T and creates lower C
   without an earlier formal-row rejection.
2. The genuine generalized/used root reaches **original T plus its C lower**,
   not just the negative escaping C. Its owner/boundary makes T local while C
   remains an outer anchor, or supplies another actual lower/replay/equality
   route. Row ordinal similarity is insufficient.
3. The kept self upper carries P's ordered attachment and resolved `{io}`
   payload with the original annotation position/local authority. Capture,
   freshening, canonical equality and replay preserve the relevant identities
   and map them consistently. The payload must be in the semantic comparison,
   not merely diagnostic metadata.
4. Replay's ordinary lower insertion and retained Empty filter observe this
   payload, reach the finite observation, and preserve independently attached
   same-family contributions. No premature memo completion, contextual
   subsumption, resource failure or rollback may suppress the compared event.

Current `EffectEndpointKey` (`lib.rs:753–765`), endpoint-only effect tasks,
`candidate_effect::BoundKey` and `candidate_scheme::Bound` have no P payload.
`candidate_insert_bound` records the active processing pair or bound-pair
origin (`candidate_extrusion.rs:383`, `candidate_effect.rs:350–361`), copied
bounds transfer these origins, and replay connects both bound origins to its
task (`candidate_extrusion.rs:628–630`). Those are real diagnostic dependencies.
They do not establish attachment ownership, contextual semantic identity,
or that a source initializer's original T is exposed in a later scheme.
No new carrier or production design is selected by listing these missing facts.

## Coverage, failure controls and handoff

New claim class: unreviewed conditional local non-observation, an exact
negative-extrusion owner trace, and a conditional anchored-replay discriminator.
Established results remain the independently reviewed fixture and its stated
positive-lower premise. No full theorem, source admission, runtime successor
discrepancy, soundness, principality, hygiene closure or implementation authority
is promoted.

Oracle independence: pinned Oracle source grounds filter/replay behavior;
pinned successor source independently grounds orientation, copying and scheme
owners. The combined conditional derivation **shares** the supplied contextual
extension/filter assumptions. Oracle drops the self edge and does not execute
the proposed keep alternative. No independent executable oracle validates
that combination; a checker implementing it would only check those premises.

Analytical controls: remove P and the keep-only violation disappears; expose
only C and the needed T lower is unreachable; freshen both rows at equal level
and the induced context moves to an upper at C'; add a real return dependency
and the no-equality argument no longer applies; add a concrete lower at C and
drop may also reject. These are derived controls, not executed mutations.
No random seeds, enumeration ranges or mutation runner were used.

Checks: bounded `git show <pin>:<path> | nl -ba | sed -n ...` owning reads;
ten-path SHA-256/live-byte comparison against baseline; note-only whitespace
and hash checks at submission. All ten dependencies matched pinned bytes;
HEAD was unchanged at dependency check. No code/Cargo/compiler/source execution,
tests, formatter, Git mutation, child agent or benchmark ran. Source/hash reads
were lightweight; CPU time, peak RSS and elapsed wall time were not measured.
The only write is this leased note. Parser/lowering/publication, all-source
root reachability, contextual payload transport, termination and rollback were
not verified. No exhaustive source search was attempted.

Recommended next action: audit the **actual negative-extrusion caller and later
scheme root** for original-T/C incidence and the anchored/local partition,
returning that source-owned certificate or a precise exclusion. Another
endpoint-only toy checker cannot supply this missing premise.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-upper-self-filter-observer.md`.
- Baseline SHA: `566310fa8a1076d5e518af3fb50585005194afdc`; Oracle SHA:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none in the ten checked dependencies. Key SHA-256s:
  selected authority `ff61df92a84185ef22aecbc6915208fbdee225dc647b51007ea28601e38a70f9`;
  concrete gate `592dc8d6ea54aefd0cbc76244966874ac2d61b66cd249795c2ea3ce1de337765`;
  fixture `2b81891ce53f22b842c0b68a8de52c850bf130e7040277f94b0a0339db37acd4`;
  fixture review `099ab969aaa8b3c17abbbb410cbaeaf40f5d2a283e108bf25d5876ac5df15164`;
  extrusion `34639c30b21699549772e9d4e27513f8bf9c4db999c11bad28a0fff266cf0a5a`;
  intrusion `097aa65bfdac125ff1ed61de362e9302de6a1ef2a1ea94fd12ae29e77c8e9b8a`;
  scheme `4fe9d709e5237fb8e767276887cd3cf558cd6069606d67649be6934ac063c863`.
- Review status: frozen, unreviewed research; producer does not certify it.
- Checks already run: pinned source inspection, ten dependency byte/hash
  comparisons, note-only whitespace/hash check. No executable semantic checks.
- Proposed checkpoint message: `research: trace upper self activation through negative extrusion`.
- Shared-record deltas intentionally left to primary/curator: distinguish the
  reviewed lower-retention fixture from upper retention; record negative
  extrusion's opposite source link, insertion/replay distinction and the
  original-root/anchored-partition observation gate. Keep contextual self
  discharge, source formal rows, payload transport and production gates open.

Writes stop at this frozen submission.
