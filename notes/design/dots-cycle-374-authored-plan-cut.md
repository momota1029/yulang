# C374: bind a source-addressed event to the visible occurrence

I-65 step 1 only. Source-level derivation using C291, C359, C360, C365,
C367 and the C373 retained-event cut. No new Lean module or fixture.

## Exact source ordinal to exact candidate position

C291 `SourceMetadataBundle291.registry` keeps the literal
`SourceBundle.declarations` list as its `declarations` field, not an
ID lookup or a sorted table. Consequently C365 `visible s q` is
literally that same list filtered by `row.role == q.demand.role`.
On the event side, C360 `NativePreparation360.Prepared` provides
`authored` at `frame.sourceOrdinal` in this raw catalogue, and
`identity` with the demand role. These are actual fields used by
`prepare` before the compiler; neither comes from the resulting
dictionary ID, target, or model. The event's environment must be
the actual `s.current.environment`, not a re-ordered copy.

Let `A` be that raw authored declaration list, `P` its role
predicate, and `rank(i) = ((A.take i).filter P).length`. For a valid
source ordinal `i` with `A[i]? = some d` and `P d = true`:

1. `(A.filter P)[rank(i)]? = some d`. Split `A` as
   `take i ++ d :: drop (i+1)`; filter each piece. At the length of
   the filtered prefix the fresh head is exactly `d`.
2. Among indices of entries passing `P`, `rank` is strictly
   increasing. If `i < j`, the filtered prefix before `j` contains
   the whole filtered prefix before `i` and at least the retained
   entry at `i`. The proof needs no declaration equality or
   uniqueness-of-ID hypothesis.
3. For every valid visible ordinal `k`, there is a unique passing
   raw index `i` with `rank(i) = k`. For existence induct on the
   raw list: a passing head consumes visible ordinal 0 and decrements
   remaining ordinal; a skipped head consumes none. In both tail
   cases increment the raw index. Uniqueness is point 2. The map
   therefore retains positions even for identical declaration values.

Obtain the actual matched visible ordinal `k` from C367 `Stores`
in a singleton-live tape; the source event belongs to that chosen
catalogue entry precisely when its valid authored raw index has rank
`k`. Equivalently use the unique original index from point 3. Matching
the declaration ID or even the whole declaration value does not prove
this positional equality. It cannot recover an index in the presence
of duplicates, and is unnecessary in this argument even if a
particular checked catalogue excludes them. This does not assert that
duplicate entries can both be accepted by the language.

## What this adds to the event-side bridge

For a genuine `Prepared` event at this exact source index, explicitly
pair `frame.occurrence = q.occurrence` and the original request
`q.demand`; the role alone cannot do this. The two independent
facts (the matched tape ordinal; the event's authored position)
now refer to the same authored declaration occurrence without a
semantic model or comparing values after the event. The real compiler
returns children at the clause ordinal, with `q.occurrence ++ [j]`;
C361's existing `Direct`/ `actual_compiler_position` provide the
same positional link to an independently authored bare-binder
operand in their represented case. They are not substitutes for
compound instantiation or selected-capture layout.

The static ordinal link does not create the actual event. It checks
attachment of an independently known event, and does not generate
`Layout`, infer capture from the body, certify that rows are retained
at a post-write state, or prove active version/grant. C360
`Prepared` stops before final typed output installation and does
not elect a declaration; Stage-1 full selection still needs native and
candidate-local K2 priority and real event/capture production. Keep the
source catalogue, demand occurrence, authored row provenance, and
where/fixed-output attachment separate. C372 handles the ordinary
retained state *after* a genuine event and C373 only transports
declaration value, not positions. The frozen public theorem and
accepted output domains are unchanged.
