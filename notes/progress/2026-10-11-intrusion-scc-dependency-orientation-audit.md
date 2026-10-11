# Intrusion SCC dependency orientation audit

Status: frozen, unreviewed research checkpoint; source characterization and
conditional mathematical discriminator. No theorem closure or implementation
authority.
Date: 2026-10-11
Baseline: `c8c62f473028d7684813e83284cc228b28a09831`
Owner/method: `intrusion_graph_source_map`, bounded static source audit.
Exclusive lease: this note only. No compiler, test, design or Git mutations.
Budget: 30 minutes static investigation; at most four concurrent lightweight
read commands in a batch within this lane, no builds or executable probes.

## Objective and authority

Compare the SCC adjacency actually constructed by
`candidate_intrusion.rs::settle_candidate_intrusion` with the directions of
constraints processed by `candidate_extrusion.rs::candidate_apply_value`, its
Effect counterpart, structural extrusion, and four-port Function dispatch.
The accepted user operation is parent retention on extrusion and equality of
the parent and copy when they enter the same SCC. Its governing source is
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Direct decision** and
**Selected operation and compiler responsibility**. The retained boundary
does not establish soundness, principality, or public cutover.

The top-level principles in
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3 require
mathematical Simple-sub operations, justified optimizations, and proof-derived
implementation; §§4–5 govern abnormal paths. This audit makes no rollback
requirement. The research/write boundaries come from `rules/research-lab.md`
**One semantic baseline**, **Evidence quality**, and **Writes, artifacts and
review snapshots**, plus `rules/git-concurrency.md` **Disjoint-file mode**.

The inspected authority states the equality operation but does not formally
define the directed dependency graph meant by “same SCC.” In particular, it
does not equate physical bound incidence with the directed subtype relation,
nor specify a variance-sensitive structural dependency graph. This note
identifies a distinction requiring adjudication; it does not select a new
language meaning or assert that subtype-relation SCC is the selected meaning.

## Three objects that must be kept distinct

1. **Physical adjacency P:** the exact graph built by the current SCC owner.
   A row points to every row/structural endpoint in either stored bound side.
   A Function points to all four ports. An Allowance or Support points to its
   symbolic tail. Parent metadata contributes no edge.
2. **Constraint graph C:** a comparison graph defined here only for the audit:
   each accumulated scalar constraint `a <: b` contributes `a -> b`. This
   faithfully preserves the direction named by the emitted relation, but is
   not independently established as the intended intrusion dependency graph.
3. **Structural occurrence/dependency graph:** a constructor references its
   children, potentially with signed positions. Outgoing occurrence edges do
   not by themselves encode subtype variance. A semantic account must state
   what its edges mean before its SCCs can be compared with P.

No numerical-level invariant proving termination or absence of particular
physical SCCs establishes that P has the semantic SCCs required for intrusion.
Conversely, P differing from C alone does not refute the selected operation.

## Exact scalar storage and orientation

`candidate_apply_value` canonicalizes the endpoints and ignores identity pairs
(`candidate_extrusion.rs:808`). For two distinct rows, it selects the lower row
as upper-bound owner when `L(b) <= L(a)`, otherwise selects the upper row as
lower-bound owner. It performs one insertion and replays opposite bounds;
it does not install the mirror storage cell. The insertion routine explicitly
defines Positive as lower storage and Negative as upper storage
(`candidate_extrusion.rs:387`, `:436`, `:463`).

For the single constraint `a <: b`:

| Levels | Selected physical cell | Relation represented by cell | P adjacency | C direction |
|---|---|---|---|---|
| `L(a) < L(b)` | `b.direct_lower_rows += a` | `a <: b` | `b -> a` | `a -> b` |
| `L(a) > L(b)` | `a.direct_upper_rows += b` | `a <: b` | `a -> b` | `a -> b` |
| `L(a) = L(b)`, distinct rows | `a.direct_upper_rows += b` | `a <: b` | `a -> b` | `a -> b` |

P combines `direct_lower_rows` with `direct_upper_rows`, without reversing the
lower side (`candidate_intrusion.rs:390`). Consequently, unequal-level direct
constraints have P edges from the higher-level row to the lower-level row,
independently of the constraint direction. This is a local source fact, not a
proof of a global level invariant across every restoration/merge path.

Effect rows use the same branch conditions and one-sided storage with
`effect_levels` and `effect_bounds` (`candidate_extrusion.rs:840`, `:509`;
`candidate_intrusion.rs:415`). They are distinct typed vertices:
`ValueRow(0)` and `EffectRow(0)` are unrelated identities. Mixed-kind insertion
is rejected; no scalar Value-to-Effect subtype constraint is inferred here.

Replay respects the bound sides: inserting a lower bound pairs the inserted
bound as lower with each stored upper; inserting an upper pairs each stored
lower with the inserted upper (`candidate_extrusion.rs:763`). Those generated
relations therefore retain subtype direction even though SCC incidence
forgets the storage-side distinction. The SCC owner does not construct its
adjacency by iterating the typed relation/memo table.

## Minimal mathematical discriminator and extrusion specialization

**Claim class:** conditional finite characterization; no source-program
counterexample. Hypotheses are two distinct canonical rows, initial levels
`L(a)=0`, `L(b)=1`, empty relevant bounds, successful ordinary insertion/replay,
and no other edges or merges. Interpret the comparison graph as C above.

Submit `a <: b`, then `b <: a` through `candidate_apply_value`:

1. The first puts lower `a` on `b`, giving P edge `b -> a`.
2. The second puts upper `a` on `b`, also giving P edge `b -> a`.
3. Replay compares `a <: a`; the identity transition inserts no new edge.
4. Thus P has components `{a}`, `{b}`. C has edges `a -> b`, `b -> a`,
   hence component `{a,b}`.

This is minimal in distinct row vertices for a disagreement about whether two
rows share an SCC. In the empty, ordinary scalar-insertion envelope, one
nonidentity constraint gives one directed edge and cannot put two rows in a
shared SCC in either graph; the two opposite constraints suffice. The levels
`0,1` are the smallest unequal nonnegative levels. The same derivation applies
separately to two Effect rows using `candidate_apply_effect`.

The derivation is grounded in actual owner branches, rather than a checker
that merely assumes invented transitions. It remains conditional on those
branches being reached. No source term producing this exact two-row state has
been exhibited, and no compiler runtime was executed in this packet.

A parent/copy specialization connects the discriminator to intrusion:

| Actual extrusion operation on empty high-level parent `p`, target `0` | Creation relation/storage | Opposite submitted relation via ordinary owner | Final P edges |
|---|---|---|---|
| Positive, `L(p)=1`, creates `c` | `p <: c`; upper `c` stored on `p` | `c <: p`; lower `c` stored on `p` | `p -> c` twice |
| Negative, `L(p)=1`, creates `c` | `c <: p`; lower `c` stored on `p` | `p <: c`; upper `c` stored on `p` | `p -> c` twice |

`candidate_extrude` creates the copy at target level, retains the real parent,
and inserts the copy on `opposite(polarity)` of the parent
(`candidate_extrusion.rs:90–123`). With empty source bounds there are no copied
bound dependencies. Opposite replay again produces only `c <: c`.
`settle_candidate_intrusion` excludes parent provenance from adjacency and
requires the computed components of `p,c` to match before merging
(`candidate_intrusion.rs:477`). Therefore it does not merge this pair under
these hypotheses, whereas C puts them in one SCC. This is a source-owner
transition discriminator, not evidence that an accepted source program must
produce the opposite relation or that C supplies the required semantic graph.

The existing test `real_extrusion_parent_copy_scc_equates_both_kinds_and_polarities`
does not discriminate these graphs. Its helper `close_cycle`
(`candidate_intrusion_tests.rs:44`) invokes `candidate_restore_bound` with the
copy as owner, directly installing the reverse physical adjacency. Ordinary
`candidate_apply_value` / `candidate_apply_effect` would select the higher-level
parent as owner for the opposite relation in the displayed state. The test
establishes the merge operation when an explicit physical cycle is installed;
it does not establish equivalence of physical SCCs and constraint SCCs. The
existing natural-source tests explicitly do not claim that their source alone
forces a parent/copy SCC merge; their historical pass results were not rerun.

## Function structure and contravariance

Construction preserves four typed ports. `lib.rs:10266`, `:10282` delegate to
`term.rs:1126`, `:1147`, whose constructor checks require:

| Function endpoint | Argument Value | Argument Effect | Result Effect | Result Value |
|---|---|---|---|---|
| Positive | Negative | Negative | Positive | Positive |
| Negative | Positive | Positive | Negative | Negative |

For `x <: F-(a,ae,re,r)`, the typed owner first extrudes the structural upper
at `L(x)` and may re-enqueue a rewritten Function (`lib.rs:12428`). It stores
that rewritten Function as an exact upper of `x`; P has
`x -> F- -> {a',ae',re',r'}`. The extrusion traverses `a,ae` at opposite
polarity and `re,r` at the Function polarity
(`candidate_extrusion.rs:224`). Younger children are replaced by the appropriate
polarity copies, whose parents are retained. Thus primes matter: P references
the actual rewritten ports, not automatically the original coordinates.

Conversely, `F+(a,ae,re,r) <: x` is stored as an exact lower of `x`, after positive
extrusion at `L(x)` (`lib.rs:12415`). P still has `x -> F+ -> ports`, whereas C's
outer relation points `F+ -> x`. An isolated `x <: Function(...)` does not
generate a scalar relation between `x` and every port. Neither `x <: a` nor
`a <: x` follows merely by naming a Function argument; occurrence and subtype
dependencies cannot be identified by inspection of that one constraint.

For an actual comparison `F+(a1,ae1,re1,r1) <: F-(a2,ae2,re2,r2)`, dispatch emits
the following real children (`lib.rs:12493`):

| Field | Generated relation | Kind | Variance |
|---|---|---|---|
| Argument | `a2 <: a1` | Value | contravariant |
| Argument Effect | `ae2 <: ae1` | Effect | contravariant |
| Result Effect | `re1 <: re2` | Effect | covariant |
| Result | `r1 <: r2` | Value | covariant |

These are then subject to their own levels and storage ownership. P's
structural traversal selects the correct child *polarity* but adds the edge
from Function to child for all four fields (`candidate_intrusion.rs:445`).
It does not reverse edges for contravariant fields or add direct edges between
the compared Function terms. This is a structural occurrence traversal; its
matching port polarity is insufficient to prove a variance-sensitive semantic
dependency theorem.

A candidate polarized expansion would retain signed occurrences such as
`(Value,a,+)` and `(Value,a,-)`, rather than P's single canonical `ValueRow(a)`.
The constructor table above supplies the authentic sign transitions: argument
and argument Effect flip the containing sign, result Effect and result preserve
it. Keeping those signs is a different graph construction from P. Nothing in
this packet establishes how signed SCCs should project to the parent/copy
equality condition, or which such expansion is semantically required.

Actual Lambda construction in `lib.rs:11233` supplies a negative argument,
negative entry Effect, positive returned Effect and positive result; it also
submits entry/body Effect lower bounds to returned Effect, then Function lower
to the definition root (`:11342`). Actual Apply construction lives in
`shadow_apply.rs:1331`, reached through the candidate source schedule: it builds
a negative demand from positive argument/argument Effect and negative invocation
Effect/result, and submits `callee <: demand`. These facts authenticate the
four-port shape and direction, without proving complete Call meaning or source
reachability of the scalar discriminator.

## Allowance/Support tails and kind separation

P includes both `Allowance(view)` and `Support(view)` as distinct Effect nodes,
and adds `view-node -> EffectRow(tail)` when the view has a tail
(`candidate_intrusion.rs:440`, **Dependencies::intern**). The same view ID does
not identify the two endpoint tags. Closed views have no tail edge. Concrete
Contribution/AnnotationMember endpoints, scalar leaves and extremes are not
interned as SCC vertices.

For the usual negative bound `e <: Allowance(A,t)`, storage gives
`e -> Allowance(A,t) -> t`. This records the wrapper's tail reference. It is
not an unconditional scalar constraint `e <: t`: an allowed concrete atom may
be discharged without reaching the tail. `candidate_check_effect_operand`
(`candidate_effect.rs:919`) forwards a Contribution/AnnotationMember to the
tail only when it is absent from the allowed list; without a tail it records
a mismatch. The contextual owner may separately discharge registered
Allowance checks (`candidate_context.rs:2733`), so this audit does not erase
their filters, scope, attachments or context into plain subtype semantics.

For the usual positive bound `Support(A,t) <: e`, storage instead gives
`e -> Support(A,t) -> t`; the initial outer relation has the opposite direction
in C. If replay compares Support with an upper endpoint `u`, the concrete
operand owner expands it into `AnnotationMember(view,i) <: u` and `t <: u`
(`candidate_effect.rs:895`). In particular, replay against an existing upper
bound can make an actual tail-to-upper relation, whose physical orientation
again depends on the receiving levels. Tail occurrence is not that generated
relation. Positive/negative extrusion remaps a view with the remapped same-kind
tail (`candidate_extrusion.rs:180`); capture incidence is additional retained
metadata, not an independently inserted reverse SCC edge.

The paired formal construction stores Support on positive ports and Allowance
on negative ports (`candidate_effect.rs:1566`); composed-negative annotations
may return the scoped tail directly (`:1527`). A variable-only computation
allowance also uses the tail directly (`:1329`). Therefore an audit that only
counts wrapper nodes misses authentic direct-row paths.

Reversing every stored lower-bound edge would repair the displayed scalar
comparison with C, but that change alone is not a proved semantic repair.
Function containment still needs an interpretation of signed contravariant
ports; it is not a collection of scalar inequalities to its children.
Support-to-upper replay expands into tail/member inequalities, whereas an
Allowance check may discharge an allowed member without any tail inequality.
One unconditional wrapper-to-tail edge cannot encode those two operational
roles as the same directed subtype rule. The intended dependency relation and
its preservation theorem must supply that distinction before any proposed
lower-edge inversion is justified.

Within the audited SCC construction, Value Function nodes may point into Effect
ports, but Effect rows/views point only to Effect vertices. Thus there is no
return path from Effect to Value in this graph construction, and no mixed-kind
SCC. This is an adjacency characterization, not a theorem that effect semantics
have no dependencies on Value payloads or contextual interfaces.

## Evidence limits and recommended action

Established here by static reading: the branch-specific one-sided storage,
physical edge orientation, port polarity/dispatch directions, wrapper-tail
edges, and selected same-component merge condition. The two-row SCC mismatch
is an elementary derivation conditional on the explicitly defined C and stated
empty-state hypotheses. It is not a reviewed theorem about the intended
semantic graph, an Oracle comparison, or a source-qualified counterexample.

There is no executable oracle in this packet. Reading independently owned
generation, storage, dispatch and SCC consumers supplies source correspondence;
all are still the current compiler implementation, not an independent semantic
oracle. No random seeds, finite enumeration ranges, model mutations or benchmark
samples apply. No builds/tests/probes ran. Uncovered: authentic source generation
of the exact opposite relation for a parent/copy pair; all-context complete Call
and effect hygiene; scheme restoration reachability; rollback/replay lifecycle
invariants; correctness/completeness/principality of any selected SCC graph.
Neither the number of inspections nor a numeric rank argument closes those
premises.

Recommended next action: the primary should use this explicit discriminator to
pin the existing intended dependency relation with its semantic/proof owner,
then request a source-qualified trace or proof that P preserves exactly the
parent/copy SCC condition needed by that relation. If C is not that relation,
state the actual relation and test this same witness against it. Do not schedule
an edge-orientation compiler repair from this note alone.

## Dependency snapshot, checks and commit packet

All listed dependencies were compared with the pinned baseline using
`git diff --name-only <baseline> -- <exact dependency paths>`; no dependency
changes were reported. SHA-256 snapshot:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` | `61e30f6fc52097ac8a3be3577284d45baa27ab528c4a7f109e3bfcedb405fd46` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/term.rs` | `75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Commands: bounded `rg`, `nl -ba ... | sed -n ...`, `cat` of governing rules and
sections; SHA-256 and exact dependency-diff checks. The leased note's trailing
whitespace search returned no matches. Resource use: no Cargo,
compiler, benchmark or search process; reads complete in subsecond tool calls;
aggregate CPU, peak memory and exact wall time unmeasured. Static investigation
remained within the assigned 30-minute bound. No broad source search was
completed or claimed.

Commit packet:

- Exact leased/changed path:
  `notes/progress/2026-10-11-intrusion-scc-dependency-orientation-audit.md`.
- Baseline SHA: `c8c62f473028d7684813e83284cc228b28a09831`.
- Changed dependency hashes: none observed; snapshot above.
- Review status: frozen, unreviewed research-only characterization; independent
  review pending. Producer has stopped writing before submission.
- Checks already run: static source/owner correspondence, exact dependency
  baseline diff, SHA-256 snapshot, leased-note trailing-whitespace check;
  no runtime tests or executable model.
- Proposed checkpoint commit message:
  `research: audit intrusion SCC dependency orientations`.
- Shared-record deltas intentionally left to primary/curator: record the
  physical-vs-constraint SCC distinction, unresolved graph-meaning premise,
  exact two-row/parent-copy discriminator and next owning evidence; preserve
  the parent semantic/proof gate as OPEN. No shared status/index/design/question
  bundle has been edited.
