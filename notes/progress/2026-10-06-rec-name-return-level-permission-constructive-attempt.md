# Constructive level invariant for recursive member-use extrusion

Date: 2026-10-06
Status: frozen, independently reviewed research-only source characterization and conditional derivation
Independent review: compiler_referee found no BLOCKING, major, or minor findings in the coupled level-invariant component; law (L) remains open.
Baseline: `62560fbbc2d69971a80afec95fd34858c763024b`
Exclusive write lease: this file only
Method: static production-owner audit and induction on successful owner transitions
Implementation authority: none

## Objective, governing sections, and result boundary

Investigate law (L) in the reviewed contextual valuation bridge for one
incoming use of either member of `my f x = g; my g y = f`. Its exact value
tasks are `F²(ρ)≤ρ`, `ρ≤Top`, and `F²(ρ)≤cu`, where `cu` is the existing
occurrence row. Preserve the selected language meaning and the entire caller
assignment.

Governing inputs are `tasks/current.md`, “Objective and authority”, “Closed
decisions”, and the recursive name-return paragraphs at lines 479–512;
the contextual valuation note, P1–P4, “Exact transition correspondence”, and
“Extrusion, source permissions and diagnostic ownership remain explicit”;
the pure production reduction, “Exact named scheme and incoming-use
reduction” and “Smallest residual H4 premise”; and the member scheme bridge,
H1–H4 and “Source audit”. The three assigned rules were read in full.
`notes/design/INDEX.md` was used only for locators. The redesign charter
§§1–4, 22–23 governs the F5 comparison boundary and the selected existential
guard/variable-only level direction. F5 §23 describes the legacy level and
extrusion owners, without selecting successor semantics.

**Result:** the inspected creation/insertion/aging owners support an installed
graph invariant that justifies the already-aged-row skip. An aged holder
with a younger descendant cannot be produced by those successful owner
transitions from empty rows. This closes a structural premise left open by
an arbitrary-inventory treatment. It does not establish source law (L).
Current production collection supplies an additional narrow fact: all
production-allocated rows and frozen use levels are one, so this particular
production incoming route does not change row levels at all.

The primary confirmed before dispatch that tracked worktree inputs were
byte-identical to the supplied baseline. No Git command was used by this
producer. The hashes below freeze the actual read inputs. Candidate RecGroup,
the regular-tree carrier, and F5 remain comparison material. No question
bundle or new semantic decision was consumed.

## Exact owners and hypotheses

Locations refer to the pinned `crates/yu-solver/src/lib.rs`.

| Owner | Relevant creation or mutation |
|---|---|
| `VariableBounds` / `EffectBounds`, :3701 / :3712 | Default rows contain empty direct adjacency and exact bound vectors. |
| Session startup, :9470–9527 | Collected value/effect components and parameter rows receive empty bounds and level one before admission. |
| `fresh_value_at_level`, :9550; `fresh_effect_at_level`, :9581 | Append a new empty row at the supplied level, with a fresh ordinal and zero mark. |
| `constrain_live`, :11059, structural/row branch :11134–11151 | Extrude the structural endpoint to its receiving row's current level before calling `apply_value_task` to store the bound. |
| `apply_value_task`, :12071, row/row branch :12077–12121 | Extrude both endpoint rows to their minimum level, then store paired direct lower/upper adjacency. |
| Same owner, :12183 / :12251 | Store exact non-variable lower/upper after the caller's extrusion. |
| `apply_effect_task`, :10853–11026 | Apply the dual effect discipline: age both direct endpoints to minimum before paired adjacency; extrude a non-row bound before storage. Current non-row effect endpoints are leaves. |
| `extrude`, :10670–10824 | Traverse Function fields and installed row bounds/adjacencies; lower younger rows; skip marked or already-aged rows before descending. |
| Collection, :1126–1135 | Freeze each actual `DefinitionUse` with `use_level: 1` and its existing occurrence component. |
| Instantiation, :14527–14658 | Q/R rows are fresh at that frozen use level; restore bounds, then route the substituted predicate into the existing occurrence row. |
| `route_incoming_inner`, :14877–14888 | Select finalized member scheme and the existing `use_value_component`; no replacement target allocation. |
| `LiveVariableMetadata`, :749–757 | Records only `Collected`/`Fresh` origin and `non_generic`; no existential introduction level or source permission token is specified here. |

H0. Handles, row indices and Function fields remain valid and retain their
identities; constructor syntax is finite and acyclic. Installed row cycles
are allowed. The relevant live graph is finite.

H1. Rows start empty and subsequent installed bounds/direct adjacency are
created through the listed owner paths. An arbitrary caller inventory,
test-injected vector write or a direct private `apply_value_task` invocation
that bypasses its extrusion caller is not an H1 trace.

H2. Observe only successful, completed owner transitions. Extrusion has no
interleaved graph mutation; every push and journal reservation succeeds and
the stack drains. There is no abandoned operation, partial observation,
rollback, row retargeting or unowned mutation in this theorem.

H3. For the additional current-production specialization, use collection's
actual `DefinitionUse` construction and the current production allocation
call sites, rather than a privately supplied use record or test helper.

These are explicit operational premises. H1–H2 can describe heterogeneous
levels allocated through the private row helpers; that larger class is not
claimed source-reachable. H3 names a narrower actually collected production
class. Neither class supplies an interpretation of source admissibility.

## Installed graph invariant and extrusion induction

Define the graph on value and effect rows. A row has outgoing dependencies
to its direct lower/upper neighbors and to every row appearing syntactically
in either side of its installed exact bounds, traversing all four Function
fields. Atoms contribute no dependency. Write `λ(v)` for a row's level.
The invariant at completed mutation boundaries is

```text
E:  v → w implies λ(w) ≤ λ(v).
```

Because direct adjacency is paired, E forces direct neighbors to have equal
levels. Exact-bound dependencies need only be nonincreasing. Induction on
path length gives `λ(w)≤λ(v)` for every row reachable from v, with no
acyclic-row assumption. This is stronger than a statement about only the
immediate Function child.

First prove an extrusion lemma on a fixed graph satisfying E. For any root
endpoint e and target t, a completed `extrude(e,t)` changes precisely the
reachable younger rows:

```text
λ'(v) = min(λ(v),t)  if v is reachable from e;
λ'(v) = λ(v)         otherwise.
```

Here reachability includes the root row itself and the syntax children of a
constructor root. A row initially at level at most t may be skipped because
E gives every descendant level at most its initial level, hence at most t.
No descendant then needs lowering. A row initially above t is lowered to t
on its first pop and its outgoing dependencies are scheduled. Reencountering
it under the same generation requires no additional work: all its outgoing
dependencies have already been scheduled. Successful pushes and eventual
stack exhaustion are essential to this statement. Generation wrap resets
marks; the journaled `u32::MAX` case returns failure instead of completing.

E need not hold after each individual stack pop: a lowered holder can have
an unprocessed younger child on the frontier. The proof therefore uses
pending scheduled dependencies and claims E only after successful stack
completion. It does not circularly assume E in the temporarily lowered
state to justify that frontier.

For an old row skipped because its *current* level is at most t, either its
initial level was already at most t (the preceding path-length argument),
or this invocation already processed it (the frontier argument). Extrusion
never writes a level below t. These exhaust the skip cases. Finiteness and
marks give termination for finite row graphs and acyclic constructor syntax,
subject to successful fallible growth; no resource-limit guarantee follows.

The final pointwise formula preserves E. If a reachable holder has an
outgoing dependency, the child is reachable too, and applying `min(-,t)` to
both preserves the inequality. If the holder is unreachable but its child
is reachable, only the child's level may decrease, which also preserves E.

Now induct on the installed-graph owners:

1. Startup and fresh allocation preserve E because a new row has no
   dependencies and no existing dependency targets its fresh identity.
2. A structural bound is extruded to the holder's current level before
   storage. The lemma puts every row in that bound at or below the holder.
   Extrusion cannot lower that holder further: its level is already the
   target, even if the new payload mentions it. Installing the dependency
   therefore preserves E, including a recursive self-occurrence.
3. A direct row pair is extruded twice to the common pre-call minimum.
   Each call preserves E; neither writes below that minimum. Both endpoints
   end at the minimum, so installing both adjacency copies preserves E.
4. Effect owners apply the same argument. Decomposition and replay enqueue
   further constraints; each new installation again passes through its
   relevant extrusion owner. Duplicate/terminal/mismatch paths install no
   dependency and cannot break E. Term construction without installation
   adds no edge to the installed graph.

Consequently E is derived from creation and mutation rules under H0–H2;
it is not an assumed arbitrary inventory restriction. The familiar
aged-holder/younger-child pattern violates E and requires bypassing an owner,
a partially completed operation or an additional mutation rule. No new
arbitrary-inventory witness or equivalent toy probe is submitted here.

## Apply the invariant to the exact member-use target

The fresh recursive row ρ is empty at the frozen use level. Inserting
`Lu=P₀(Top−,P₀(Top−,ρ+))` as its own lower preserves E: the only live child
is ρ, already at the receiver level. `ρ≤Top` is terminal. Before `Lu` is
installed in `cu`, extrusion enforces `λ(ρ)≤λ(cu)`. Replays against existing
uppers may connect ρ to older caller rows; E and its proof cover those rows'
complete installed bounds and both adjacency directions. Freshness alone
does not isolate ρ from the caller, and the proof makes no such assumption.

Under H3 an even narrower invariant is `λ(v)=1` for every current production
row. Startup supplies it, and both production `fresh_value_at_level` call
sites are in instantiation and consume collection's frozen `use_level=1`.
The searched current production region contains no call to
`fresh_effect_at_level` and no call to `child_level`; their uses in the test
module starting at :16240 are outside H3. The only forward indexed level
writes found are extrusion's :10703 / :10793; their guards cannot fire when
both the row level and every receiving/minimum target are one. Thus the
exact current production member-use route changes no row level, including
replays through caller rows. This is a current producer characterization,
not a selected support limit or evidence for future nested/existential forms.

## Why source permission law (L) remains open

The contextual note's requested extension is

```text
R_initial(σ) ∧ F²(d)≤d ∧ d≤Top ∧ F²(d)≤σ(cu)
  implies [A_alloc(σ,d) iff A_final(σ,d)].                 (L)
```

E proves that extrusion performs the intended installed-graph lowering
despite the early skip. It says nothing about which semantic assignments
remain permitted when a level decreases. The exact missing premise is a
source admissibility rule relating a row's interpretation and scope evidence
to its level, together with preservation of that rule under each derived
comparison and lowering. Bounds may imply carrier inequalities under P1;
they do not imply this permission rule.

The selected charter §22 requires a generation-time guard for every derived
comparison involving an introduced existential, including replay and aliases;
§23 assigns levels to variables and leaves exact coverage/preservation open.
The inspected legacy row metadata does not identify such an existential's
introduction level or associate it with permission evidence. This observation
does not assert that the selected successor must add a rigid node or any
particular representation. It establishes that these legacy owners alone
do not supply the missing selected-semantic premise.

For H3, allocation-to-final level metadata is literally unchanged. If a
source bridge separately establishes that A depends only on that unchanged
level/scope metadata for this pure fragment and does not add a new permission
obligation, its preservation follows immediately. That is an additional
conditional premise, not a definition of A selected by this note. Current
production's all-one fact removes level *change* from that narrow bridge;
it does not establish admissibility, production realization of every candidate
target, coverage of the generation-time guard, or law (L) for P2's arbitrary
levels and broader source states.

No established source-permission theorem, accepted target-class definition,
diagnostic completeness, principal inference or production authority is
claimed. The useful reduction is: the already-aged skip has a constructive
owner invariant; the remaining blocker concerns the meaning and source
preservation of admissibility, rather than arbitrary younger descendants.

## Independence, coverage, failure conditions, and next action

There is no executable oracle. The graph theorem follows from observed
creation/mutation owners plus H0–H2, without the candidate regular-tree order
laws. Its application to the exact recursive tasks uses the reviewed prior
route audits; a denotational permission extension would still share their
candidate realization premises. A checker supplied E or an A transition rule
could test its consequences, but would not independently establish source
permission semantics. No source rule is inferred from a passing probe.

Coverage is symbolic over finite installed graphs produced by these owners,
including row cycles, both exact-bound sides, both direct adjacency copies,
nested Function fields and cross-kind row dependencies. The current-source
specialization is limited to collection/instantiation's existing level-one
producers. Seeds/ranges and enumerated case counts are inapplicable. No
mutation was executed; named falsifiers are storage without prior extrusion,
one-sided direct aging, later level increase, term retargeting, bypassed owner
writes and abandoned extrusion frontier. Any new such production mutation
invalidates the induction until audited.

Commands: `cat` for assigned rules; bounded `rg`/`sed` reads of the named
governing sections and production owners; `sha256sum` of scoped dependencies;
one final Python hash-stability and note-text integrity check. An initial
combined source capture was truncated; the relevant named sections were then
read in narrower captures. No whole-file/document audit is claimed.
No Git commands, compiler changes, tests, builds, semantic probes, formatting,
child agents or questions were used.

Resource use: one lightweight shell/Python process at a time, zero heavy
processes and zero compute searches. CPU time, peak memory and total wall
time were not instrumented; the assignment supplied no numerical caps.
The static-only, one-output, bounded-owner-path constraints were enforced.
Nothing remains running. Rollback/failure paths, test-injected inventories,
future nested/rigid/existential source production, arbitrary P2 targets and
the actual source admissibility relation remain unverified.

Recommended next action: obtain a source-level admissibility judgment for
the admitted pure member-use target class, then use E as the extrusion lemma
in its guard/preservation proof. Another arbitrary-level inventory checker
would leave that exact premise untouched.

## Frozen dependencies

SHA-256 hashes of read inputs, rechecked before submission:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
c168107cd143d85ca8b836b1ddc774def94972f81474292d37e003a69a4c0f49  tasks/current.md
d56f970490ec9e4699f55c47d1e037bbcfab00592b054c9b138d517b208ab9f0  notes/design/INDEX.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
f7351170386a2b832ccd5bfccec32ad46fab3c7ab6bf42b9387ea39f1ecae53b  notes/progress/2026-10-06-live-row-contextual-valuation-attempt.md
f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779  notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md
fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e  notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-rec-name-return-level-permission-constructive-attempt.md`.
- Baseline SHA: `62560fbbc2d69971a80afec95fd34858c763024b`, supplied and
  tracked-input equality confirmed by the primary.
- Changed dependency hashes: none during this lane; the eleven hashes above
  pin the read snapshot. Primary revalidation against integration HEAD is
  still required.
- Claim/review status: frozen, independently reviewed research-only source
  characterization and conditional graph invariant derivation; source law (L)
  remains open. The review covered both level-permission notes and the cited
  production owner paths, not source-denotation or failure/rollback proofs.
- Checks already run: scoped owner/authority reads, dependency hashes and final
  text/hash integrity check; no tests/builds/probes.
- Proposed one-line research-checkpoint commit message:
  `research: derive reachable extrusion level invariant for member uses`.
- Shared-record deltas intentionally left for primary/curator: record E and
  its successful-owner premises, the current production all-one specialization,
  and the residual source admissibility/derived-guard premise. Keep (L), source
  realization and target-class selection open. No shared task/index/theory,
  authority, manifest, lockfile, question or compiler path was changed.

Writing stops at submission of this frozen artifact. Any review repair requires
a returned finding and a renewed lease.
