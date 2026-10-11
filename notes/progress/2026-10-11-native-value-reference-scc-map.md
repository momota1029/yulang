# Native Value reference graph and intrusion correspondence

Date: 2026-10-11
Status: frozen, unreviewed research-only static source correspondence.
Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`, branch
`research/simple-sub-intrusion`.
Exclusive lease: this note. No compiler change, executable probe, build, test,
Git mutation, shared-record edit, or delegation.

## Objective and governing premise

Audit the current `settle_candidate_intrusion` adjacency against the primary's
accepted user correction: vertices are Value variables, and a directed edge
goes from a variable's value to a Value variable referenced by that value.
Child-to-parent and nephew-to-uncle references are permitted graph shapes.
An inequality `a <: b` is not itself an edge, and a parent record is not itself
an edge. This correction governs this packet even where older records describe
the edge meaning as undecided.

Exact governing sections are `rules/design-authority.md` “Authority order”;
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3 and
“Authority and integration”; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`
“Direct decision” and “Selected operation and compiler responsibility”;
`rules/research-lab.md` “One semantic baseline, explicit dependency invalidation”,
“Evidence quality and stopping unproductive loops”, and “Writes, artifacts and
review snapshots”; and `rules/git-concurrency.md` “Disjoint-file mode”.

Claim class: bounded static characterization of the pinned representation,
with an explicit conditional transfer of the previous rank argument. This is
not a proof that every intended source history is represented, that intrusion
is semantically adequate, or that any parent theorem can close.

## Actual payload ownership precedes graph interpretation

The persistent original reference is
`/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`. Its
`shared/src/main/scala/simplesub/Typer.scala:223` defines `Variable` with both
`lowerBounds: List[SimpleType]` and `upperBounds: List[SimpleType]`.
`Function(lhs,rhs)` owns its two child objects at `:209`.

The actual mutations distinguish reference direction from comparison direction:
`constrain` writes `lhs.upperBounds ::= rhs` at `:115–117`, or
`rhs.lowerBounds ::= lhs` at `:118–120`. In both cases the object whose payload
changes references the inserted object. Function comparison at `:106–108`
reverses the argument *comparison*; it does not reverse the stored Function
child reference. Extrusion writes parent bounds and copied bounds at
`:146–154`. Freshening copies both bound lists at `:166–185`.
This original source contains no parent-copy intrusion implementation and
cannot independently validate Yulang's added operation or effects.

The corresponding native representation is concrete:

- `lib.rs:734` defines `ValueEndpointKey`; a `ValueRow` names one live Value
  variable, while positive/negative Function endpoints name actual term nodes.
- `lib.rs:3968` defines `VariableBounds` with both direct row lists and both
  exact structural/leaf lists. `candidate_insert_bound_with_evidence` at
  `candidate_extrusion.rs:456–501` actually appends the inserted endpoint to
  the owner's selected list. These writes establish references independently
  of the later SCC scan.
- `term.rs:196–214` stores four Function child handles in `TermNode`.
  `BranchTermArena::positive_function` and `negative_function` at
  `:1126–1165` validate and intern those fields. The two Value children are
  argument and result; the other children are Effect ports.
- `lib.rs:11382–11411` resolves a component/live-variable child handle to a
  canonical Value row. Both variable polarities resolve to the same row
  identity; Function tags and live views still validate the requested polarity.

Thus the identification of owner-to-bound adjacency with references comes from
the independently inspected constructors and fields, rather than from an
assumption that physical lower/upper orientation defines the language.

## Edge-by-edge map

All native locators below are relative to `crates/yu-solver/src/`.

| Current adjacency in `candidate_intrusion.rs` | Constructor-owned reference | Disposition for the selected Value-variable graph |
| --- | --- | --- |
| Value row → direct lower row, `:391–403` | Owner's `direct_lower_rows` contains that row, inserted at `candidate_extrusion.rs:464–471` | Real outward reference. Reversing it to follow the inequality would misorient this reference. |
| Value row → direct upper row, `:391–403` | Owner's `direct_upper_rows`, inserted at `candidate_extrusion.rs:472–479` | Real outward reference. |
| Value row → exact lower/upper Function, `:404–413` | Owner's exact bound contains a Function term, inserted at `candidate_extrusion.rs:480–501` | Structural intermediary representing references inside that payload. |
| Function → argument Value port, `:445–468` | `TermNode` argument field | Real outward reference; opposite polarity chooses its endpoint view. Positive Function uses negative argument; negative Function uses positive argument. |
| Function → result Value port, `:445–468` | `TermNode` result field | Real outward reference; same polarity chooses its endpoint view. |
| Function → argument/result Effect ports, `:445–468` | Actual Effect child fields | Extra vertices/branches relative to Value-only SCCs; no reversed reference is introduced. |
| Effect row → its lower/upper Effect endpoints, `:415–438` | `EffectBounds` fields | Outside this packet's Value graph. All target kinds remain Effect. |
| Allowance/Support → Effect tail, `:440–443` | Retained effect view's tail field | Outside the Value graph; target is Effect-only. |
| Parent/copy metadata, `:477–486` | `Parent {copy,parent,polarity,target}` | Qualification/provenance only. No graph edge is added by reading this record. |
| Leaf endpoints, rejected by `Dependencies::intern`, `:622–637` | Value leaves contain no Value child | Omission is harmless for Value-variable reachability. |
| AnnotationMember endpoint, also excluded by `intern` | An Effect view can contain an Effect tail, independently visible in `candidate_scheme.rs:446–449` | An omitted Effect reference, not an omitted Value reference in the inspected representation. No Effect SCC adequacy claim follows. |

For the selected variable-only graph, expand each variable's immediate bound
payload through nested Function syntax, stop at each reached Value row, and
record that referenced row. Traversing that row's own payload is the next graph
edge, not an additional immediate reference from the original owner.

The current graph subdivides these reference edges with Function vertices.
Every path between Value rows can be partitioned at its row visits into exactly
those bound/Function reference segments. Conversely each segment has the
displayed path in current adjacency. Function nodes are immutable syntax
nodes; recursive paths go through rows (`candidate_scheme.rs:1109–1110`).
Therefore subdivision preserves reachability and SCC equivalence *between
Value rows*, even though the full graph's vertex set is larger.

Effect branches cannot introduce an extra path between Value rows: the scan has
no Effect-origin edge to a Value endpoint. Once a path enters an Effect node it
cannot return to Value. Function Effect ports consequently do not change Value
SCC membership. This argument is specific to the pinned adjacency; it is not a
source-wide theorem about future Effect payload constructors.

No omitted or misoriented Value reference was found among the inspected native
endpoint variants and mutation owners. Comparisons, contextual relation labels,
diagnostic parent edges, capture metadata and source-name provenance do not
add references unless an actual bound or term constructor stores a handle.

## Earliest actual additions and ancestry examples

For ordinary source Lambda construction, `admit_lambda_fact` obtains the actual
parameter and body Value handles (`lib.rs:11233–11260`), then constructs the
Function at `:11342`. This is the first payload constructor adding its Value
port references. The slot-2 comparison at `:11344–11362` is subsequently
drained; `candidate_apply_value` at `candidate_extrusion.rs:815–830` selects the
root row as lower-bound owner, and the physical insertion makes
`root → Function → parameter/body` reachable. Signature Functions similarly
construct the Value ports at `candidate_effect.rs:1398–1443`. A relation label
alone is not the insertion event.

For actual extrusion ancestry, `candidate_extrude` checks
`L(original) > target`, creates an empty fresh row, records its parent, and
inserts the source link (`candidate_extrusion.rs:83–124`). For positive
extrusion this is an upper bound on the original; for negative extrusion it is
a lower bound on the original. Both are the real reference `parent → copy`.
`retain_extrusion_parent` by itself adds no `copy → parent` reference.
Copied selected bounds are installed later by `Work::Bound` at `:308–324`,
after recursive reconstruction; those copied payloads can have other references.

A conditional `copy → parent` witness is just one installed direct bound
holding the parent's row, or a copied bound Function whose Value port holds
that row. The scan follows it without consulting ancestry. If the two retained
rows also have the real extrusion source link, they form a reference SCC.
This is a constructor-level discrimination, not an authentic source witness:
ordinary admission may orient storage toward the other owner, and extrusion
may replace the parent occurrence before installation.

For nephew/uncle references, suppose `C` and `U` are two recorded copies of
`P`, and `N` is a copy of `C`. If a selected bound of `C` contains `U` and
`L(U) <= target(N)`, `Work::Visit` returns `U` unchanged at
`candidate_extrusion.rs:85–87`; `Work::Bound` then installs `N → U`.
If the occurrence is inside a Function, reconstruction preserves its actual
port polarity and outward direction at `:325–355`. This is precisely a
nephew-to-uncle reference supported by the scanner and constructors.
If `U` instead has a higher level than the target, that same occurrence is
replaced by a polarity-specific copy of `U`; the new edge targets that copy.
The existence of the assumed selected bound in an authentic source history is
not established by this conditional construction.

Fresh-use reconstruction has a related real owner: it maps each local row to
a fresh use row and keeps each shared row (`candidate_scheme.rs:1008–1019`),
rebuilds Functions from the joint remap (`:1141–1157`), and physically restores
the captured owner/side through `:1227–1266` and
`candidate_extrusion.rs:673`. It can therefore install a fresh row's reference
to an older shared row. Fresh-use allocation itself creates no extrusion
parent record, so a pictorial nephew/uncle naming must not manufacture one.

## Revisit of the previous Value rank argument

The prior note
`notes/theory/2026-10-11-local-restoration-value-scc-preservation.md` §2 already
measures owner-to-both-bound references and outward Function ports. Its graph
premise agrees with the Value-row reachability just derived; it did not need
comparison edges. The user correction alone therefore does not refute that
argument. This correspondence is separate from its source preservation proof.

Write `H(ValueRow(v)) = L(v)` and
`H(Function(a,ae,re,r)) = max(H(a),H(r))`, with leaves zero. The exact required
premise is `H(bound) <= L(owner)` for every installed native Value bound,
preserved through every relevant source restoration and level change. Then:

1. Direct bound references descend or preserve level by this premise.
2. For a Function reference segment, both reached Value ports have ceiling at
   most the Function ceiling, including argument ports of opposite polarity.
   Reference direction remains outward. Nested Function induction gives the
   same inequality.
3. Effect detours cannot return to Value, as derived above.
4. Every retained original/copy pair begins with
   `L(copy)=target < L(original)` by the actual extrusion check. If these levels
   do not change before the first Value merge, `copy → ... → original` would
   contradict steps 1–3.

The relevant preservation owners were revisited, not assumed from ancestry:
row/row admission picks the higher-level owner at
`candidate_extrusion.rs:815–824`; row/Function dispatch extrudes at the receiving
row's level before applying at `lib.rs:12412–12454`; selected copied bounds are
installed only from the recursively reconstructed endpoint at
`candidate_extrusion.rs:308–324`. Native dispatch bypasses legacy destructive
row aging (`lib.rs:13744–13759`). Fresh restoration requires the *additional*
source premise that captured owners are local and shared rows' levels are at
most boundary `B <= use level U`; then remapped owners and local references
are at `U`, while retained shared references are at most `U`.
Those premises belong to the prior note §§3–6, including lexical/module
construction and all Value level/metadata writers. They are not established
merely by an SCC scan or by this packet's bounded reread.

Thus nephew-to-uncle references with a sufficiently low shared uncle coexist
with the rank premise. A true upward child-to-parent reference would violate
it; the selected graph definition allows that reference, while the previous
native-construction theorem claims the current writers do not produce it for
an unequal-level retained pair. Neither family terminology nor comparison
polarity settles that claim.

Authentic Value parent/copy SCC reachability: no new authentic source history
was constructed here. Conditional on the previous exhaustive writer/restoration
bridge remaining established, the corrected graph retains its native
nonreachability consequence. Without that bridge, authentic reachability is
unresolved by this audit. This does not prohibit the intended graph shapes,
justify disabling intrusion, or prove ordinary source inference complete.

## Evidence, frozen dependencies, and limits

Commands were bounded static `rg`, `rg --files`, `cat`, `sed`, `nl`, read-only
`git status`, `git rev-parse`, `git branch --show-current`, dependency-scoped
`git diff <baseline> -- <paths>`, and `sha256sum`. Direct dependency comparison
against the assigned baseline was empty. No randomized or exhaustive search
was run; seeds/ranges, mutations and executable oracle comparison are
inapplicable. Two initial guessed paths were absent (`simple-sub-reference/src`
and a `yu-constraints` crate); the subsequent actual path locators above replace
those guesses. Search completeness is confined to the named source owners.

The original reference is independent source evidence for ordinary bound and
Function ownership, but shares Simple-sub's level/variance conventions with the
candidate. It supplies no independent oracle for Yulang effects or intrusion.
The graph derivation fails if a new Value payload variant is not traversed,
an Effect-origin Value reference is added, source references exist outside the
inspected bound/term payloads, or canonical representatives lose retained
payload references. Rank transfer additionally fails if any actual writer or
level update violates its stated inequality/restoration premises.

One lightweight shell process at a time; zero Cargo/build/test/probe processes,
benchmark samples, Git mutations, or children. CPU/RAM peaks and exact elapsed
wall time were not measured. No explicit numeric wall budget was supplied;
the packet remained a bounded static audit. Review is pending and belongs to
the primary. Full source reachability, all abnormal-state reuse, semantic
adequacy of parent equality, complete Call, effects/hygiene, soundness,
principality, and production cutover remain outside this result.

SHA-256 dependencies:

```text
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615  crates/yu-solver/src/term.rs
3dfd8ba4b21b76ee434a6b30697c5197213eae0679b84b98a6908e8a512fe6c4  notes/theory/2026-10-11-local-restoration-value-scc-preservation.md
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Recommended next action: give the constructive proof lane this frozen
constructor/reference map and require it to settle the exact all-writer rank
premise or supply an authentic upward child/parent or nephew/uncle continuation;
keep the source and semantic parent gates distinct.

## Commit packet

- Exact leased path:
  `notes/progress/2026-10-11-native-value-reference-scc-map.md`.
- Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`; changed direct
  dependency hashes: none.
- Claim/review: frozen research-only static characterization and conditional
  rank transfer; unreviewed, no parent gate closure or implementation authority.
- Checks already run: named payload/constructor/adjacency reads, static producer
  and level-writer search, baseline dependency diff, SHA-256 capture. No tests,
  builds, probes, compiler execution, or independent review.
- Proposed checkpoint message:
  `research: map native Value references into intrusion SCCs`.
- Shared-record deltas left to primary/curator: record the selected Value
  reference graph and its constructor correspondence; replace old uncertainty
  about user-selected graph meaning without promoting semantic adequacy;
  retain rank/source reachability status with its exact remaining premise.
  No task/index/authority/theory map was edited.
