# Odd/even after the two qualified equalities: fixed native ground model

Date: 2026-10-12
Status: reviewed conditional research; constructive finite satisfiability
derivation; native canonical-merge implementation correspondence remains OPEN
Yulang baseline supplied by primary: `06430602372f7c94ca8cba362fd360a728388ffa`
Reference baseline supplied by primary: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output lease: this file only; leaf, no delegation

## 1. Frozen statement and scope

Use exactly the integer reference term, constructors, original bound store,
source resolutions and local publication order in the frozen
[native derivation](2026-10-12-cross-level-odd-even-simple-sub-derivation.md)
§§1–5. The original source remains:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

O/E are distinct source definition Values; a/b are distinct formal Values.
Inner n resolves to b, outer n to a, inner odd to O, and final even to E.
The outer recursive type row o remains monomorphic throughout its initializer.
E publishes inside that initializer at boundary 1; O publishes at boundary 0.
No source root, formal, provider, or independently allocated use is identified.

Fix the completed native store at the end of the pinned trace, before a fresh
external use of O. Fix the actual polar extrusion pairs `(C,T,+,target=1)` and
`(D,R,-,target=1)`. For this packet only, assume the actual event endpoints
are `(E,O)`, so the approved O/E root SCC qualifies this one occurrence.
Impose precisely `C=T` and `D=R`. This does not establish that any source
constructor emits the assumed endpoints. Freshening is not another extrusion.

**Claim and quantifiers.** For this fixed term, fixed primitive objects I=int
and K=bool, fixed allocation and complete generated native constraints, there
exists one joint ground substitution satisfying all constraints after these
two equalities, with root o assigned `I -> K`. Injective renaming of fresh row
identities changes nothing. This is a fixed-instance class-B discriminator
and a concrete class-A constraint instance, not an all-source preservation,
soundness, required-principality, or arbitrary-continuation theorem.

The required conclusion concerns all 21 native rows, all eleven App demands,
the two recursive RHS completions, original extrusion links, the already
allocated E-use frame, and the specified boundary-0 fresh use. It does not
choose separate marginal witnesses. Original overloaded source elaboration,
complete Call/effect obligations, original scoped strategies and independent
public principal criteria remain at their original gates. This pure reference
term has no attachment/provider/witness/residual representation that could
discharge those obligations.

The claim class is a constructive finite constraint theorem awaiting fresh
independent review. Its optional operational realization below is explicitly
conditional on level closure; no implementation or theorem status is promoted.
Falsifier: an actual generated constraint evaluates to a failed comparison,
or the stated leveled quotient fails a native level/generalization rule.

Governing sections: top-level inference principles §§1–5; parent-copy decision
“Selected operation and compiler responsibility,” “Value-reference SCC
clarification,” and “Definition-root Value ownership”; value/type association
“Approved extrusion-event qualification” and “Implementation and proof
boundary”; Source Generalize §§2–4. Native storage and copying rules come from
reference `Typer.scala:48–83,88–156,166–188,199–227`, not the successor code.

## 2. Complete fixed native store

Let F(X,Y) mean Function(X,Y). L/U show distinct members, retaining self bounds
after quotienting where present. Lists may contain repeated members in the
actual trace; every repeated constraint has the same check below. The native
owners are `typeLetRhs` (recursive roots/publication), `typeTerm` Lam/App
(formals/demands), `constrain` (storage and replay), `extrude` (the two polar
copies), and `freshenAbove` (the one unsigned E-use map).

| Row | Original level | L | U |
| --- | --- | --- | --- |
| o | 1 | F(A,S) | F(C,D) |
| A | 1 | I | I |
| e | 2 | F(B,V) | empty |
| B | 2 | empty | I |
| j | 2 | K,D | V |
| P_le | 2 | F(I,K) | F(I,G) |
| G | 2 | K | K |
| H | 2 | F(j,F(j,j)) | F(K,Q) |
| Q | 2 | F(j,j) | F(R,V) |
| P_sub | 2 | F(I,I) | F(I,T) |
| T | 2 | I | C |
| R | 2 | D | j |
| V | 2 | K,D | empty |
| C | 1 | I | A |
| D | 1 | K | S |
| e' | 1 | F(B',V') | F(T_outer,S) |
| B' | 1 | I | I |
| V' | 1 | K,D | S |
| P_outer | 1 | F(I,I) | F(I,T_outer) |
| T_outer | 1 | I | B' |
| S | 1 | K | D |

The eleven App result rows are P_le/G/H/Q/P_sub/T/R/V/P_outer/T_outer/S.
j is the one fresh builtin-if variable. The remaining rows are the recursive
roots/formals, the two extrusion copies, and e'/B'/V' from the one E-use map.
In particular C's parent is subtraction result T, not formal B.

The original recursive Call demand is `o <: F(T,R)`, transported by negative
extrusion to `o <: F(C,D)`, with retained links `T <: C` and `D <: R`.
The original conditional demands `R <: j` and `j <: V` are active, not merely
stored opaque conditions. `D <: j` and `D <: V` were placed as low rows in
high rows' lower lists; no high upper on D existed before equality.

This table follows the cited trace and the actual reference guarded cases:
upper insertion replays all current lowers (`:115–117`), lower insertion
replays all current uppers (`:118–120`), and Function comparison reverses the
domain and preserves the codomain (`:106–108`). It includes the outer delayed
replay from o's new F(A,S) lower against its earlier F(C,D) upper.

## 3. Exact quotient and every newly activated comparison

Write X=[C=T] and Y=[D=R]. Canonical rewriting substitutes X/Y in every
occurrence without any additional row equality. Unioning both bound sides
gives:

```text
X: L={I},   U={X,A}
Y: L={K,Y}, U={S,j}
o: L={F(A,S)}, U={F(X,Y)}
P_sub: L={F(I,I)}, U={F(I,X)}
Q: L={F(j,j)}, U={F(Y,V)}
j: L={K,Y}, U={V}
V: L={K,Y}, U={}
V': L={K,Y}, U={S}
S: L={K}, U={Y}
```

Other rows retain §2's bounds. The self upper on X is the retained T<C link;
the self lower on Y is the retained D<R link. They impose reflexive constraints,
and may be skipped by an identity comparison without deleting their provenance.

The full new cross-product at X is `I <: X` and `I <: A`. At Y it is
`K <: S`, `K <: j`, `Y <: S`, and `Y <: j`. To close the latter constraint
through j's retained upper `V`, explicitly replay j's own lower/upper
cross-product after canonicalization: `L(j) × U(j)` contains `Y <: V` (and
`K <: V`). This is a third-owner replay at j; it is not generated by the
single call `constrain(Y,j)`, whose left-variable case only replays Y's
lowers against j. Thus the distinct-member closure adds V to U(Y); it adds no
new equality and needs no new polar extrusion copy when the level certificate
in §5 holds. All K lowers are already present at their destinations. The
reference comparison cache ends repeated variable pairs. This is a finite
explicit replay derivation with its owner and schedule stated, not an
assumption that stored constraints will eventually activate.

## 4. One simultaneous ground substitution and finite verification

Define one substitution σ on the original identities (the repeated ground
values do not identify their allocated frames):

| Rows | σ |
| --- | --- |
| A,B,B',C,T,T_outer | I |
| D,R,j,G,V,V',S | K |
| o,e,e' | F(I,K) |
| P_le | F(I,K) |
| P_sub,P_outer | F(I,I) |
| H | F(K,F(K,K)) |
| Q | F(K,K) |

This lists all 21 rows. In particular σ(C)=σ(T)=I and σ(D)=σ(R)=K, so both
selected equalities hold jointly. Each primitive comparison uses the same
I/K object as in the original constructor, matching reference identity success
at `Typer.scala:93`. Ground Functions compare by the actual two children.

Every original direct App or recursive-completion demand checks as follows:

| Actual constraint | σ check, using Function variance |
| --- | --- |
| F(I,F(I,K)) <: F(B,P_le) | I<:I; F(I,K)<:F(I,K) |
| P_le <: F(I,G) | I<:I; K<:K |
| F(K,F(j,F(j,j))) <: F(G,H) | K<:K; F(K,F(K,K))<:itself |
| H <: F(K,Q) | K<:K; F(K,K)<:itself |
| F(I,F(I,I)) <: F(B,P_sub) | I<:I; F(I,I)<:itself |
| P_sub <: F(I,T) | I<:I; I<:I |
| o <: F(T,R), and its transported F(C,D) demand | I<:I; K<:K in both demands |
| Q <: F(R,V) | K<:K; K<:K |
| F(B,V) <: e | F(I,K)<:itself |
| F(I,F(I,I)) <: F(A,P_outer) | I<:I; F(I,I)<:itself |
| P_outer <: F(I,T_outer) | I<:I; I<:I |
| e' <: F(T_outer,S) | I<:I; K<:K |
| F(A,S) <: o | F(I,K)<:itself |

The table contains eleven App demands plus the two RHS completions. The
remaining stored/replayed comparisons are exhaustively grouped by their
owners; a bound itself is lower<:owner or owner<:upper:

| Owner(s) | All lower/upper intersections after quotient and replay |
| --- | --- |
| o | F(A,S)<:F(X,Y), giving X<:A and S<:Y: I<:I and K<:K |
| A,B' | I<:I |
| X | I<:X and I<:A: I<:I |
| Y | K<:S,j,V and Y<:S,j,V: K<:K |
| S | K<:Y: K<:K |
| j | K<:V and Y<:V: K<:K |
| V' | K<:S and Y<:S: K<:K |
| P_le | F(I,K)<:F(I,G): I<:I and K<:K |
| G | K<:K |
| H | F(j,F(j,j))<:F(K,Q): K<:j and F(j,j)<:Q, both ground reflexive |
| Q | F(j,j)<:F(Y,V): Y<:j and j<:V, both K<:K |
| P_sub | F(I,I)<:F(I,X): I<:I and I<:X |
| P_outer | F(I,I)<:F(I,T_outer): I<:I and I<:T_outer |
| T_outer | I<:B': I<:I |
| e' | F(B',V')<:F(T_outer,S): T_outer<:B' and V'<:S |
| e,B,V | No lower/upper cross-product; their individual bounds also evaluate reflexively |

For every individual bound, σ(owner) equals σ(bound); consequently neither
an empty intersection row nor a repeated stored member hides an unchecked
condition. The original extrusion links become I<:I and K<:K. The delayed
outer replay and all new merge replays are in the second table. There is no
comparison K<:I or I<:K. Thus σ is a model of the entire fixed post-equality
system and σ(o)=F(I,K), proving the frozen finite existence claim.

## 5. Levels: ground model, necessary quotient closure, and owning seam

The substituted ground model has level 0 everywhere and is well scoped at
both boundaries. This fact proves satisfiability; it is not permission for
the inference algorithm to select σ eagerly or ground its store.

For a mutable canonical quotient, preserving the reference invariant
`level(bound) <= level(owner)` (`Typer.scala:221–227`) requires a separate
level certificate. Choose representative levels min(1,2)=1 for X and Y,
retaining all other original levels initially. X is lawful: its bounds are
I(level 0), X and A(level 1). **Y initially is not lawful:** inherited upper
j has level 2 while Y has level 1. This is the first precise contradiction to
the raw-minimum-merge representation, not a contradictory type constraint
or a source untypability result.

The least downward closure required by this fixed bound graph lowers j to 1
because it occurs in U(Y), and lowers V to 1 because it occurs in U(j).
U(V) is empty; its lowers K/Y are already at most 1. Nothing else must lower.
After the §3 replay U(Y)={S,j,V} remains lawful. All other rows keep their
levels, and every payload obeys the invariant:

```text
level 1: o,A,X,Y,S,j,V,e',B',V',P_outer,T_outer
level 2: e,B,P_le,G,H,Q,P_sub
level 0: I,K and all substituted ground types
```

H's F(j,F(j,j)) and Q's F(Y,V) payloads now have level 1, below their level-2
owners. e's F(B,V) has level 2 due to B, matching e. All other payloads are
immediate from the tables. This is a finite necessary closure certificate
and a sufficient leveled realization of the fixed constraint quotient; it
adds no equality, source restriction, or changed binder. Selecting and proving
a general production level-closure algorithm is outside this lease.

The actual Yulang owning merge is `candidate_intrusion.rs::merge_candidate_rows`
`:513–606`: append both bound sides, take minimum levels (`:579–589`), redirect
the forest, canonicalize contextual bound evidence, and replay every retained
lower (`:592–605`). Its insertion helper at `candidate_extrusion.rs:399–495`
canonicalizes endpoints and appends the selected side; its replay helper
`:763–807` enumerates opposite bounds and drives their replay. The inspected
`candidate_context_canonicalize_bounds` at `candidate_context.rs:3125–3150`
transports relation/witness evidence. These bodies supply no recursive native
level lowering of j/V. They also do not establish the original source event
endpoints; the qualification mismatch is already recorded by the governing
value/type clarification.

This is a narrow static ownership observation, not a reachable Y3 failure:
the actual successor has additional representation/consumer rules, and this
note constructs no source-to-candidate store bridge. Nor does it prove absence
of relevant later level handling outside the inspected methods. The finite
model is established; a claim that the live merge preserves the native
leveled-store invariant at this seam remains OPEN pending its actual owner.

## 6. Both original generalization frames and the specified fresh use

At the original E publication, e/B/V have level 2 while D has level 1.
The pinned `freshenAbove(1,e)` allocates e'/B'/V' at ambient level 1 with
one memo, copying both sides and retaining D. This is exactly §2's E-use
frame; it is not regenerated after equality. The quotient rewrites retained
D to Y in both original V and previously allocated V'. It does not equate
e with e', B with B', V with V', or either root with a source Value.
σ assigns both frames simultaneously and validates their complete constraints.
In particular both `V <: ...` and `V' <: S` use the same shared Y, with
σ(Y)=K; an independent marginal choice for each frame was not made.

The level certificate in §5 concerns a late equality operation at the frozen
completed-store cut. On any later E use, a lawful map at boundary 1 copies
e/B and stops at the now level-1 V (including its Y lower), so that shared
constraint remains shared. It cannot retroactively turn the already allocated
V' into V. Earlier intrusion scheduling could change this allocation trace;
this note proves neither scheduling equivalence nor a cache/recapture policy.

At O publication boundary 0, the reachable quotient graph, following both
bound sides, contains exactly o/A/S/X/Y/j/V. All seven have level 1 after
the level certificate. A final `freshenAbove(0,o)` therefore copies those
seven rows to level 0 with one unsigned memo; self bounds and the shared
Y/j/V cycle use the corresponding single copied identities. The original
e/B and the E-use e'/B'/V' are not reachable from this root and are not
silently merged into that frame. Assign the seven copied rows by σ of their
originals. Every copied bound remains satisfied and has level 0. A fresh
int Call adds `o_new <: F(I,Z)`, whose real function replay checks I<:I and
K<:Z; extending this same model by Z=K satisfies it. An additional independent
map remains independent; aliases of this one map share it. This is a check
of the specified fresh-use construction, not arbitrary-client principality.

The root's positive compacting route still sees only o's F(A,S) lower,
A's negative I upper and S's positive K lower. The new Y uppers do not occur
on this selected route. Thus the pinned simplification argument still gives
the required `int -> bool` display; independently, σ already supplies its
ground instance. No assertion about a full principal public Yulang scheme
follows from this fixed native display.

## 7. Dependencies, checks, omissions and handoff

SHA-256 snapshots, captured by static `sha256sum`:

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-12-cross-level-odd-even-simple-sub-derivation.md` | `5a4d89e1c22b553767a6e6789199ec7ef54cafd96216bd1c6b00147d1a1672ad` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Reference `shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference `shared/src/main/scala/simplesub/TypeSimplifier.scala` (trace dependency) | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |

Baseline commit identities are primary-supplied provenance; no Git command
verified them. Actual operative file pins are the hashes above. The earlier
trace's own historical baseline is retained in that file, without replacing
this packet's baseline. No dependency file was edited.

Checks: static `cat`, bounded `rg`, `sed`, reference `nl -ba`, dependency
SHA-256 capture/recheck and artifact text inspection. The first guessed
candidate path under yu-hir was absent; the actual owner is yu-solver. No
execution, solver/search/checker, test, build, benchmark, Git operation,
subagent dispatch or external contact occurred. This is one handwritten
derivation and one small required level-closure calculation, covering 21
original rows, eleven Apps, two RHS completions, one extrusion event/two
equalities, one already allocated E frame and one boundary-0 O frame.
Only lightweight static command processes ran; no heavy process, timing
sample or machine-resource reservation. CPU/RSS and reasoning wall time were
not measured; the assignment bound was 20 minutes, static reads only.

Requested runtime: normal proof leaf `gpt-6.1-sol/high`; observed effective
model/effort unknown because no runtime metadata was supplied. The callable
schema lists prover; `.codex/config.toml` registers it with Sol/high defaults,
and `.codex/agents/prover.toml` omits model/effort pins. This does not establish
an observed override or hot reload. No escalation was requested.

Review: fresh independent `compiler_referee` PASS for the fixed finite model
and level certificate, with no blocking or major finding. Its minor finding
required making the third-owner replay schedule explicit in §3; this wording
repair is closed by primary inspection and `git diff --check`. The review does
not cover source admission, endpoint construction, production merge behavior,
or parent theorems. Reviewer identity:
`/root/odd_even_intrusion_model_review`; effective model/effort unknown.

Unverified scope: original source elaboration/admission and event endpoints;
live canonical merge's level/generalization handling; arbitrary future
constraints; earlier scheduling/cached-frame recapture; complete Call/effects;
global preservation, soundness, required principality and F5 cutover. All remain
with the primary's existing parent gates. No theorem is independently reviewed
or self-certified here.

One next action: independently review this finite model and the exact native
level seam, then route the source-qualified leveled-merge bridge to its owning
construction/consumer gate. The missing premise is the actual operation's
preservation of the native leveled bound store and allocated frames, not another
ground compatibility witness. That is class A/B at its owner; no third
equivalent model note should substitute for it.

Commit packet:

- Exact changed/leased path: `notes/theory/2026-10-12-odd-even-intrusion-ground-model-proof.md`.
- Baseline: `06430602372f7c94ca8cba362fd360a728388ffa`; direct dependency hashes
  as above; no detected dependency change in the final recheck. Pinned-commit
  equality and integration belong to the primary.
- Review: fixed finite model reviewed; explicit third-owner replay wording
  repair closed by primary; parent theorem remains OPEN.
- Checks already run: complete finite direct-demand/bound/replay derivation,
  required level closure, both frame checks, static owner inspection and hashes.
- Proposed one-line checkpoint: `research: derive odd-even model after qualified intrusion`.
- Shared-record deltas left to primary/curator: record finite post-equality
  solvability of this native integer instance; retain assumed `(E,O)` endpoint
  qualification; distinguish the explicit level-closure certificate from the
  actual merge bridge; retain original source, soundness/principality, complete
  Call/effects and production gates OPEN. No shared record was edited.
- Writes stop on handoff; no Git action or self-certification.
