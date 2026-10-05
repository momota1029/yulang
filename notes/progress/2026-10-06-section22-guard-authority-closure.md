# Section 22 guard coverage: origin-relative structural insertion

Date: 2026-10-06
Status: Draft / unreviewed research / no authority
Method: constructive Authority-only consequences and minimal local residual
Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd` (primary supplied)
Branch: `research/simple-sub-intrusion` (primary supplied)
Exclusive lease: this file only; implementation authority: none

## Result and exact scope

The selected decisions determine direct forbidden comparisons, require their
derived/replayed forms to be checked, and require preservation of original
existential correspondence. They do **not** turn the actual lower bound
`B(z) <: z` into an equation `z = B(z)`, nor turn carrying `B(z)` into an
ordinary row into an actual comparison `z <: row`. These distinctions prevent
a false early closure through either rigid equality or Cartesian support K.

A genuine fixed-root specialization and the explicitly selected ground
narrowing can be rejected without K. Neither result classifies this pure
recursive instance or decides its four actual shapes. The remaining semantic
seam is an origin-relative preservation/permission law for one oriented
variable/structure insertion, instantiated at three receiving rows. A
conditional finite-trace proof uses that local law without requiring O's
blanket classification of every row as non-existential. The local law itself
is still unproved; this note neither defines source admissibility nor selects
which of its possible outcomes Yulang accepts.

## Sources and authority boundary

Paths below are relative to the repository root. Let C denote
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md`.

| Source | Consequence used |
|---|---|
| C §§1–2, lines 17–55 | F5 generalization/schemes are historical comparison material; soundness/principality precede final acceptance compatibility; original extrusion cannot be copied as successor meaning. |
| C §20, lines 549–568 | Open request names are rigid; check uniformly under declared interface/bounds and fixed captures; caller-private equations are not arm assumptions; aliases preserve the witness; dependent returned/stored roots keep joint binder correspondence; inference existentials and hidden request binders differ. |
| C §21, lines 597–601 | Complete Function subtyping and principal source inference remain proof gates. |
| C §22, lines 605–617 | Equal/older forbidden comparisons reject; actually derived comparisons re-enter the guard; the eventual `kappa <: Int` rejects. |
| C §22, lines 619–631; §23, lines 635–645 | No mandatory rigid IR or composite-level algorithm; variable-only levels; ordinary structural decomposition and variable/extrusion enforcement; complete coverage/preservation remain open. |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` §1, lines 18–38 | User-selected one inequality, oriented structural bounds and variable propagation; concrete successes do not compose into a transitive concrete preorder. |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` §4, Name rule | Copy a supplied interface with its source positions; do not infer a fresh existential introduction from Name copying. |

`notes/design/INDEX.md` locates these selected scopes; its labels do not promote
surrounding Draft constructions. The inspected operation-instance equality
kernel and F5 §§22–23 illustrate different algorithms, not additional
Authority. No free-term algebra, occurs-check policy, recursive carrier,
constructor level, source envelope, or support guard is adopted here.

## Close the consequences that do follow

1. **Direct variable guard.** Given an actual comparison involving a source-
   certified `Ex(a,l)` and a peer variable at level `<=l`, the selected guard
   rejects the forbidden comparison before commitment (C §22). Reaching it
   through aliasing or replay changes neither this obligation nor its result.
   This does not invent an identity/reflexivity exemption or an identity test.
2. **Derived structural guard.** Whenever an applicable ordinary structural
   rule actually produces such a variable comparison, the same rejection
   follows (C §§22–23). The constructor has no stored level. This consequence
   says nothing about whether a mismatched constructor/variable pair produces
   that child comparison; it has no matching constructor heads to decompose.
3. **Ground discriminator without K.** C §22 explicitly requires rejection
   of the derived `kappa <: Int`. K gives this shape no cross-support pair
   because Int has empty variable support. Therefore K **alone is insufficient
   as complete selected guard coverage**. This falsifier uses the selected
   example itself and assigns no level to Int. It does not extend the example
   to a blanket rejection of every ground endpoint, especially legacy Top.
4. **Fixed-root rejection without K.** In a real §20 opening, keep the
   declared admissible request instances and captured environment fixed. A
   body demand must work for each such instance. If a proposed equality or
   inequality fails at one admitted instance, restricting the opened name to
   its successful instances cannot repair the uniform proof. Reject that
   specialization. Proof: the failing instance remains in the unchanged
   declaration domain and refutes the demanded uniform obligation. This is
   exactly the fixed-capture/uniformity requirement, not a scope algorithm.

For point 4, a new equation `root=B(root)` fails if an admitted counter-instance
violates it. For the actual **directed** demand `B(root) <: root`, assume a
genuine §20 rigid opening, no declared assumption entailing that demand,
an admitted substitution `root:=Int`, and rejection of `B(Int) <: Int` by
the source inequality. Uniform checking then fails at that substitution,
without K. The admitted-Int and Function/Int-mismatch premises are explicit;
neither is proved by R storage or imported from legacy F5. If `B(root)<:root`
is instead a declared source bound, replay checks under that assumption and
this counter-instance argument is invalid. The source judgment must identify
**declared assumption versus new obligation**, not merely supply an Ex flag.
No rigid/constructor disjointness at every instance is inferred.

## Apply to the actual finite alias trace

Use `my f x = g; my g y = f`, followed by finitely many distinct unused bare
aliases to f or g. The source-guard note, “A source-produced target envelope”
and “Exact value replay closure”, lines 132–228, establishes the following
inventory for each incoming use, under its successful-owner premises:

```text
B(z) = PureFun(Top, PureFun(Top,z))
prefix: c <: R_h
q1: B(z) <: z      q2: z <: Top
q3: B(z) <: c      q4: B(z) <: R_h   (actual replay)
```

All collected/current rows and frozen use levels are one, as characterized
by the level-permission note, “Apply the invariant to the exact member-use
target”. This is an actual producer fact, not a chosen support envelope.
That note's E invariant justifies an equal-level extrusion skip; it proves
neither source permission nor the absence of introduced existentials.

q1 installs an oriented lower, not a fixed-root solution or equality. B has
a concrete outer Function head but contains z; it is not a ground term.
There is no Function/Function pair, actual `z <: c`, or actual `z <: z` child
in this inventory. Ordinary legacy extrusion traverses the syntax and skips
the equal-level z without producing these comparisons (source-guard note,
lines 199–227). This identifies the audited machinery, not successor meaning.

No request/arm opening occurs here. Classifying z as `Ex(z,1)` would require
a separate source origin certificate; it would still not prove that z is
§20's opened rigid name. The origin-transport note, “Smallest missing transport
lemma”, independently retains the missing source-interface/row realization.
Thus neither q1's syntax nor its level alone permits applying point 4.

q3/q4 may carry an interface dependent on an existing binder. C §20 expressly
requires joint binder correspondence for dependent returned/stored roots and
introduces no general source escape ban. Merely finding an Ex occurrence
inside B is consequently not a proof of illicit specialization. A receiving
row can represent transport of a dependent interface; alternatively a
proposed realization could detach or solve that binder. The absent
source-to-row realization must distinguish those cases. No particular
equal/older-row storage is certified legal by this observation.

## Minimum semantic insertion seam and conditional trace proof

Supply an actual source derivation Δ, its declared assumptions versus new
obligations, original joint origin/binder correspondence, and permission
relation P over the entire caller tuple and fresh instance. P retains the
original quantifiers: one convenient valuation of a hidden binder is not its
uniform proof. These are input proof objects; P is not defined by this note.

**Local residual M:** for the actual oriented insertion `B(z) <: v`, identify
what source comparison/transport that insertion realizes. On the same
tuples/families satisfying the original incoming source constraints, show
that an accepted insertion preserves P in both directions:
`P_before(sigma,d) iff P_after(sigma,d)`, with the same joint correspondence.
Forward preservation alone would not prove the trace lemma below.
If instead it performs a
forbidden equal/older comparison or specialization, reject before committing
it, including any actual variable/extrusion consequences. This is the
authority-required behavioral proof interface, not an algorithm or an
instruction to inspect a Cartesian product. It introduces no extra subtype
edge merely because a binder occurs in B.

For this exact trace, the instances needed are `v=z`, `v=c`, and `v=R_h`.
The smallest distinct-variable case is `B(z) <: c`; the one-variable q1
instance must also be resolved, since it may reject before q3 is attempted.
The distinct-variable clause is precisely: **does this directed structured
bound preserve the origin-bearing interface's permission relation at this
receiving row, or specialize a represented binder?** Levels decide any
forbidden variable comparison once realized; they do not supply realization.

The terminal q2 also needs a source certificate that this legacy Top endpoint
does not refine P, or its selected guard rejection. Legacy terminal success
and empty support do not establish a selected exemption. No constructor-level
rule or general ground-type convention is needed to state this obligation.

**Conditional finite-trace lemma.** Assume an admitted collected prefix with
source-derived Δ, fixed caller tuple, valid correspondence, and P. Suppose M
proves permission preservation for each actual accepted structural insertion,
the q2 terminal has the preceding non-refinement certificate, and no route
changes origins, levels or correspondence without the proved preservation.
Then P holds before this completed incoming route iff it holds afterwards,
on the same tuples/families satisfying the original incoming constraints.

Proof: apply M at q1, the terminal certificate at q2, M at q3, then M at the
actually derived q4. Compose the equivalences with the unchanged tuple and
correspondence. No new variable or source introduction appears in replay.
The source-guard closure supplies exactly these four shapes, so there is no
remaining value transition in this bounded observation. The proof extends
by induction to finitely many independent bare aliases, retaining prior
instances in P. A rejected prefix has no completed-route conclusion.

This does not demand four redundant physical checks: certificates may be
transported by a proved invariant or shared realization. Every actual
comparison must nevertheless satisfy its current selected guard. O (no
introduced existential among any relevant rows) makes this guard component
vacuous and is one sufficient specialization; the lemma requires preservation
of the actual origin relation instead. It therefore does not assume O.
This is a conditional reduction, not a proof of M, terminal permission,
the full source relation A, or law (L) for an undefined A.

## Verification, frozen inputs, and commit packet

Required rules/researcher instructions read; bounded `cat`/`rg`/`sed`/numbered
reads and SHA-256 only. Truncated used spans were reread narrowly. Zero builds,
tests, probes, Git commands, children, questions, or other writes. Work stayed
within the initial 20-minute bound; CPU/RSS not measured. No executable oracle
or enumeration; trace inherited. Full Function comparison, effects, arbitrary
callers, rollback/publication, source realization/carrier/principality unverified.

Frozen direct content hashes (SHA-256; charter and five assigned notes):

```text
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  charter
a3a39eb02d18efe3b7b0a1d7389703d5a35f655d32d592d288f9236468ada8cc  guard-coverage-authority-audit
20b5f791958db4f8a1f9e06863db6e5e95e72bd4f03d9c8f5c4d4f094516becd  source-guard-derivation-attempt
8514ca2ed9cac0c0dc0261c1d91afa0881ea0de07dd20b5f03f8e54150dfff2f  o-classification-falsification-attempt
b7a6f86a625bb7e6047433da3512a7eda96833d0f57a124eae2d76c09295c10e  name-row-origin-transport-attempt
4f162399344ddce70262f3fcd39a2fecb91df75eb98c4a29dad1d5e14ac11758  level-permission-constructive-attempt
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  concrete-compatibility-boundary
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  source-result-synthesis-choice
```

- Lease: `notes/progress/2026-10-06-section22-guard-authority-closure.md` only.
- Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`; primary revalidation
  against integration HEAD is required. No changed dependency was observed.
- Claim/review: Draft, unreviewed Authority characterization/conditional reduction; no closed semantic gate.
- Proposed commit: `research: reduce section22 coverage to origin-relative insertion`.
- Deferred records: origin realization, K's ground incompleteness, q1's lower/equality distinction,
  and weaker local M instead of requiring blanket O. No shared record edited.
- Next action: prove M at q1 and q3 from one provenance-complete source use
  realization; resolve q2's source endpoint meaning. Reuse q4 by preservation
  if justified rather than introducing another support model.

Writing stops at this frozen handoff; any repair requires a renewed lease.
