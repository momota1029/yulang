# Universal scheme use versus existential introduction: source audit

Date: 2026-10-06.
Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`.
Method: bounded correspondence audit of selected source clauses and frozen
Oracle specification/fixture text; no executable experiment.
Status: unreviewed research characterization and conditional derivation;
no successor typing rule, policy proposal, theorem closure or implementation
authority. Artifact frozen on submission; independent review pending.
Lease: this file only.

## Objective and governing dependencies

Determine whether selected source rules classify a fresh instance of an
ordinary universally quantified scheme as an existential introduced for
charter §22. The authority packet fixes these sources:

- [Redesign charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§1–2,20,22–23: replace F5 scheme machinery; final well-typed-program
  capability is the Oracle target; essential request opening; every derived
  comparison repeats the existential guard; levels belong to variables.
- [Result synthesis](../design/2026-10-02-source-result-synthesis-choice.md)
  §4: known computation interfaces are forwarded, implicit interpretation
  polymorphism is rejected, value/effect type polymorphism remains required.
- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–2,5: source annotations, public schemes and internal views are distinct;
  generalization/instantiation preserve the shared source relationship;
  exact generation and preservation judgments remain open.
- [Principal scheme acceptance criteria](2026-10-04-principal-scheme-acceptance-criteria.md),
  “Expected principal schemes”: the accepted ordinary identity presentation
  is `my id x = x` with `id : 'a -> 'a`. This is a source acceptance criterion,
  not a completed successor derivation.

Historical comparison only: Authoritative F4 §§1,3,7,15 and F5 §§1,7–9,23.
Charter §§1–2 withdraw F5 Q/R and scheme-equivalence requirements from the
successor gate. Frozen Oracle reference:
`a58eefc31e22141574b6f20c6a5748151c6d79f1`.

## Established textual facts and the missing bridge

Charter §20 describes three separate events for an operation-local binder:
the operation's universal binder is instantiated once at use; a request
packages the existing witness; elimination opens fresh names for uniform arm
checking. Packaging adds no fresh instantiation, and fresh proof names create
no independently solvable instances. Its final paragraph explicitly separates
the illustrative equality kernel's existential inference variables from hidden
request binders. Thus neither a common allocation mechanism nor the word
“fresh” identifies these semantic events.

Charter §22 supplies a conditional guard: **an existential introduced at level
`l`** rejects comparison/unification with types at levels `<= l`; comparisons
above `l` permit ordinary internal propagation. Every derived comparison
re-enters that guard. The clause does not define which ordinary scheme-use
allocation is such an introduction. Section 23 removes constructor/head level
metadata and leaves exact variable/extrusion coverage and preservation open.
Assigning `Int` a level zero would reinstate an unselected head-level rule.

Call-view §2 requires source-slot identity, lexical scope, correlations and
original joint constraints to survive use-time instantiation. It does not
classify the newly allocated type coordinates under §22. Result-synthesis §4
preserves ordinary value/effect polymorphism, but supplies neither a universal
scheme-elimination judgment nor an existential-origin judgment.

**Bounded conclusion:** no clause in the assigned selected sections identifies
ordinary universal-scheme freshening with §22 existential introduction, or
explicitly classifies every such fresh instance as a nonexistential. This is
absence of a bridge in the inspected source set, not a proof that no selected
rule anywhere in the repository supplies it. The missing premise is the
source-derived judgment relating ordinary universal elimination/use allocation
to the guard's introduction domain, including its level and constraint paths.

F4 cannot fill it: §3's scheme has zero binders and only `Bottom | Int`.
F5 §1 explicitly gives `forall q0. q0 -> q0`; §§7–9 require a shared fresh
variable per binder within a use and isolation between uses. Section 23 places
incoming variables at the consuming body's level. These establish historical
freshening behavior within the old pure fragment. They do not establish
successor existential classification, and Q/R is not successor authority.

## Conditional derivation and smallest source discriminator

Keep these propositions distinct:

```text
FreshUse(t, sigma, use)    t is a fresh solver coordinate for this scheme use
Intro22(t, l)             t is an existential introduced under §22 at level l
exists t. C(use,t)        a mathematical satisfiability projection
```

The third proposition can describe the search for an instance satisfying a
use's constraints. It supplies neither the first proposition's implementation
nor the second proposition's source introduction. Similarly, allocation of a
fresh variable does not itself prove `Intro22`.

The following implication is conditional on two explicit hypotheses:

1. H-origin: ordinary scheme freshening of coordinate `t` entails
   `Intro22(t,l)`.
2. H-path: typing the considered use generates a comparison between `t` and
   a variable `X` with `level(X) <= l`, possibly through replay/propagation.

Then §22 rejects that comparison at generation/comparison time. Its repeated
guard also rejects a derived comparison of those endpoints. This follows
directly from the selected guard; H-origin and H-path do not follow from it.
No claim is made about a constructor-only comparison or a source program
whose exact variable/extrusion derivation is unavailable.

The smallest located ordinary source discriminator consists of one definition,
one use and one concrete argument:

```yu
my id x = x
id(1)
```

The frozen Oracle fixture
`crates/yulang/src/source/tests/case_01.rs:74–86`,
`dump_mono_without_std_specializes_root_expression_call`, writes exactly this
source and asserts `mono roots [(m0 1)]` and `m0 = d0 : int -> int` after a
successful dump. At `:20–32`,
`dump_poly_without_std_infers_identity_function` asserts the definition line
starts `my d0:id: 'a -> 'a = `. These are static test contracts; neither test
was executed here. Removing the use removes the fresh-use question; removing
the argument removes the located concrete specialization observation.
No automated shrinking or global minimality proof was performed.

The frozen decided specification
`spec/2026-06-07-principal-monomorphization.md:222–224,329–332,435–455`
explains ordinary `id 1` specialization: instantiate the quantified variable
to a use-site fresh monomorphic variable, solve its bounds, and substitute
the concrete `int` solution into `int -> int`. Its bounds example includes
`int <: alpha` and `alpha <: int`. These are historical Specialize rules,
not a successor generation judgment; its explicitly demanded `int` result
must not be silently attributed to every unannotated source call.

Frozen `crates/infer/src/instantiate.rs:620–651,732–739` separately shows the
inference allocator freshens scheme quantifiers, preserves its per-use mapping,
and calls `fresh_type_var_at(self.level)`. The inspected code and specification
do not identify those allocations as request opening or as §22 introductions.

Consequently `id(1)` discriminates a future proposed bridge if that bridge
proves H-path and predicts rejection. It is **not an established successor
counterexample** now: the selected origin and decomposition/level bridge are
missing. The fixture alone also does not prove successor soundness or
principality.

## Independence, coverage and failure conditions

There is no checker or supplied transition model. The independent inputs are
current selected source obligations and frozen historical specification/fixture
text. The fixture and old implementation are from the same Oracle revision
and are not independent reviews or proofs of each other's behavior. They share
that historical language contract and may share defects. The current user
criterion independently fixes the identity scheme presentation; it does not
independently certify the frozen runtime/dump observation or the missing bridge.

Coverage is the assigned selected sections, the stated F4/F5 sections, the
four frozen Oracle paths below, and exact textual searches used to locate the
identity source. Some broad locator output was truncated; only the subsequent
explicitly read passages support this audit. No exhaustive repository absence
claim is made. No seeds/ranges, executable cases, mutations, tests, builds or
performance samples were run. Exact successor name-use generation, type/effect
scheme elimination, structural decomposition, extrusion coverage, hidden
request lifecycle and final acceptance of this source remain unverified.

The audit fails or needs delta review if a governing dependency changes, an
accepted selected source judgment already supplies H-origin/H-path, the exact
Oracle fixture/specification is superseded for its historical scope, or the
primary assigns a broader origin rule. Reinterpreting solver satisfiability's
mathematical `exists` as object-level existential introduction invalidates the
argument. Copying F5 or Oracle levels into successor semantics also invalidates
the claimed authority boundary.

## Commands, resources and next action

Checks were read-only `git rev-parse HEAD`, `git ls-tree`, bounded `git grep`,
`git show ... | sed/rg`, `rg`/`sed` source inspection, and a Python SHA-256 plus
byte-equality comparison of nine direct live dependencies against the pinned
baseline. All nine were unchanged at the comparison. No Git mutation occurred.
The lease path was absent before creation. No tests/builds/probes were allowed
or performed; heavyweight process count is zero. Reads used at most four
concurrent command calls in a batch. CPU time, peak memory and total wall time
were not instrumented; no resource performance claim is made. Output is this
one note; transient command output was bounded.

Recommended next action: the primary should locate or adjudicate the missing
ordinary scheme-use-to-§22 origin judgment before a solver proof/checker assumes
it; then validate that judgment and its variable/extrusion paths against the
identity acceptance discriminator. This requests no new policy in this note.

## Frozen dependency fingerprints

SHA-256 at the pinned baseline (all checked equal to live bytes):

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337  notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md
7ec6ae3b8ea4048d0407388b23665092a121a3720f8658055dfb5e1046a09c25  notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
```

Frozen Oracle SHA-256 at `a58eefc31e22141574b6f20c6a5748151c6d79f1`:

```text
30220bb81581e7470e51e295df681d292caff71599cb01a0a08d04e226d1f7f3  spec/2026-06-07-principal-monomorphization.md
876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c  crates/infer/src/instantiate.rs
c5e2989e57f72a52633d9978066a944dd25594c90b58b10af02b26f9165333da  crates/yulang/src/source/tests/case_01.rs
e4c329f407a16a9e70159ec9af6d40a6b7e5082b1cfeec7f1892bd52d4f7efb2  crates/yulang/src/source/tests/case_02.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-universal-scheme-use-origin-audit.md`.
- Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`.
- Dependency hashes changed: none at producer recheck; fingerprints above.
- Claim/review: bounded source audit and conditional derivation; independent
  review pending; research-only artifact, frozen on submission.
- Checks already run: static passages and fixture assertions inspected;
  direct dependency SHA-256/byte equality; no tests/builds/executable checks.
- Proposed commit message: `research: audit universal scheme use origins under existential guard`.
- Shared-record deltas left for primary/curator: record the missing ordinary
  universal-use origin/level bridge separately from §22 replay-guard coverage;
  link the frozen `id(1)` static discriminator without declaring a successor
  counterexample or changing authority/theorem status. No shared paths edited.
