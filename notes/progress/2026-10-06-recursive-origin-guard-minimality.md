# Recursive Name origin: guard discriminator and residual minimality

Date: 2026-10-06
Status: Reviewed research-only partial-completion analysis
Review: independent compiler_referee and spec_auditor, no findings on this note.
Review record: [closure review](2026-10-06-recursive-origin-guard-closure-review.md).
Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Implementation authority: none

## Scope, sources and result

Adversarially minimize the origin/guard gap for `my f x = g; my g y = f`
with finite unused bare aliases of f/g. The source-guard note's completed
production history is inherited; no new source acceptance is asserted.
Selected authority is the charter §§1–2, 20–23 and source-result synthesis
§4. Candidate pure/SCC judgments are comparison material, not selected
Yulang semantics. No regular-tree carrier, transitive concrete comparison
relation, new existential introduction, or source admission rule is selected.

**Result:** q1 has a direct existential endpoint and can replace q3 as the
earliest *conditional* discriminator. It removes the need to hypothesize K's
Cartesian support-to-peer coverage. It does not remove the missing direct
structural-bound permission rule. In particular, q1 is neither the selected
ground-narrowing example nor a direct variable/variable comparison. A
one-variable, one-obligation partial completion is sufficient to separate
the local guard components; it does not certify full-calculus non-entailment.

References: [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
§§20–23; [selected synthesis](../design/2026-10-02-source-result-synthesis-choice.md)
§4; [source-guard derivation](2026-10-06-rec-name-return-source-guard-derivation-attempt.md)
“Exact value replay closure” and “Guard classification”; [origin falsification](2026-10-06-rec-name-return-o-classification-falsification-attempt.md)
“Two source-origin completions”; [coverage audit](2026-10-06-rec-name-return-guard-coverage-authority-audit.md)
“Exact clauses”; [Name transport](2026-10-06-rec-name-return-name-row-origin-transport-attempt.md)
“Constructive source step”. These research references do not add authority.

## Fixed history and what the authority eliminates

For one incoming bare alias `my h = f`, preserve the admitted collected
prefix `c <= r`, all current levels equal to one, and the fresh constrained
R instance z. The inherited added value history, in execution order, is:

```text
B(z) = P0(Top-, P0(Top-, z+))
q1: B(z) <: z
q2: z    <: Top-
q3: B(z) <: c
q4: B(z) <: r       (replay via c <= r)
```

There is no derived z/c variable task and no Function/Function comparison.
The trace ends before alias generalization/publication. Effect collection is
separate; this incoming substitution allocates no effect row.

The selected Name rule copies a *supplied* interface. It contributes no new
source introduction in that synthesis step. It does not determine the
preceding generalized interface or realization of z/c/r. Absence of request
opening proves absence of that §20 event, not exhaustiveness of source
introduction categories. Mathematical existential valuation and stored R
category do not establish `Ex(z,1)` or its negation.

For the ordinary-versus-Ex(1) perturbation studied here, c/r cannot be
flipped: their already admitted direct comparison is forbidden if either is
Ex at introduction level one. Fix their ordinary status and all earlier
instances as in the paired origin construction. This does not prove ordinary
classification for arbitrary collected rows, or exclude other introduction
levels not specified by this envelope. Vary only z's source-origin flag.

## A compact decision table

Write e=0 for the supplied negative classification of z, e=1 for supplied
`Ex(z,1)`. Ordinary c/r and the unchanged admitted prefix are fixed. The
table concerns only the §22 guard component, not full source acceptance.

| Shape | e=0, no guarded origin in this inventory | e=1 from selected clauses alone | Extra fact needed for a definite e=1 verdict |
|---|---|---|---|
| q1 | Vacuous | Open | Direct existential endpoint versus restored structural lower bound |
| q2 | Vacuous | Open | Existential endpoint versus greatest-Top comparison; no constructor level is selected |
| q3 | Vacuous | Open | Nested existential occurrence versus ordinary receiving variable |
| q4 | Vacuous | Open; re-entry is mandatory | Permission for the new receiving root, retaining the same binder correspondence |

“Open” is a missing derivation, not permission to accept. The explicit
`kappa <: Int` rejection does not assign truth values to these four shapes.
The re-entry requirement makes q4 an obligation; it does not infer its
result from q3. Inferring equal q3/q4 results from their ordinary level-one
targets additionally needs a guard-extensionality/correspondence lemma.

With e=1 the added conjunction is `g1 && g2 && g3 && g4`. Execution stops at
the first false guard. Consequently a derived rejection of q1 makes q2–q4
irrelevant to that execution's guard failure. If q1 passes, q2 remains an
obligation; only after it passes can the distinct-target seam become decisive.
With e=0, negative origin throughout the inventory makes all four conjuncts
vacuous, exactly the reviewed conditional O argument.

## Why q1 is stronger than q3, but not already ground narrowing

If z is Ex, q1 mentions it as a complete endpoint. No support-product rule
is needed to *locate* that endpoint. q3 instead needs a rule connecting the
occurrence inside B(z) to permission against c. This removes one coverage
step from the q1 attack, while retaining the classification and structural
permission seams. The K table's `(z,z)` test is one possible treatment of
q1; q1 itself is not the comparison `z <: z`.

Three shortcuts fail:

1. **Groundness:** `V(B(z))={z}`. A concrete outer Function head does not
   make B(z) ground. The selected ground example has `V(Int)=empty`.
2. **Direction:** `kappa <: Int` constrains the upper endpoint of the abstract
   type. `B(z) <: z` adds a lower bound. In any candidate greatest-Top carrier,
   z=Top satisfies q1, since `B(Top) <= Top`. Thus q1 does not by itself force
   z to be a Function-headed value. This is only a candidate-Top sensitivity
   argument; it does not imply that a source existential may acquire that bound.
3. **Replay status:** q1 restores the R bound. Whether this represents a
   declared existential assumption or a newly forbidden specialization is
   missing source correspondence. Bounds declared by an interface and a
   private solver constraint cannot be equated merely from their syntax.

Computing a composite “level” as min/max of its support would yield one for
B(z), but selects an unprovided rule. Giving its Function head level one
contradicts §23's direction. Deriving a z/z guard from extrusion requires an
actual variable/extrusion coverage argument; unchanged levels alone do not
provide it. Neither the direct endpoint observation nor the Top witness
settles the structural-bound permission judgment.

## Minimal relative partial completion, without K

Retain the paired origin constructions after erasing source decorations.
C0 labels z ordinary; C1 labels z Ex(1); both fix the same ordinary c/r,
prefix, injective freshening, candidate graph and production inventory. Add
to both the single shared hypothetical clause D for this exact attempted
shape:

```text
Ex(z,1), attempted restored comparison B(z) <: z
------------------------------------------------ D (hypothetical)
the guard rejects this attempted comparison before commitment
```

Then C0's added guard component is vacuous, whereas C1 stops at q1. No
verdict for q2–q4 under C1 is needed, no z/c task is fabricated, and no
Cartesian product is used. The distinguishing obligation uses one variable
and one attempted comparison, the earliest comparison in the inherited
trace. B's two Function heads remain because this is the actual production
bound, not a new unary synthetic source. Keeping the alias fixes the common
audited use route; deleting it abandons that source-produced incoming route.

This is a *partial* origin/permission completion with an explicit extra
premise, not two completed models of the selected Yulang calculus. D is not
derived here. Its single added rejection does not contradict any explicitly
selected acceptance for this shape, but that observation is not a proof of
global extendibility, source adequacy or principality. Its useful improvement
over K is the precise smaller missing clause. It does not choose D as policy.

## Global K and retained binders

K alone cannot be a global implementation of §22: `V(Int)=empty` gives no
support pair for `kappa <: Int`, so its guard passes the exact selected
forbidden specialization. A ground-narrowing clause must supplement or
replace it. This is a direct defect in globally promoting K, although the
prior note explicitly restricted K to the four-shape alias vocabulary.

Section 20 supplies a separate correspondence concern. K would reject
`T(kappa) <: T(kappa)` whenever both supports contain the same Ex(1), and
would reject equal-level pairs between retained dependent binders. But §20
requires joint witness correspondence through aliases/resumptions and
dependent returned/stored roots; it does not say these transports generate
those comparisons. Therefore no additional *unconditional* §20/K conflict
is proved. If a source adequacy bridge both requires admission of such
binder-preserving transport and generates that K-rejected task, that bridge
would expose a conflict. Pure identity transport may instead copy a supplied
interface without this task. No reflexive exemption or escape ban is chosen.

## Boundary, checks and frozen packet

A local decoration/table is insufficient for full-calculus non-entailment:
the complete source admissibility relation and source-to-row realization are
not provided, and local completions need not extend to request opening,
declared bounds, dependent transport and principal inference. This is a limit
of the present method and inputs, not a proof that no complete countermodel
could exist. No fresh behavior, full A/(L), or production change is authorized.
Next action: derive the source role of z and then the direct-endpoint q1
permission before seeking a nested-support q3 rule. Retain §22 ground
narrowing and every-comparison re-entry as established requirements.

Checks: required policy/source reads, bounded section searches, initial HEAD
and branch equality, `git diff <baseline> --` all eight semantic dependencies
(empty), target absence, SHA-256 snapshots and final leased-file integrity
read. No scripts, tests, builds, probes, enumeration, children, Git mutations,
question edits or shared-record writes. No executable would distinguish a
source claim here without assuming D/K. CPU/RSS were not instrumented; only
lightweight read processes and one leased-note write were used.

| Frozen dependency | SHA-256 |
|---|---|
| charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| selected synthesis | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| origin falsification | `8514ca2ed9cac0c0dc0261c1d91afa0881ea0de07dd20b5f03f8e54150dfff2f` |
| coverage audit | `a3a39eb02d18efe3b7b0a1d7389703d5a35f655d32d592d288f9236468ada8cc` |
| Name transport | `b7a6f86a625bb7e6047433da3512a7eda96833d0f57a124eae2d76c09295c10e` |
| source-guard derivation | `20b5f791958db4f8a1f9e06863db6e5e95e72bd4f03d9c8f5c4d4f094516becd` |
| candidate pure source rules | `beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73` |
| candidate SCC rules | `78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda` |

Commit packet: exact lease is this note; baseline SHA is the header value;
dependency hashes unchanged; initial Draft/unreviewed research checkpoint,
followed by the independent review recorded above; checks above;
proposed message `research: minimize recursive-origin guard discriminator`.
Primary/curator owns any shared-record synthesis, review promotion or full
gate status. Those changes were deferred at the producer's frozen handoff;
the primary subsequently synchronized status in the linked review record.
