# Correlated helper frames: conditional equality obstruction

Date: 2026-10-13
Status: unreviewed research; finite conditional derivation and bounded operational calculation
Baseline: `c69d0b3629879294511fce4e8e20ceffc791ac53`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file; proof leaf, no delegation
Budget: one Sol/high pass, at most 45 minutes; zero heavy processes

## 1. Frozen claim and exclusions

Fix this resolved reference source, preserving all its binders:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

There is one recursive binding F, one nonrecursive sequential binding G,
and distinct formals x, y, z. All recursive references to f use its one open
monomorphic root o. The two published g Names introduce independent
description frames 0 and 1 for the same actual helper provider. They do not
introduce another f, rerun g initialization, or select another runtime object.
The two calls occur in the same enclosing f-body context. `succ:int->int`,
`0:int`, and `true:bool` are the actual reference contracts.

**Conditional statement.** For every joint interpretation of these two
frames in any subtype preorder with transitivity, Function domain/result
rules as below, and `bool` not a subtype of `int`, if:

1. the source-use constraints retain `int <: B0`, `S0 <: V0 <: int`,
   `B0 <: S0`, and `bool <: B1`;
2. the qualified argument equality is active in both frames as
   `C = B0` and `C = B1`, with literally the same C;
3. all clauses are interpreted jointly, preserving their original scope and
   dependency incidences;

then that interpretation requires `bool <: int`, and hence cannot satisfy
those clauses. Equality may mean two subtype constraints, or canonical
identification. Only its two subtype consequences are used.

Quantification is over one shared outer assignment/strategy and both frame
assignments together. Equivalently, fix any common enclosing invocation
parameter h: the argument is about `C(h)`, `B0(h)` and `B1(h)` in that one
context. C is not independently chosen for each frame, and the frame's
Parameter description is fixed before its own invocation challenge. The
proof requires neither choosing a witness after the challenge nor identifying
the frames' runtime receipts or returns.

The equality-placement hypothesis is **not established here**. Its original
source binder and source-to-operational transport are the disputed premise.
Native level 1 proves native retention of C; it does not classify C as
`Shared`, `Established`, `Desc`, or `EventProof` in Source Generalize.

Required conclusion: the above conditional impossibility, a finite derivation
of the reference source's ordinary scalar typing, and whether faithful
constraint equality or faithful canonical merging can avoid the conditional
impossibility. Excluded conclusions: a full Yulang source counterexample,
complete Call/effect admission, public principality, general soundness or
termination, all-history equality/replay adequacy, and a replacement operation.
No source-domain restriction or fresh-C repair is selected.

Claim classes: conditional scalar theorem; constructor-derived native
allocation; bounded, explicitly scheduled equality-encoding calculations;
ordinary algebraic source derivation. Independent review is pending. This
artifact does not promote a parent proof gate.

## 2. Exact authority and source owners

| Dependency | Governing scope |
| --- | --- |
| [Frozen nested derivation](2026-10-13-nested-live-root-generalization-derivation.md) §§4–7 | Actual helper root and map; shared-C allocation S; missing original source placement; scalar discriminator; exact odd/even distinction |
| [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md) §§2–4 | Complete retained relation, original declarations/scopes, shared anchors, independent frames, local-law boundary |
| [Source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md) §2 L1–L5; §§3.1,3.3–3.4,4,5.2 | Original constructors, typed record owners and telescopes, whole-frame allocation and one joint strategy |
| [Selected intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md), Selected operation; Definition-root Value ownership | Qualified equality affects solving and later use; source root reference ownership |
| [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), Approved extrusion-event qualification; Qualification | Original G/F event qualifies actual pairs `(C,B,+,1)`, `(D,R,-,1)`; freshening creates no new extrusion event |
| [Local self-recursion](../design/2026-10-10-local-self-recursive-binding.md), Selected behavior; Proposed source-to-solver seam | Active outer references directly use one root; helper installation precedes later capture/freshening |
| [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5 | Native generation/accumulation/propagation, natural inference, proof-directed construction, necessary abnormal-path safety |
| Original paper, *The Simple Essence of Algebraic Subtyping*, §§3.5.1–3.5.2, Figs.6–9; §5 and footnote 15 | Low-level bound hygiene, independent refinement inside approximating bounds; printed proof sketches exclude let polymorphism |

The actual reference source is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`
at reference revision `9bae772624c23b52a93c1b226157e16898b4d9db`.
The paper is `/home/momota1029/rust/simple-sub-reference-paper.pdf`.

| Actual owner | Produced fact / consumer |
| --- | --- |
| `Typer.scala:23–28` | Authentic `succ` and `true` contracts |
| `typeLetRhs:48–55` | o at level 1 for recursive f, RHS constrained below o; nonrecursive g published as `PolymorphicType(1,Function(B,S))` |
| `typeTerm:62–83` | Same-root monomorphic f Name, formals, all five App demands, record formation, sequential g installation |
| `constrain:106–127` | Reversed Function domains, covariant results, bound accumulation, opposite-bound replay, wrong-level extrusion, primitive rejection |
| `extrude:134–159` | Actual C/D at level 1; polar memo and directional links |
| `freshenAbove:166–190`; `PolymorphicType.instantiate:201–202` | One coherent freshening map per g Name; level-1 coordinates retained |
| `SimpleType.instantiate:205–207` | Active monomorphic f returns o itself |

The current Rust owners were read narrowly:
`crates/yu-hir/src/module/local_source.rs:329–372,636–657`;
`crates/yu-solver/src/candidate_source.rs:245–325,375–411`;
`crates/yu-solver/src/candidate_scheme.rs:116–120,1320–1386`.
They retain lexical identity, active-initializer direct linking, later
`LocalScheme(id,root,boundary)` installation, and capture/freshening. Apply
still records `source.definition_root()` there. These are owner locators,
not an actual emitted G/F certificate or a Yulang equality-transport proof.

## 3. Original scopes and complete reference clause inventory

Use `X->Y` for a reference Function and `Q={a:W0,b:V1}`. All variables below
are type coordinates; F/G and the actual providers are different objects.

| Coordinate / event | Native level / original source position |
| --- | --- |
| o, A | 1; f's recursive inference root and x's Parameter scope |
| B | 2; y's Parameter declaration in g; its type scope precedes g's own challenge |
| Z | 2; z's distinct Parameter declaration inside the wrapper Lambda |
| R | 2; original inner `f y` App result, at its body introduction |
| S | 2; original wrapper App result, at its body introduction |
| C, D | 1; actual negative extrusion operands in o's bound store; original source declaration/region remains unprovided |
| B0/S0, B1/S1 | 1; two independent native images of the reachable g graph |
| V0, W0, V1 | 1; first g App, succ App, second g App results |
| e | One retained extrusion provenance occurrence G/F with both signed pairs; no freshening operation creates another e |

A numeric level is not a substitute for the original source binder tree.
For a genuine full frame, body declarations and EventProof fields stay at
their own introduction scopes beneath the frame's translated dependencies.
Actual EventFields stay under their actual event keys. This note never moves
R's binder to B's pre-challenge scope to simplify the scalar calculation.

Here is every reference source clause, including the unused recursive call.
Function comparison means `X0->Y0 <: X1->Y1` entails `X1 <: X0` and
`Y0 <: Y1`. No equality between source body and invocation ports is inferred
for Yulang from this two-port reference rule.

```text
Kbase:
  f lookup in g       : callee = o                         (monomorphic)
  y lookups           : both occurrences = B              (same formal)
  inner App           : o <: B->R
  wrapper Lambda      : type = Z->B
  wrapper App         : Z->B <: R->S                       [R <: Z, B <: S]
  g Lambda/publication: root = B->S, boundary = 1          (nonrecursive)

Kextrusion:
  o <: C->D; B <: C; D <: R
  retained e          : (G,F), (C,B,+,1), (D,R,-,1)

Kfresh(i), i=0,1:
  g lookup            : type = Bi->Si
  copied bounds       : Bi <: C; Bi <: Si
  map                 : mu_i(o)=o, mu_i(C)=C,
                        mu_i(B)=Bi, mu_i(S)=Si

Kuses:
  0                   : int
  g 0 App             : B0->S0 <: int->V0                 [int <: B0, S0 <: V0]
  succ                : int->int
  succ App            : int->int <: V0->W0               [V0 <: int, int <: W0]
  true                : bool
  g true App          : B1->S1 <: bool->V1                [bool <: B1, S1 <: V1]
  record              : Q = {a:W0,b:V1}
  f Lambda/completion : A->Q <: o
  completion replay   : C <: A; Q <: D
  f publication       : PolymorphicType(0,o)
  final f Name        : instantiate that publication at level 0
```

`o <: B->R` is the original App obligation; the stored approximating
`Kextrusion` entails it by domain reversal and result covariance. It is not
an assertion that both demands are literally present in U(o). Likewise the
completion replay lists generated consequences, not additional source forms.
The final Name uses one new coherent map on the finite reachable graph.
It is downstream of the contradiction. In the satisfying ordinary assignment
below, assign each of its copies its original coordinate's value; all copied
clauses remain true. There is no omitted scalar final-root check.

Before adding equality, the original g root reaches B, S and the upper bound
C of B. It does not reach R, Z or D. Actual `freshenAbove` therefore emits
the two Kfresh blocks, not two copies of the discarded-call body graph.
Kbase and Kextrusion remain in the original store. Native inference succeeds
with this original store; a full-source interpretation must additionally keep
the inner Call's meaning. Root reachability cannot delete that obligation.

For comparison with **complete** hypothetical source frames, retain each
frame's translated body, rather than discard its call:

```text
Kbody(i):
  f Name = o; y Names = Bi; wrapper Lambda type = Zi->Bi
  o <: Bi->Ri; Zi->Bi <: Ri->Si                  [Ri <: Zi, Bi <: Si]
  o <: C->D; Bi <: C; D <: Ri                   (retained-C/D allocation S)

Keq(base): C = B; D = R
Keq(i)  : C = Bi; D = Ri                        (same actual pair provenance)
```

This is a finite scalar incidence presentation of allocation S, conditional
on an original-scoped source introduction and allocation for its operands.
Kbody's Ri/Zi incidences do not claim that native root freshening emits those
coordinates, or that Source Generalize has already classified them. Keeping
them makes the mathematical whole-body clauses explicit without adopting the
missing source bridge. The contradiction uses a subset already in Kfresh,
Kuses and the argument half of Keq(i). Result equalities and complete body
clauses cannot remove that contradictory subset.

## 4. Conditional impossibility: direct derivation

Take one joint assignment satisfying the premises. The second source call
gives `bool <: B1`. The frame-1 equality gives `B1 <: C`. The frame-0
equality gives `C <: B0`. The first frame's body/copied bound gives
`B0 <: S0`. The first g App gives `S0 <: V0`. The actual succ consumer gives
`V0 <: int`. Repeated transitivity yields:

```text
bool <: B1 <: C <: B0 <: S0 <: V0 <: int.
```

This contradicts the fixed primitive relation. Thus no such joint assignment
exists. The proof does not use `D=Ri`, W0, A, a new client W, separate marginal
witnesses, or a different recursive contract. It uses the actual correlation
provided by the first result's succ consumer. Two heterogeneous arguments
with only `Bi <: C` would succeed; the missing direction `C <: B0` is what
transmits that consumer restriction to C.

If a genuine complete source program has this scalar projection at the
indicated scopes, every satisfying strategy for it would project to the
impossible assignment. Conjoining its remaining complete clauses cannot
restore satisfiability. This implication is an unsatisfiability argument;
it proves neither the existence of that projection nor source admission.

## 5. Ordinary reference source derivation and joint assignment

Let `U=int|bool` and `T={a:int,b:bool}` in the algebraic semantic type
language. U is not an added native `SimpleType` constructor. Assume the one
recursive f has type `U->T`. For arbitrary beta with `beta <: U`, bind y at
beta. Both y Names use that beta. The inner f Name still has `U->T`, so
`f y` has type T by the ordinary App rule. Bind z at T; then `lambda z.y`
has type `T->beta`. Applying it to `f y` has type beta. This proves the
helper relationship:

```text
g : forall beta <: U. beta->beta.
```

The entire inner call and its result T have been checked, even though z is
unused. Choose beta=int for `g 0`; its result is int and actual succ returns
int. Choose beta=bool for `g true`; its result is bool. These choices coexist
under the same `f:U->T` assumption, producing the one record T. Bind x at U;
the enclosing Lambda has `U->T`, discharging that same monomorphic recursive
assumption by the ordinary recursive-let rule. After publication the final
f Name has that type. x being unused also permits other domains; no principal
or maximal-domain claim is made here.

The following **one joint assignment**, including the base call and both
complete scalar helper bodies, verifies every scalar clause in §3 except
the added Keq clauses:

```text
o = U->T; A = U
B = C = S = U; D = R = Z = T
B0 = S0 = V0 = W0 = int; R0 = Z0 = T
B1 = S1 = V1 = bool; R1 = Z1 = T.
```

For example, `(U->T) <: (int->T)` and `(U->T) <: (bool->T)` hold because
`int <: U` and `bool <: U`. Both wrapper clauses hold. `C <: A` and
`Q <: D` hold with Q=T. The retained shared C is therefore compatible with
ordinary independent helper descriptions **without** `C=Bi`. Result
equalities `D=Ri` also hold in this assignment; they do not repair the
argument obstruction.

This is a direct typing derivation under genuine reference scalar constructor
contracts, not an execution or a complete Yulang proof. Recursive evaluation
may diverge; no termination or actual return witness is asserted. The paper's
§5 theorem does not itself certify this let-polymorphic extension, as its
footnote 15 explicitly leaves the duplication correspondence separate.

## 6. Equality represented by constraints

### 6.1 Faithful translated equality

Represent `C=Bi` by `C <: Bi` and `Bi <: C`. The proof in §4 uses exactly
those directed clauses. Equality need not be a structural quotient, and
antisymmetry of the preorder is unnecessary. Accordingly a faithful
constraint representation does not change the conclusion.

Writing a base pair of constraints is not proof that either direction is
active in old or future frames. In particular, at levels C=1 and B=2,
the actual reference `constrain(C,B)` cannot store a high-level B directly
in U(C). Its wrong-level branch invokes negative extrusion. The operational
translation must be examined rather than treated as a raw graph edge.

### 6.2 Concrete pre-publication native schedule

Here is one bounded calculation, conditional on inserting the selected
argument equality after g's complete RHS and before its publication. It is
not an actual intrusion implementation in the Scala reference, which has none.
Use the real `constrain` and `extrude` operations with their default fresh
per-operation cache. Existing `B <: C` is the forward half; process the
reverse half by `constrain(C,B)`.

At this cut B has upper bounds C and S, and S has lower bound B. Negative
extrusion of B to level 1 creates E; traversing B's S upper bound creates H,
the negative image of S. Memo registration precedes bound traversal. The
resulting directed incidences are:

```text
levels: C,E,H = 1; B,S = 2
B.lower includes E                  [E <: B]
S.lower includes H                  [H <: S]
E.upper includes C,H                [E <: C, E <: H]
C.upper includes E                  [C <: E]
existing: B.upper includes C,S; S.lower includes B
```

Thus the reverse equality is enforced through `C <: E <: B`, while retaining
low-level bound hygiene. Every g freshening retains C,E,H and copies B,S:

```text
Bi.lower includes E
Bi.upper includes C,Si
Si.lower includes Bi,H.
```

Consequently the semantic frame constraints include `C <: E <: Bi` and
`Bi <: C`. There is no hidden fresh E_i. The extra E/H are the actual
polarity/level repair produced by extrusion, not another reconstruction layer
or a proposed semantic operation.

The native consumer replay also detects the failure in this fixed order:

1. Infer `g 0`, adding `int <: B0` and `S0 <: V0`. For the latter,
   `constrain` stores V0 in S0's upper bounds and replays S0's lower B0,
   processing `B0 <: V0`. That stores V0 in B0's upper bounds and replays
   B0's lower E, processing/storing `E <: V0`.
2. Infer the succ App, adding/storing `V0 <: int` in V0's upper bounds.
   It need not eagerly derive or store `E <: int`.
3. Infer `g true`, adding `bool <: B1`. B1's upper C processes
   `bool <: C`; C's upper E processes `bool <: E`; E's upper V0 processes
   `bool <: V0`; V0's upper int processes `bool <: int`. `constrain`
   reaches its primitive mismatch branch.

Every edge named in this replay is supplied by an owner above. The proof
does not assume that copied lower bounds insert symmetric upper bounds:
`freshenAbove` writes the copied bound lists directly, and step 1 specifically
uses B0's copied **lower** E. Stored constraints alone would not establish
this activation; the ordered replay demonstrates it for this finite schedule.

The argument equality suffices. A faithful additional `D=R` before publication
may add bounds or merge result coordinates but cannot remove the active
argument/consumer clauses. No all-schedules or rollback/replay theorem follows
from this finite calculation. If constraints are instead recorded only after
both old frames have been allocated and are never translated/replayed there,
the premise `C=Bi` has not been met. That delayed implementation supplies no
counterexample to §4 and no faithful general transport proof.

## 7. Equality represented by canonical merging

Assume a lawful merge substitutes one canonical coordinate J for B and C in
all owning roots, retained clauses and consumers, with target level
`level(J)=min(2,1)=1`, preserving all bounds. This is an explicitly stated
operational hypothesis; merely selecting a representative ID is insufficient.

Before g publication its root becomes `J->S`, and S retains lower J. Each
native g use retains J and freshens any still-high S to Si, with `J <: Si`.
Thus the calls generate:

```text
int <: J; J <: S0 <: V0 <: int
bool <: J; J <: S1 <: V1.
```

The first g App replays S0's lower J while adding `S0 <: V0`, storing
`J <: V0`; the succ App stores `V0 <: int`. The second argument's replay
follows J's upper V0 and V0's upper int to `bool <: int`. If canonical hygiene also
lowers S, the two uses retain still more shared coordinates, and the same
chain through J remains. Merging D/R does not remove it.

More generally, quotienting the faithful **already allocated** finite
constraint set maps C, B0 and B1 to the same J, so §4's chain is unchanged.
Picking a level-2 representative and freshening its whole class independently
would make the shared C acquire different images. That changes the frozen
retention premise; it is not equality encoding's preservation of that premise.

This section proves the scalar quotient consequence and a finite consumer
path under complete canonical incidence rewriting. It does not certify a
real merge implementation. The untouched Scala constructors hold ordinary
local references and have no canonical-representative consumer; a separate
source/operational proof must justify rewriting those references, snapshots,
captured roots and all later uses in an actual implementation.

## 8. Complete Call, effects and source admission boundary

The finite reference derivation includes all five original App occurrences:
inner `f y`, wrapper application, `g 0`, `succ (g 0)`, and `g true`.
The declaration/type derivation accounts for the discarded recursive result;
it is not replaced by a pure identity source. It also includes all three
Lambda formals, both publications, the record and the final f Name.

For Yulang, each corresponding complete Call rule program must retain:

| Original local incidence | Required fields and obligations |
| --- | --- |
| Callee computation | Its original evaluation, Return/Request alternatives, returned actual callee/provider and pending suffix |
| Whole argument | Original inert carrier, formation/license, typed guard and future designated-execution obligations |
| Receiver and entry | Current receiver/configuration, actual receipt, original Value or retained-Computational entry role; designated Force where Value entry requires it |
| Body | Actual Return/rebind and formal/provider identity, full body checking/evaluation and any request/response/resumption continuation |
| Invocation return | Source-designated consumption and return descriptor, with the original invocation port and dependent evidence |
| Effects/worlds | All conservative effect alternatives/guards, attachments, handlers/protection, output and residual lineage, shared histories/worlds and original witness dependencies |

These are the uncontracted local fields from Source Generalize §3.1 and
L1–L5, not new opaque successful-Call predicates. This note has not constructed
their authentic primitive clauses for the witness. It cannot infer those
clauses, their strategy or scope from the reference's two-port Function rule.
In particular it does not identify body and invocation ports, forget effect
attachments, or select independent provider/witness marginals.

The exact bridge needed to turn §4 into a Yulang refutation is therefore:
(a) admission of the fixed source under genuine local Call/closure/recursive
laws; (b) its genuine scalar argument/result/consumer projection; (c) the
owning registration's original declaration/telescope for C and the qualified
equality; and (d) active equality transport to both independent g frames while
retaining that same C. Approved G/F qualification proves neither (a) nor (c)/(d).
The current Rust direct-root and local-use owners prove neither complete Call
nor those equality clauses. No parent soundness/principality gate closes here.

## 9. Economy audit and one next action

The prior fixed-anchor/publication attempts and frozen nested derivation
already isolated this same source placement. This bounded pass makes its
conditional obstruction and two equality encodings explicit. It does not
count a repeated fiber calculation as progress on the missing premise.

Under `rules/compiler-engineering.md`, scope-safe qualified equality and its
source/operational bridge are A; ordinary independent helper typing is B.
Active-root and demand incidence reconstruction from levels/IDs/SCCs is D:
registration, active lookup, App generation and extrusion already know that
incidence and can retain it. A retained certificate removes lost ownership
information; it does not establish the lawful original source binder/allocation
for C. These A/B obligations retain their original scope and OPEN status.

One next action for the primary: obtain the original-scoped active-root
dependency law at helper registration and Call-demand accumulation, including
its equality allocation/activation. If that independently established law
and genuine admitted Call projection force the frozen shared-C premises,
submit this conditional contradiction to the existing design-authority path.
Another equality/quotient proof or larger probe under the same premises will
not establish that law. No selected operation is redesigned by this packet.

## 10. Checks, frozen dependencies and handoff

Authority: existing research scope, no semantic adoption. Behavior: conditional
and source-bridge uncertain. Scope: internal source/solver correspondence.
Performance: cold static work. Reviewer/verification assignment remains primary
owned; producer inspection is not independent review.

Commands: bounded `cat`, `sed`, `rg`, `nl`, `pdftotext -layout ... -`,
`sha256sum`, and read-only Git HEAD/branch/status/dependency inspection;
one leased Markdown creation and narrow whitespace/content inspection.
An initial Rust read used the abbreviated paths from the dependency note and
failed; the actual `crates/` paths above were then read. No test, build,
reference execution, executable probe, benchmark, Git mutation, subagent or
other-path write. Zero measurement samples and zero heavy processes. One
lightweight shell/PDF process at a time after initial independent read batches;
CPU/RSS were not measured. Wall-time budget: 45 minutes, not exhausted.

Requested runtime: normal `prover`, `gpt-6.1-sol`/high per primary packet and
configured defaults. Observed effective model/effort metadata: unknown.
`.codex/config.toml` registers prover and Sol/high defaults;
`.codex/agents/prover.toml` omits model/effort pins. The callable schema supports
prover; this leaf launched no worker. No Astra, override-success or hot-reload
claim. Writes stop at handoff.

Direct dependency SHA-256 values:

```text
f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9  frozen nested derivation
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  Source Generalize selection
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  Source Generalize construction
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b  parent-copy operation
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775  occurrence qualification
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  local self-recursion
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  top-level principles
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  candidate_scheme.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference Typer.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698  reference paper PDF
```

No dependency was changed by this leaf. The direct dependency hashes at the
pinned baseline match the inspected files. The primitive separation, five
App scalar clauses, ordinary joint assignment, reverse-equality extrusion and
specific opposite-bound replays were checked manually against actual owners.
No independently reviewed status or general runtime adequacy is claimed.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-13-correlated-frame-equality-obstruction-proof.md`.
- Baseline SHA: `c69d0b3629879294511fce4e8e20ceffc791ac53`.
- Changed dependency hashes: none by this leaf; inspected hashes above.
- Claim/review status: unreviewed conditional derivation and bounded scheduled
  native calculation; primary must assign fresh independent review.
- Checks already run: direct source-owner reads, full scalar clause/assignment
  derivation, constraint/merge cases, dependency hash and note whitespace checks;
  zero tests/builds/executable inference or measurement samples.
- Proposed checkpoint message: `research: derive correlated shared-frame equality obstruction`.
- Shared-record deltas left for primary/curator: retain original parent A/B
  gates OPEN; record that faithful active shared-C equality has the same
  obstruction in constraint and canonical encodings; record pre-publication
  E/H extrusion/replay as bounded evidence; keep original source placement,
  complete Call/effects and admitted-source bridge unproved. No shared record
  changed.
