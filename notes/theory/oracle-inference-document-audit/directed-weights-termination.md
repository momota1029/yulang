# Historical directed weights, residual budgets and termination

Date: 2026-10-12
Status: bounded document audit and derivations independently reviewed; source theorem OPEN
Claim class: historical proof audit; no theorem-status promotion
Primary baseline: `67830dce14e6987b37e47b2540c204fcd06a92c6`
Oracle anchor: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; writing stops at handoff
Authority: the primary's document-first packet; no implementation, tests or probes

Independent review: a fresh `compiler_referee` confirmed the DW15 algebraic
counterexample, the bounded elementary and fixed-word-graph derivations, the
source bridge gaps and model/transfer distinctions. No blocking or major
submission findings. Review does not close the original source theorem or
certify the whole colored/typing/generalization corpus. Original producer hash
before this review-status annotation: `c5c07cbd77fcd2e1c551c74522871ef0a364ccc8a198f92b4637607dabf7df32`.

The elementary entry algebra, budget conservation and a fixed-graph potential
argument admit direct derivations. The combined paper's source-to-cycle-balance
bridge is not established by its displayed construction rules. Moreover, one
unqualified projection equation is false in the paper's own label algebra.
These are separate findings. Neither establishes a counterexample to termination
of an actual source program, and neither is a reason to discard the old model.

## 1. Frozen corpus, authority and reading coverage

All line locators below refer to `git show REV:PATH | nl -ba`, not live Oracle
files. The dirty Oracle capture worktree was not read or changed. The directory
instruction at the Oracle anchor explicitly calls these papers a miniature
research model rather than the production specification. A paper calling its
result a theorem or complete proof is recorded as an author claim, separately
from the producer's validation and the primary's future independent review.

Short names keep the six distinct paper lineages visible:

| ID | Exact recovered path under `research/effect-mini-language/` | History and inspected version | Assigned reading coverage |
| --- | --- | --- | --- |
| CW | `colored_weighted_simple_sub_ja.tex` | ADD `b2555e09a` June 21; deleted `1301b1a93` June 22; recover `1301b1a93^` | §§3–4 weight/bounds/split, §7 recursion/cleanup, §§10–12 correspondence, principal and termination claims; lines 388–656, 865–943, 1134–1237 |
| WC | `weighted_effect_subtraction_core_ja.tex` | ADD `5f1e75e7d`; deleted `1301b1a93`; recover parent | All definitions/transitions/invariants after surface grammar, lines 106–513 |
| DP | `directed_stack_weight_principal_letrec_ja.tex` | ADD `59df62404` June 22; deleted `1301b1a93`; recover parent | §§1,3–4, basic soundness/principality §§9–10, terminal open obligations; lines 152–173,232–556,860–1000,1059–1088 |
| CS | `directed_stack_weight_principal_letrec_colored_soundness_ja.tex` | ADD `0dd37b900`; revised `cfd2ef4b5`; renamed with changes by `f2c186b3e` | Revised weight/bounds/split and scope, lines 170–194,255–579; remaining obligations 1530–1562; ADD-to-revision guard diff inspected |
| RT | `directed_weight_row_solver_termination_ja.tex` | Declared June 21; ADD `fac1aeec8` June 22; deleted `f2c186b3e`; recover `f2c186b3e^` | Entire mathematical core and proof boundaries, lines 124–681 |
| CP | `directed_stack_weight_letrec_complete_ja.tex` | Declared June 22; ADD/rename `f2c186b3e`; anchor version unchanged since that commit | All §§1–9 premises and assigned proofs, lines 189–1407; compact/principal links and integrated conclusion; selected colored premises |

The parent commits resolve to `a08815e4d1afa8ff7470cd720303d884687d1a68`
for `1301b1a93^` and `305da4228ffc726a3db0423c60f17a9ba4b18297`
for `f2c186b3e^`. “All assigned proofs read” refers to the weight, row-split
and termination groups, not the whole colored metatheory or the 645-path corpus.

Rescue alternate **RA** is CP at `a1952fd3281e0a293f899f4cfdb852e4f24d727c`.
Its diff adds an effect-sequence fan-out/provenance-normalization requirement
before row atomization and records an implementation replay-lowering gap.
It is a nonmerged alternate, not an authoritative successor to the anchor.
`0dd37b900` → `cfd2ef4b5` instead changes guard coloring from current visibility
to entry-except snapshots, including corresponding theorem hypotheses; it does
not close the predecessor's explicitly open termination obligation.

Supporting documents were read before current comparisons:

* Oracle `spec/2026-05-31-effect-variable-subtractable.md`, §§Directed weight,
  Weight composition, Row upper bound, Bound replay and termination relation
  (anchor lines 45–214,302–344), with prerequisites/filter/annotation/compact
  (1–375). It declares May 31 initial / June 22 revision and core-spec standing;
  direct user-approval provenance is not established in this audit.
* Oracle `notes/design/2026-06-22-directed-stack-weight-implementation.md`,
  entire note. Its source is CS, not CP. It explicitly supersedes conflicting
  older protect/floor readings; its implementation-status prose is documentary
  evidence, not independent code correspondence.
* Historical May seed `archive/notes/design/2026-05-30-effect-system-with-monomorphize.md`
  and detail `archive/notes/design/2026-05-30-effect-system-spec.md`, recovered
  at `9b853468f^ = 7915390c9cc8fb7f39eb04123abc0c7b581ea4a0`, introductory
  grammar/bind sections. Detail lines 3–8 explicitly give the seed priority.
  May subtractable predecessor at the same archive ref, lines 1–67, records
  lifetime IDs, weighted variance, fresh introduction and shallow recursion.
  These are lineage premises only; later detailed proof claims remain unread.
* Oracle `notes/design/handler-row-subtraction.md`, introductory shift/peel
  and shallow-handler sections: prior boundary intuition, no directed algebra
  theorem imported from it.

Active workflow sources: `rules/agent-orchestration.md` (Model routing;
Proof delegation/decomposition), `rules/research-lab.md`,
`rules/design-authority.md`, `rules/compiler-engineering.md`
(proof-obligation economy), `rules/git-concurrency.md`,
`rules/orchestration-budget.md`, and the `yulang-proofs` skill.
This is one leaf producer; independent review belongs to the primary.

## 2. Statement, quantifiers and exclusions frozen before audit

### CP model

Fix finite `Fam`, `B = P(Fam)`, finite static `Id` from a finite term, and a
fixed seed `seed(u) ∈ B` per ID. The grammar is unit, function, computation
and effect row with regular recursive graphs; handler is complete for one
family and shallow; recursion is monomorphic inside each RHS. Scheme
instantiation freshens type variables, row variables and local IDs together.
Normalized marker semantics is the operational object; thunk/force, ADTs,
family type arguments and polymorphic recursion are excluded by CP §1 and
its final “scope outside” paragraph. These exclusions belong to the old
theorem; they are not proposed restrictions on current Yulang.

For each `u`, left entry `(p,q,F)` is in `N×N×B`, denotes
`pop_u^p push_u(seed(u)∩F)^q`, and retains floor `F` even when `q=0`.
Only `push_u pop_u = 1` cancels. Left weight is `(A,(e_u))`; `A` is ambient
remaining budget. Right weight is a finite-support natural pop map.
Products intersect ambient/floors, multiply left entries by directed
cancellation, and add right pop counts. At a row endpoint,
`flat(L,R)` appends the right pops after the left word.

`Common(L) = A ∩ ⋂_{q_u>0}(seed(u)∩F_u)`; empty intersection is `Fam`.
For `J ⊆ Common(L)`, `L minus J` changes `A` to `A\J` and every floor
to `F_u\J`, preserving counters. A nonempty split uses
`J = K∩Common(flat(L,R))`, memoizes `(source,J,residual weight)` and emits
an ordinary head plus residual continuation. An endpoint whose source is
its tail is deleted before splitting. Ordinary heads are not executable
weighted endpoints. Exact seen keys contain every fact and full-label field.

The original termination claim is universal: for **every** finite
source-admissible environment and finite CP term, **every** graph produced by
the stated inference rules with the four prescribed machine conditions has
finite solver processing and finite infer/saturate/compact/generalize execution.
CP's graph premise is claimed to follow from source construction, not an
assumed rejection of nonbalanced source graphs. The audit does not substitute
the easier arbitrary-graph theorem for this claim.

The local principal split claim is universal over every decomposition of the
same original comparison: its chosen head `J'` is included in `J`, and its
whole solution factors through the maximal split by residual constraints.
The whole principal claim ranges over every weighted typing satisfying the
effect-only skeleton and monomorphic recursion, with substitution, injective
ID renaming and allowed subtype widening. A mere subset-of-head argument is
not its complete conclusion.

### RT model, kept separate

RT has finite Boolean algebra `B` and finite row-only primitive graph; no source
grammar, values, constructors, generalization or colored execution. Its pair
monoid is **two full weights**, `Weight × Weight^op`, with product
`<L|R>·<L'|R'>=<L·L'|R'·R>`. It counts endpoints' tail projections in its
control graph and permits runtime rejection of nonneutral cycles. Its theorem
requires cycle-neutrality at **every** primitive-fact expansion stage.
Neutral means full pair identity, not CP's zero signed displacement.
RT's residual updates armed entries and can incorporate seeds into floor;
CP's residual changes all floors and has active-only Common plus ambient.
Identical terminology supplies no equality between these definitions.

CW uses integer signed coefficients; WC uses `(upper,n,own)` with generated
inequalities; DP/CS use same-ID `(leading pops,H,active pushes)` and no CP
ambient budget. These are changes of model, not aliases for CP definitions.

## 3. Stable dependency DAG

`V` means direct derivation checked by this producer, pending independent
review. `C` means conditional derivation with identified premises. `G` means
a missing bridge. `F` means a displayed algebraic claim has a concrete failing
instance. `U` means not independently audited. No status here promotes a
shared theorem gate.

| ID | Statement / exact owner in CP | Immediate dependencies | Audit |
| --- | --- | --- | --- |
| DW01 | finite model/kinds/seeds, §§1–3,189–357 | none; model definitions | V as definitions |
| DW02 | entry and left-weight monoids,313–357 | DW01 | V |
| DW03 | mixed Pos/Neg observation preservation,391–421 | DW02; independently defined polar observations | C/G |
| DW04 | budget conservation and strict descent,447–490 | DW01,DW02 | V for one coherent path |
| DW05 | bound storage and opposite-pair closure,555–600 | insertion-before-replay; complete scheduling | V conditional on displayed machine transitions |
| DW06 | directed-bound invariant survives construction and replay,580–585 | annotation/variance/propagation owners | G |
| DW07 | row split local soundness,602–649 | DW03,DW04,DW06; independent row interpretation | C/G |
| DW08 | local principal head and residual factorization,651–661 | DW07; fresh/shareable residual solution extension | V for head inclusion; G for full factorization |
| DW09 | finite initial graph,1063–1074 | finite syntax; finite environment instances; finite nested saturation | C |
| DW10 | every nontrivial source SCC has exactly one let-rec root,1082–1096 | formal origin-arc construction; alias/nesting coverage | G |
| DW11 | lexical bracket invariant,1103–1118 | source-owned matching-pop placement | G |
| DW12 | origin label adequacy,1120–1138 | DW06,DW11; filter/variance trace transport | G |
| DW13 | balanced or deleted self-tail contour,1140–1195 | DW10,DW11,DW12; atomization classification | G |
| DW14 | source replay cycle balance,1197–1213 | DW09,DW12,DW13 | C; source premise open |
| DW15 | counter/displacement projections,1021–1038 | DW02; pair/flatten correspondence | F for (1); V for signed additivity |
| DW16 | residual gadget contraction,1220–1234 | DW04,DW15; all incident paths retain generating provenance | C/G |
| DW17 | all-stage cycle balance,1236–1245 | DW14,DW16; replay expands to old paths | C |
| DW18 | SCC potential and bounded bicyclic counters,1253–1289 | finite graph; zero displacement of every closed walk; word composition | V for words; pair bridge G |
| DW19 | finitely many normalized full path labels,1291–1302 | DW01,DW18; bounded full-pair components | C/G |
| DW20 | residual depth at most lattice height,1312–1320 | DW04; coherent decreasing lineage through history | C |
| DW21 | finite generation at each residual depth,1322–1340 | DW09,DW17,DW19,DW20; memo/target finiteness | C |
| DW22 | exact row solver terminates,1342–1358 | DW20,DW21; once-per-key finite processing | C |
| DW23 | unique least saturation,1360–1367 | DW22; fair monotone closure with fixed identities | C |
| DW24 | whole infer/compact/generalize terminates,1371–1400 | DW09,DW14,DW22; finite compact/generalize; strengthened environment induction | C/G |
| DW25 | fresh factorization/compact representation/principality,1960–2054 | DW03,DW05,DW08; ordinary Simple-sub and generalization laws | C/G |
| DW26 | integrated termination/soundness/principality,2127–2169 | DW22–DW25; separate colored preservation/fundamental theorem | REFUTED as a conjunction in the printed scope: the required colored fundamental theorem fails for admitted CBV `I-Let`; termination remains unproved and principality remains conditional/open |

The dependency order is definitional algebra → bounded abstract graph result
plus source-generation bridge → residual-generation correspondence → solver
termination → whole inference. CP's proof writes the source bridge before
the abstract graph result; this graph separates their logical dependencies.
The principal and colored branches are not consequences of termination. The
integrated theorem as printed is refuted because its required colored
fundamental branch has a concrete admitted-term counterexample; this does not
refute termination or principality as separate claims.

RT's separate edges are `RT01 entry/weight/pair monoids → RT02 budget descent`,
`RT03 stagewise cycle neutrality → RT04 closed-walk identity → RT05 finite
path labels`, then `RT02+RT05+memo/provenance → RT06 bounded residual depth
and finite generation → RT07 conditional worklist termination`. `RT03` is a
hypothesis enforced by rejection in the draft, not proved source reachability.

## 4. Checked algebra and fixed-graph derivations

### DW02: directed entries

Freeze `(p,q,F),(r,s,G)`. Concatenating the canonical words cancels exactly
`c=min(q,r)` adjacent push/pop pairs, leaving
`(p+r-c,q+s-c,F∩G)`. The rewrite `push pop → empty` terminates by length and
has no overlapping critical pair; normal forms are `pop^p push^q`.
Thus normalization after associative word concatenation is associative, and
the independently associative meet of floors gives the claimed product monoid.
The left weight is its finite pointwise product with the ambient meet monoid.
This proves the mathematical summary operation; it does not prove that all
runtime frames with one static ID have the same effective capability.

### DW04: residual budget

For any `J⊆Common(L)`, counters and hence the active-ID set do not change.
For each active ID, `seed(u)∩(F_u\J)=(seed(u)∩F_u)\J`.
Intersecting this equality with `A\J` yields
`Common(L minus J)=Common(L)\J`, also when there are no active IDs.
If `J` is nonempty then `J⊆A`, so `A\J` is a strict subset of `A`.
Subsequent composition intersects ambient and cannot increase it. Therefore
a history that actually carries **that same decreasing budget** has at most
`|Fam|` nonempty removals. Lattice-height conventions may count vertices
rather than strict steps; the paper's “height” bound is correspondingly weak.

RT's analogous algebraic calculation also works: new entries arising from
zero-counter narrowed floors contribute factors already dominated by the new
ambient budget. Its claim that pop-only entries do not narrow Common must be
read with its entry budget definition: a pop-only entry **with a narrowed
floor** can narrow it. This does not invalidate the conservation identity.

### DW18: potential on a finite graph of actual words

Freeze a finite graph whose edge labels are finite bicyclic words and suppose
every directed closed walk has zero displacement, separately for every ID.
In an SCC fix root `r`. Define `h(v)` as displacement of any path `r→v`.
Two such paths can both be closed by one path `v→r`; zero closed displacement
proves the two values equal. Thus each edge has displacement `h(y)-h(x)`.

For a path starting at `s`, at edge `a:x→y` with normal word `pop^m push^n`,
the displacement before that edge is `h(x)-h(s)`. Every prefix during it is
at least `h(x)-h(s)-m`. Include the initial prefix zero. Consequently
`p = -min(0, all prefix displacements)` is bounded by the maximum of
`m-h(x)+h(s)` over finitely many edges and start vertices, and
`q=p+h(t)-h(s)` is bounded too. Finite IDs and finite floors/ambient then give
finitely many **flattened word** labels in each SCC. A path crosses a finite
SCC condensation DAG without revisiting a component, so intercomponent paths
retain finite bounds. This is a valid abstract proof, stronger than requiring
every cycle label to be identity: `pop push` is a nonidentity idempotent.

This derivation does not establish finite **full pair** labels under the
paper's raw pair product; DW15 and DW19 state the missing distinction.

RT04/RT05 have simpler checked proofs for their original full-pair monoid:
delete closed subwalks with identity label; every path reduces to a simple
path with the same label; there are finitely many simple paths. These results
remain conditional on stagewise full-pair neutrality. The RT one-pop self-edge
counterexample, lines 504–517, is valid in that arbitrary-graph model and
does not prove source admissibility in CP.

## 5. Exact failing step and reduced premises

### DW15: flatten is not the claimed counter homomorphism

CP lines 1024 and 1033 assert
`ctr(b diamond c)=ctr(b) diamond ctr(c)` as a consequence of entry monoid
and flatten. Under the definitions this is false without a restriction.
Fix one ID `u`, floors/ambient equal `All`, seed arbitrary. Let

```text
b = (left identity, right pop_u)
c = (left push_u, right zero)
```

Both are legal one-sided labels. Their pair product has left `push_u` and
right `pop_u`; flatten cancels and its entry counter is `(0,0)`.
Flattening first gives `pop_u` then `push_u`, whose product is `(1,1)`.
The displayed equation therefore equates distinct elements of the defined
bicyclic monoid. This is a minimized within-model algebraic counterexample.
No source term, runtime divergence or current compiler failure is claimed.

Signed displacement still adds correctly: the two counts cancel in the
difference even though normal words differ. Ambient/floor finiteness and
residual counter preservation also remain valid. DW18 needs an actual word
composition bridge; signed additivity by itself does not supply it.

The declared directed-bound condition `R1=0 or L2=0` excludes this particular
pair. CP lines 580–585 restrict its explicit statement to pairs directly
generated by annotation/structural decomposition. Missing are its inductive
preservation through stored bounds, opposite replay, W-Mix branches,
function swap, filter consumption and residual continuation. That is the
specific owner-level premise to prove, rather than repeating the potential
argument or assuming arbitrary pair flatten is multiplicative.

Also, flattened counters do not alone bound separate pair components.
For raw label `<push|pop>`, every power flattens to identity but its separate
counts grow. This label may be removed by mandatory W-Mix; it is **not** a
counterexample to a machine that normalizes it first. It identifies why DW19
must specify the exact canonical pair/branch representation and prove that
its full cache keys are bounded by the established word bound. The paper's
phrase “canonicalize where necessary” is not that representation theorem.

### DW03, DW07, DW08: observation and factorization

Mixed normalization's proof asserts what Pos/Neg can observe rather than
giving an independent observation relation and a proof of its relevance
quotient. “Pure pop does not increase permitted head” proves one subtraction
observation only, not arbitrary negative/positive contextual observations or
complete comparison equivalence. This branch requires the separately scoped
colored/polar semantics, which this audit does not certify.

The head-inclusion half of local principality is immediate:
`J'⊆K` and `J'⊆Common(L)` imply `J'⊆J`. The second half needs a joint
solution-extension construction. The proof says to leave `J\J'` in gamma
and invokes its freshness, but supplies no substitution proving both
`alpha<:[J;gamma]` and `gamma @ (L minus J)<:beta` for the original entire
decomposition, with correlated bounds and regular tails preserved. Hash-cons
reuse further means gamma is not fresh for every subsequent target.
Required bridge: same source/head/residual key has one principal residual
that simultaneously extends all compatible target constraints. The subset
argument and initial allocation freshness do not prove that conclusion.

Local soundness is conditional on an independently specified weighted row
interpretation. At CP 644–649 it reconstructs the original comparison by
the described split meaning. That is useful rule consistency but cannot
alone establish colored/source semantic preservation. Self-tail deletion
likewise needs its own row/colored observation preservation theorem, not
only a termination motivation. CS explicitly leaves coinductive solution-set
equality/infinite observations open (1546–1548); CP's stronger integrated
principal use cannot inherit that stronger conclusion from finite observation.

### DW09–DW14: source construction is the critical bridge

Finite **syntax traversal** is established: I-Ref for monomorphic recursion
returns the same root and does not reinfer the RHS. This neither proves
acyclicity nor bounds the number of facts saturation creates.

DW10's proof treats child graphs as disjoint and every nonrecursive connector
as a forward arc. Displayed I-Ref shares monomorphic type/row ports, and
I-App generates a comparison to a function containing argument/result ports;
W-Fun reverses domains. No complete origin-arc construction shows these
shared and reversed ports have the asserted forward orientation. A fresh
result port alone does not prove it. Nested let-rec can reference outer
monomorphic roots; the argument “nested root is fresh” does not prove that
two roots cannot occur in one reachable row SCC. This is an unproved
classification, not a demonstrated source counterexample.

DW11's proof (1112–1116) says lambda/application/handler place matching pops
at return and operation exit. The displayed generation rules 813–911 insert
push annotations, result filters and ordinary shape/handler constraints;
they give no explicit matching-pop source constructor or row-atomization
rule. Operational pop-paint is separately defined later. A well-bracketed
runtime activation does not make every subtype-replay contour a complete
activation. Needed: an exact source/atomization judgment emitting marker
traces and labels, then a proof that every executable closed replay walk is
an image of the claimed balanced-or-deleted contour.

DW12 also says filter leaves counters unchanged (1136), while W-Filter
(545–553) consumes the left weight after checking and retains only right
pop. A provenance rule must account for the consumed left segment or state
which observation has ended; blindly transporting its counters unchanged
does not follow from the displayed machine. Function swap has a similar
unwritten trace orientation premise.

DW13 applies single-root and lexical bracketing to classify every other
recursive contour as entry/exit-balanced. That exhaustiveness statement is
the essential lemma, not a consequence of monomorphic lookup alone.
Theorem DW14 is valid **if** DW12/DW13 hold, but they are not independently
established here. Source-admissibility's recursive definition includes schemes
obtained by saturation/compact. The whole-inference proof can avoid a circular
solver premise only with a well-founded simultaneous source/environment
derivation and invariant-preserving scheme extraction/instantiation.
Its stated environment class also omits the weighted local monotypes added
by I-Lam and the open monomorphic root added by I-LetRec; applying an IH
quantified only over source-admissible environments to those extensions
requires a strengthened environment theorem. This is an induction-domain
gap, not permission to restrict ordinary local source.

RA explicitly records another source/operational bridge: effect sequences
must fan out directly to predicate/filter uses before replay. Its inserted
paragraph near the row-termination theorem says intermediate join variables
in the Rust implementation can expose a var-var cycle not represented by
the assumed lowering. It records count-free same-alias storage subsumption
as an implementation rule and calls for normalization/revalidation.
This historical acknowledgement localizes correspondence debt; it neither
repairs CP's missing source constructor nor proves the subsumption sound.

### DW16–DW24: residual history and worklist closure

Residual subtraction preserves counters of its **continuation** and strictly
reduces its ambient. A contraction of every later closed walk additionally
needs all incoming/outgoing incidences of a shared residual node to map to
compatible generating endpoints. CP describes insertion by head/continuation,
but provides no inductive provenance invariant for later replay, repeated
target reuse and atomized structural bounds. Its proof's reference to
projection-properties(3) for counter preservation is a citation mismatch;
(4) is the residual-counter clause. Correcting that reference would not
provide the missing path-incidence invariant.

DW20's local lattice argument is valid on a coherent provenance lineage.
To apply it to “every generation history”, explicitly define such a history
through memo sharing, Replay and ordinary head facts, and prove it never
restarts with a fresh ambient budget on the same claimed residual lineage.
CP separates ordinary head facts from weighted endpoints; RT does not use
that same fact distinction. Their finite-depth inductions therefore require
their own history invariants, not a common informal phase picture.

Given finite full labels, bounded well-defined depth and finite memo-key
candidates, DW21's induction is correct: each finite stage offers finitely
many source/head/residual triples and finitely many existing targets. Given
that finite state space, DW22's once-per-key proof is correct. Its finite
processing assumption includes complete opposite-pair enumeration and
enqueue/seen lifecycle; stored bounds alone do not establish active replay.
DW23 additionally assumes fairness, monotone checking/failure semantics and
history-independent canonical identities. DW24 still needs the source
environment and compact/generalization invariants already identified.

## 6. Historical proof status and imported results

| Lineage | Author's recorded status | Audit result for assigned group |
| --- | --- | --- |
| CW | Principal weighted scheme, static/dynamic correspondence, preservation and termination are conjectures; termination explicitly most uncertain,1191–1206 | Integer-vector normal form and signed path additivity work; no bounded replay theorem is supplied |
| WC | Transition definitions and invariants; Common/subtraction themselves partly referenced rather than defined | Explicit insertion/replay closure provides a useful machine skeleton; no proved termination or principal theorem to import |
| DP | Principal finite graph claimed separately from actual worklist; termination and self-tail solution preservation remain open,166–172,1068–1080 | Bicyclic fixed-family composition valid; principal residual/compact/generalization remain conditional |
| CS | Adds colored results for normalized well-bracketed realization; concrete marker placement, termination, family-argument relation and stronger self-tail observation remain open,1530–1548 | Weight/split route remains DP-like; guard-snapshot revision changes hypotheses; it supplies no source termination theorem |
| RT | Proves constructor-free termination under finite data, exact keys, stagewise neutrality and residual memoization | Fixed-graph neutral-path mathematics validated; dynamic residual-history bridge remains conditional; rejection is part of this model |
| CP | Claims unconditional termination for generated source graphs plus soundness/principality, including integrated theorem | Concrete DW15 failing equation; unresolved source/atomization/bracketing and residual/full-label bridges; original source theorem not discharged |
| RA | Adds fan-out/provenance-normalization premise and documents implementation lowering gap | Alternate revised premise; cannot be silently promoted or treated as a merged correction |

CP's compact representation invokes the ordinary Simple-sub coalescing proof
at 1979–1984. Principal let and let-rec invoke a “standard generalization
lemma” at 2000 and 2043; no full level/extrusion/generalization lemma is
displayed in the assigned papers. Extending that ordinary result to
directional wrappers, floor-only state, IDs, filters and joint residual
constraints requires the actual extension hypotheses. CP's assertion that
ordinary coalescing plus mixed observation suffices is not an exact
source-to-implementation correspondence.

The recursive solution morphism argument itself has useful structure:
map the unique monomorphic root to the alternative recursive type, map
fresh skeleton variables by translation generality, retain every RHS
constraint and verify the closing constraint. It is conditional on the
RHS factorization/row relation and does not create a least regular solution
or principal exported object merely by naming such a morphism.

No external Simple-sub paper theorem was independently reverified in this
pass. Citations to Parreaux and Damas–Milner are historical imports, not
evidence that these extended hypotheses were checked.

## 7. Documented historical seams and current transfer ledger

The anchor spec and implementation note do **not** state CP's row endpoint
semantics. Spec lines 160–186 and implementation “Row Split Contract” first
distribute right pop to the target tail and compute Common only from active
left pushes. CP lines 604–615 flatten right pops before Common. For example,
left `take(Empty,u)` plus right `pop(u)` has empty left-only Common but
flattened identity has Common `All` with full ambient. W-Mix ordering may
affect whether such a raw pair reaches the endpoint, so this is a documented
definition discrepancy, not an established program-result contradiction.
Spec 339–344 explicitly keeps solver ambient/floors out of colored visibility;
CP includes ambient/effective floors in Common. The note also records
same-boundary alias subsumption, whereas CP's theorem uses full exact keys.
Translation must specify all these distinctions instead of importing the
complete paper as an implementation proof.

Current comparisons use only pinned `67830dce1` sources:

| Reuse class | Historical item | Exact current source / reason and necessary transfer premise |
| --- | --- | --- |
| Reusable as stated, producer validation only | DW02 entry monoid; DW04 one-lineage set budget conservation; DW18 finite word-graph potential theorem; RT04/RT05 neutral graph lemmas | Mathematical results with their original model/hypotheses; no source or implementation inference follows |
| Conditional on a proved translation | ID freshening and monomorphic recursive sharing | `2026-10-08-source-generalize-definition.md` §§2–4 preserves original scopes, fixed coordinates, once-per-frame binders and aliases. Prove a joint scoped map from old schemes to actual source Generalize, including dependent residuals; independent marginal substitutions cannot supply it |
| Conditional on a proved translation | Old active-ID capabilities/Common and normalized markers | `2026-10-10-contextual-attachment-admission-design.md` §§3–4 retains exact occurrence, grouping, operation order/shared children, receiving filters and replay provenance. Prove old-ID to attachment-instance map, directed operation and observation preservation, including source-owned `both`, `swap`, filter discharge and freshening |
| Needs repair | DW15 flattened-counter homomorphism; source cycle-balance proof | Concrete equation failure in §5 and missing generation owners. Repair the proof or derive the proper restricted composition law before transfer |
| New obligation | Generic current contextual termination | Attachment/admission §5 explicitly describes source-reviewed PUSH and POP/PUSH circuits requiring exact symbolic acceleration and leaves mixed components open. Old zero-displacement assumption is not selected for every such current circuit; do not reject ordinary source to regain it |
| New obligation | Finite residual identity space in the current algorithm | `2026-10-10-contextual-residual-lineage-selection.md`, Selected policy and Preserved contract: separately constructed recipes retain lineage even after row/key equality, with current/future lower fan-out. Prove finiteness/progress for actual recipe creation and transport; CP source/head/weight memo sharing cannot replace the selected lineage policy |
| New obligation | Parent/copy intrusion preserves termination, soundness and required principality | `2026-10-10-parent-copy-scc-intrusion.md`, Selected operation/Value-reference clarification; `2026-10-12-intrusion-value-type-association.md`, Qualification and frontier. Current SCCs are actual Value references, with type occurrences associated to values; only qualifying retained extrusion pairs become equal. Old constraint/row SCC potential supplies no association or equality-preservation theorem |
| New obligation | Complete Call extension of old I-App | `2026-10-07-complete-call-contribution-definition.md` §§2–4 preserves callee computation, whole carrier, actual provider/entry, original pending suffixes and future alternatives; `2026-10-10-call-reify-construction-direction.md` Scope/Required next construction retains actual `P_old`. Prove the full source/consumer bridge; CP's ordinary function-shape constraint alone cannot supply it |
| Unreviewed / not transferred | Whole colored theorem, strongest principal export, all family arguments/ADTs, complete source acceptance | Outside this leaf's assigned proof validation and/or original model. Current design and proof dependencies keep their original obligations |

`2026-10-10-practical-complete-call-production-gate.md` is Reviewed and
non-authoritative; its governing-source table and success criterion explain
the complete contract, but approve no implementation. The five-point
Authoritative `2026-10-11-yulang-inference-top-level-principles.md` §§1–5
requires native deterministic Simple-sub construction and proved central
invariants, with necessary abnormal safety. It supersedes blanket rollback
requirements in older contextual clauses; it does not waive soundness,
principality, source correspondence, complete Call, hygiene or termination.

No old row/constraint SCC is identified with the current Value-reference SCC.
No attachment, provider, witness, color, residual recipe or description frame
is identified merely because its endpoint or projected observation agrees.

## 8. Obstruction economy and next decisive evidence

This packet did not run two new equivalent proof attempts. It audits the
recorded lineage: CW and DP/CS already leave cycle bounds open, RT proves an
arbitrary-graph sufficient condition, and CP attempts source bracketing.
Their recurring premise is the **constructional correspondence from actual
source-generated replay walks to bounded directed words**, including exact
normalization, filter/variance and residual incidence. Another potential
lemma or a larger finite graph search would leave it untouched.

For CP's original unconditional theorem this is a correctness/natural-progress
premise, not optional characterization. The source constructor originally
knows annotation lifetime and marker placement; atomization/replay must retain
the matching typed provenance. That is a constructional debt candidate under
`compiler-engineering.md`, not an adopted redesign. Current semantics cannot
be weakened to recover the old balance assumption.

One next action: primary dispatch independent document review of DW15 and the
DW10–DW14 source bridge, then assign an exact historical derivation of the
origin-arc/row-atomization constructors with the complete original CP source
domain. If this bridge was never defined, record that precise missing premise
and separately assess a natural current construction; do not rerun DW18.

## 9. Checks, resources, hashes and commit packet

Checks already run: read-only `git show`, `git log --follow`, exact deletion and
rename `git show --stat`, `git diff` for CS and RA variants, `git ls-tree`, `rg`,
line-numbered section reads and Python SHA-256 of immutable document objects.
No LaTeX build, Cargo/build/test, source experiment, inference probe or code
inspection ran. No Git mutation, external communication or child dispatch ran.
One lightweight shell/read process at a time; no persistent process or cache
output. The only changed path is this lease. Paper blobs are unchanged.
Requested runtime: `gpt-6.1-sol` / high. Observed runtime model/effort metadata:
unknown. `.codex/config.toml` registers prover and Sol/high defaults;
`.codex/agents/prover.toml` omits model/effort pins. Reading them is not evidence
of a hot reload or observed runtime override. No Astra escalation requested.

| Dependency | Git blob / SHA-256 |
| --- | --- |
| CW at deletion parent | `699bca3b9a69f0db90a0f6095ebad5b190a1dfae` / `9a979b1460e6a51b1d7ce429440e5ee942f8b2e54d3d427dee88b2815bbd843c` |
| WC at deletion parent | `e2266c6af414189b33faa1452cf70491017eaf1b` / `bc9704668ed09647cd4f342e8d02173319b13ac36b3c65dab985d945917a7234` |
| DP at deletion parent | `a1f4443ecbe8f4fd0879f6e3811f74dc28a6280b` / `ffb2985b490996545dc969787c71da4dbdcbf32448a8b3550133a4bdd3c9d085` |
| CS initial | `8214345e9584f3822788c24e1a94215eae97a36d` / `173e46b5f92e3992e44fbf6825eeeb36dcd0a4ec6c09ed197c88fd2cc3a2c9ea` |
| CS revised | `e7f6e1d8585946c63346c5aaadd9895ddfe95f6b` / `b9c9acf45af326485ca77403393a0a48dec5823e5c826631df4821892ae80a90` |
| RT at deletion parent | `08af36fe5abf2c996ca773a69bb842d3b77c62e2` / `e5849c312d1797011b18984c280db3a4f2ed756085223d573eabedf443d919f0` |
| CP at Oracle anchor | `4d935400d7c437fa97be418f569b820e3ee8323e` / `efed007a3848c94f9d8925985f66e76ab86082dcb094c7ec3851b2bdd7082843` |
| RA at alternate commit | `3cfbae0d211273046b0ebe65a3d526e2fedef831` / `31911eb0ae8351703e0b1fcfe2b9c3c3443254be0d8fcc5395ff66914dee84bf` |
| Anchor spec | `9f791220f6502c915faaa146b3f7cf3a95a7b7ed` / `fbd9588b489dbc6b987c5e7a11d1d3f1bdc696be3bed605e5dcac849f42cda7a` |
| Anchor implementation note | `12f8fe54344a10ec2de43955b592b750a3a8d2ed` / `25ff7f5e8ae4133291c671744a3ebc95789d5ebea82684e9c6105cba54fef10f` |

Commit packet:

* Exact path: `notes/theory/oracle-inference-document-audit/directed-weights-termination.md`.
* Baseline: `67830dce14e6987b37e47b2540c204fcd06a92c6`; Oracle and
  historical dependencies above. Changed dependency hashes: none by this leaf;
  primary must revalidate current comparison documents against the pinned baseline.
* Review: producer audit only; fresh independent review pending; no original
  source termination, soundness, principality or F5 replacement gate closed.
* Proposed message: `research: audit Oracle directed weights and termination dependencies`.
* Shared-record deltas left for primary/curator: link this artifact; retain six
  lineage entries and RA alternate; record DW15 equation failure and exact
  DW10–DW14/DW16/DW19 residual/source bridges as unresolved; retain elementary
  algebra and conditional fixed-graph results with their hypotheses. Do not
  mark the exhaustive whole audit or original inference goal complete.

Unverified scope: every revision of each lineage, complete archived May
documents, entire CS/CP colored proofs, external ordinary Simple-sub theorems,
concrete Oracle and current compiler correspondence, and the rest of the
catalogue. This first coherent pass establishes a dependency audit, not an
exhaustive historical certification.
