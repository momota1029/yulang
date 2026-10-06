# Directional source relation: scheduling and generalized-use falsification

Date: 2026-10-06
Status: independently reviewed conditional finite-model research; no source theorem
Review: compiler referee and spec auditor; one minor coverage-reporting issue repaired
Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Branch supplied by primary: `research/simple-sub-intrusion`
Role: adversarial researcher and executable-model producer, not reviewer
Exclusive lease: this note and `tools/research_directional_source_relation.py`
Implementation authority: none

## Result and exact claim classes

The selected direction survives the adversarial checks when its premises are
retained with original identity. The useful failure boundaries are stronger
than a local seed/upper set join:

1. A seed whose logical justification precedes an exposure can physically
   arrive after that exposure. Replay must still obtain the same protection.
   Conversely, completed seed membership cannot supply `ProtectedVarAt` for
   a genuinely later semantic seed. The approved local clause does not decide
   that late applicability.
2. Whole-scheme transport with an injective, capture-preserving use mapping
   preserves upper/lower origins and independent provider evidence. Merely
   obtaining a witness separately at each fresh use does not establish a
   witness for the same original `xi=(nu,K,D)` at all uses.
3. Lower/provider evidence does not generate protection from the formal seed,
   but remains an active constraint on the original relation. Omitting that
   evidence can change the solution set.
4. Graph extension by deterministic protection records preserves unchanged
   predicates on the old row. That statement cannot prove preservation of a
   final predicate that reads protection and supplied observation evidence.

The closure theorem below is conditional on supplied source facts,
applicability certificates and complete-scheme transport certificates. The
checker exhausts physical deliveries of those inputs; it does not derive
them from Yulang source. The two-history witness concerns local-rule proof
derivability and information loss. It is not two completed source semantics,
an accepted source-program counterexample, or a proof that genuinely late
seeds must remain unprotected. The observation test is an abstract predicate
countermodel, with no invented source execution trace.

## Governing sources and supplied versus derived premises

The current user decision, recorded in
[the directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4, fixes exactly this positive/negative pair:

```text
ProtectedVarAt(k,v,sigma,u), SourceUpperUse(u,v,U,sigma)
    => NewProtection(k,u,outEff(U))

existing SourceLower(L,v,sigma), seed(k,v,sigma)
    !=> new protection on outEff(L) from this seed
```

The same source explicitly declines a global wall-clock rule, arbitrary
late-seed replay policy and seed aggregation across recursive components.
An independent inherited protection on the lower provider survives.
[Local source generation](2026-10-06-directional-protection-source-generation.md)
§§2–3 already separates enumeration of certified records from semantic
stage reordering. Its graph-extension proof is expressly limited to
unchanged old-row predicates. The prior
[checker](../../tools/research_directional_protection.py) is a bounded local
join; this work tests replay, closed-scheme materialization and shared use
witnesses beyond that domain.

[Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–2 and 5 require original position/scope preservation through
generalization and use, one original joint assignment, source-generated
typed incidence, comparison-independent admission, and unchanged actual
callable role/entry. They leave the exact formation and generalization
judgments open. Source annotations, printed schemes and internal views are
different objects. Endpoint equality and Q cannot supply their evidence.

[Typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6 gives parameter/name/result skeletons under its stated source premises;
recursive references reuse existing nodes. It leaves recursive inference
and generalization/lifecycle unresolved. No Value-entry-implies-Pure rule
is adopted. [Typed boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md)
§2 and §4's structural-observation subsection distinguish typed `Flow`
transport from observation at executing view positions. Neither lexical
capture nor shape supplies an event-to-port witness. Those exact primitives
remain supplied here.

The [registration schedule derivation](2026-10-06-source-registration-schedule-equivalence.md)
H1–H8 and finite-closure section already prove a conditional monotone
worklist theorem and exhibit missed replay. This note specializes the
failure to directional stage/applicability evidence and whole generalized
use packets. It does not reinterpret that theorem as raw-source generation.
The [ambiguity audit](2026-10-06-source-registration-ambiguity-audit.md),
“Two partial protocols and their exact residual,” prevents presenting two
partial input histories as complete alternative source calculi.

Repository rules read: `AGENTS.md`, `rules/design-authority.md`,
`rules/research-lab.md`, `rules/git-concurrency.md` and
`rules/orchestration-budget.md`. `tasks/current.md` and the design index
were navigation and scope inputs. No current authority is inferred from a
map, proof signature, execution count or this producer's own checking.

## Finite relation model and schedule theorem

Fix one supplied finite packet P. Each record carries original component,
binder, scope and source/proof occurrence identity, plus its current use and
scope. The packet contains:

| Record | Meaning in the model | Source status |
| --- | --- | --- |
| `Seed(k,v,stage)` | justified inferred-variable seed | supplied; not created by a bare external Name |
| `Upper(u,v,c,a,b,d,stage)` | original Function demand with its output-effect occurrence | supplied source constraint; not a successful comparison |
| `At(k,u,stage)` | the exact `ProtectedVarAt` certificate | supplied; not computed from integer order |
| `Lower(l,v,g,h,stage)` | retained provider/recursive lower bound | supplied; no protection-producing rule |
| `Inherited(p,l,g,receipt,result)` | independent provider packet | supplied and transported without erasure |
| `Closed(J,P)` | whole generalization packet is closed | supplied proof premise; not proved from queue emptiness |
| `Use(J,t,rho)` | one coherent use correspondence | supplied certified injective transport of every quantified coordinate |

Logical stages in the fixture are source/proof labels. They are never the
position in a delivery queue. In particular the implementation does not
infer `At` from `stage(seed) <= stage(upper)`; an applicable source proof
must supply that record. Linear labels 0, 1 and 2 make the two abstract
histories easy to distinguish, without selecting a global stage calculus.

The model has only two kinds of productive rule:

```text
Seed, Upper, exact matching At => New(upper's out.effect)
P, Closed(J,P), Use(J,t,rho)    => rho(P), as one whole packet
```

Matching includes original component/binder/scope, current scope and use,
exact shared root and exact seed/exposure occurrence identities. The first
rule has no lower-bound branch and no solved-value or Q input. The second
rule cannot fire while any original packet record is absent. The use map
renames all four quantified Function coordinates together and leaves
captured provider/root/receipt/result coordinates rigid. It retains the
original identities while giving the materialized packet its current use
and scope. Directional protection is then recomputed from the transported
certificates. No source-origin or stage certificate is generated by transport.

Let T be these finitely many ground positive rules and I the eventually
delivered supplied records. Define

```text
F(X) = X union I union {conclusions(t) | t in T, premises(t) subset X}.
```

F is monotone and inflationary over a fixed finite universe. Every delivered
record and every correctly produced conclusion belongs to its least fixed
point L. A fair run that delivers all of I and replays every newly enabled
rule finishes at a set X containing I and closed under T. Thus `L subset X`
by leastness, and `X subset L` by step induction; `X=L`. Therefore complete
physical delivery orders give the same whole record relation, including
lower and inherited evidence. If identities differ administratively, the
comparison requires one coherent injective renaming of every coordinate.

The selected upper rule and original-identity requirements ground the first
clause. Existence/completeness of P, At, Closed and Use are explicit
conditions. Neither the theorem nor the checker proves those certificates
for arbitrary recursive source components, or B-equivalence of a scheduling
optimization. A recursive cycle without a supplied base fact contributes
nothing in this least positive closure. It is not unrolled or assumed
coinductively complete.

## Physical late delivery versus genuinely late semantic introduction

For the positive fixture, retain

```text
logical seed stage 0; upper exposure stage 1; At(k,u,1)
physical delivery order: Upper(u), At(k,u,1), Seed(k)
```

After the last insertion, the exact rule is enabled. A replay-safe scheduler
produces the same upper protection as seed-first delivery. An implementation
which tests only when Upper arrives misses it. Publication on its empty
queue is therefore not semantic closure. Physically receiving an earlier
binder seed late is an administrative condition, not a new language case.

The smallest stage-erasure collision for this local proof cut uses one seed,
one upper exposure and the positive case's one applicability witness:

| Abstract history | Seed logical stage | Upper stage | Supplied `At(k,u)` | Selected local rule entails protection? |
| --- | --- | --- | --- | --- |
| H-before | 0 | 1 | yes | yes |
| H-after | 2 | 1 | none | no derivation from the supplied local premises |

Erase logical stages and applicability evidence, keeping final source seed
and upper inventory, binder, scope, component, use and Function shape. The
two inputs are identical. Their local-rule derivability differs. Hence no
function of that erased inventory can exactly recover whether the displayed
rule has a proof for both histories. Removing the seed or exposure removes
the positive rule; removing the applicability distinction removes this cut.
This is minimality of proof coordinates, not source-program minimization.

The final column for H-after does **not** say that an authoritative late rule
has forbidden protection. It says that no such rule or certificate is among
the supplied premises. The authority covers “already protected while still
an inferred variable”; it does not specify genuine late semantic seed
introduction. A future proved clause could justify a new exposure or a
particular late applicability. Final inventory and physical replay alone
cannot prove that clause. Conversely, no new decision is needed merely to
deliver a certificate that was logically justified earlier.

The irreducible source premise for a whole-source producer is therefore an
exact coverage judgment, for each original exposure and seed origin:

```text
source proof of C entails ProtectedVarAt(k,v,sigma,u)
    iff the completed original incidence inventory retains that certificate.
```

Its derivation must state which logical stage/source premises license each
pair and how those pairs survive coherent generalization/use. If an envelope
requires genuinely later semantic introduction, the additional applicability
clause must be derived or separately selected. This note does neither. It
does not add E/R, whole-result defaults, equality alias propagation, arbitrary
variable-to-variable transport, receiver-expiry-only reasoning, or a
naturality-only singleton route.

## Generalized uses, lower evidence and observation-sensitive predicates

The model materializes two uses from the same original closed packet. All
original binder/scope/component and occurrence IDs survive. Each use has
fresh local `a,b,c,d`; the captured formal root and independently inherited
provider, receipt and result remain shared rigid coordinates. A split
freshening which leaves At attached to the old use loses the required mark.
A map that freshens a captured root is rejected. Whole-packet closure is a
premise, so early materialization cannot silently publish just seed/upper/At
and omit lower/inherited constraints.

Preserving those record identities is necessary but not enough to preserve
the full solution relation. Use two original rows:

| Original row | `nu(env:f)` | `nu(use1:c)` | `nu(use2:c)` | K | D |
| --- | --- | --- | --- | --- | --- |
| xi0 | 0 | 0 | 1 | 0 | 0 |
| xi1 | 1 | 1 | 0 | 1 | 1 |

Use 1's predicate `use1:c=0 and K=0` holds at xi0. Use 2's predicate
`use2:c=0 and D=1` holds at xi1. No original row satisfies both. Marginal
stitching manufactures `(env:f=0,use1:c=0,use2:c=0,K=0,D=1)`, which satisfies
both predicates and is absent from the source relation. This is an abstract
counterexample to independent existential witnesses, with precisely one
original `xi` required. Two uses and two anti-correlated rows are sufficient;
one use cannot show cross-use stitching. The numeric coordinates are a
finite test alphabet, not a source interpretation of actual K or D.

Likewise, a retained lower predicate `D=nu(env:f)` on the eight Boolean
triples admits four original rows. Dropping it admits eight. The lower record
is inert as a protection producer and active as a constraint. A representation
that treats “does not acquire protection” as “may discard provider evidence”
therefore fails independently of upper/lower endpoint aliasing.

Finally, take those four constrained rows and supply an abstract observation
flag O at the original upper occurrence, represented by `nu(env:f)=1` in this
test only. Let the test's final predicate be

```text
Final(xi,M) = not (O(xi) and D and ProtectedUpper(M) and not K).
```

Here K is a toy grant flag and D a toy liveness flag. These stand in for
externally supplied dependent evidence; they do not implement Yulang
`Observe`, handler selection or receipt formation. With no upper protection,
all four rows satisfy Final. With the generated upper mark, three do. Thus
the deterministic record graph can erase onto exactly the original relation,
and every unchanged old-row predicate can commute with erasure, while this
protection-sensitive final predicate changes. This falsifies the *logical
inference* from unchanged-query extension to arbitrary final-predicate
preservation. It is not a failure of the user-selected protection semantics
and not a claim that the eventual seed/refined source relations differ in
this way. The actual preservation theorem must interpret its full dependent
predicates with independently supplied typed observation/receipt premises.

## Exact executable coverage and shortcut mutations

Checker: [research_directional_source_relation.py](../../tools/research_directional_source_relation.py).
Run from repository root:

```sh
timeout 60s python3 tools/research_directional_source_relation.py
```

The final deterministic run passes. Coverage is deliberately small:

- All **5,040** permutations of five original source/proof records, one
  closed-scheme certificate and the first use request; the second use request
  arrives last in each. Compare the complete closure, not just mark counts.
- One additional schedule delivers both use requests before closure and the
  reversed original packet, covering the opposite use request order.
- Symbolic rule matching has no denotation input. A separate global-equality
  mutation consumes an explicit equal-denotation assignment and shows why
  that assignment must not merge original upper/lower protection origins.
- One two-history applicability/stage erasure collision, one focused
  physically late earlier-seed delivery, a variable-equality alias case,
  a mismatched current-scope case, and one invalid captured-root transport.
- Two anti-correlated original joint rows; eight lower-predicate candidate
  rows; four observation-sensitive constrained rows.
- Ten rejected named shortcuts, listed below.

| Shortcut mutation | Discriminating result |
| --- | --- |
| Physical arrival order is logical stage | upper/At/seed one-pass misses the required positive mark |
| Final seed inventory invents late applicability | H-after gains a mark without supplied At |
| Globally merge equal effect protection | equal c/g denotations newly mark lower occurrence l |
| Variable value equality creates source applicability | equal-valued distinct roots gain an unsupported upper mark |
| Split use freshening breaks At | use-local seed/upper cannot join old-use At |
| Cross-use witness stitching | two individually satisfiable uses manufacture a non-source xi |
| Drop lower evidence | four constrained rows become eight |
| Erase inherited packet | original independent provider key disappears |
| Freeze generalization before whole packet | materialized use has three of five required records |
| Unchanged query filtering implies observation preservation | Final admits four rows before the mark and three after it |

The delivery comparisons share exactly the supplied inventory and rules.
They are schedule consistency evidence conditional on those premises. The
independent expectations are the literal required mark table, whole original
identity/rigid-packet preservation checks, the explicit anti-correlated row
table, and the independent final-predicate truth table. No parser, Oracle,
production handler, arbitrary Function solver or source trace is used.

One Python process only, standard library, internal 256 MiB address-space
cap and 55 CPU-second cap, external 60-second wall cap. There was one initial
pilot run and one final run after narrow model/test corrections; no larger
search, process pool or Cargo invocation. Stop at the decisive witnesses.

## Frozen dependencies and commit packet

The files in this snapshot were byte-equal to the pinned baseline when
hashed. Unrelated branch movement does not change that equality. These hashes
record consumed authority/data inputs, not review certification.

| Dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `c5ab6ebf0d72fda4c025abc3a0ec9d57c9015a0c8e4ba65900ed385fb62fb9b3` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/orchestration-budget.md` | `32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716` |
| `tasks/current.md` | `7c080799a8593f5b24dea2bd22c1f4c0a59c47b2cb424af808ba25a9d4f0e233` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-06-directional-protection-source-generation.md` | `3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185` |
| `tools/research_directional_protection.py` | `097e23f8c11e62fd9fe27179814d1b033eba5b824042c20a39682ca2bc9e5275` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/progress/2026-10-06-source-registration-schedule-equivalence.md` | `971ef7ab4f85933a32bd8093c4198066c9ffaac816c12b07974ff18f2131f1d9` |
| `notes/progress/2026-10-06-source-registration-ambiguity-audit.md` | `d2d70e9197ee6c24080c2ae26909f2b984840c4be7f4dfce505376900de2c9a4` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |

Commit-ready packet for the primary, contingent on its final lease/diff
inspection:

- Exact paths: this note and `tools/research_directional_source_relation.py`.
- Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`; dependencies unchanged
  from this baseline at freeze.
- Claim/review status: independently reviewed conditional closure argument
  and bounded discriminating countermodels; the producer did not self-certify.
  No theorem-edge closure, authoritative semantics or implementation claim.
- Verification: the bounded command above; direct baseline byte comparisons,
  dependency hashes, exact leased-output/path and whitespace inspection.
- Proposed checkpoint subject:
  `research: falsify directional source relation shortcuts`.
- Shared records deferred to primary/curator: `tasks/current.md`,
  `tasks/research-lab.md`, `notes/design/INDEX.md` and theory maps. Record
  physical replay as conditional administration, retain original
  applicability/complete-scheme formation as open, and distinguish the
  graph-extension claim from full protection-sensitive relation preservation.

No production changes, shared records, existing expectations, approvals,
question-board files, Git index/ref mutations, or other workers' outputs were
written. No children were launched. General source enumeration, exact semantic
late applicability, recursive lifecycle, source-derived whole-scheme
certificates, actual typed Flow/Observe/receipts, full seed/refined relation
preservation, soundness/principality, source adequacy and Option A/2
production containment remain unverified. A producer cannot certify its own
artifact. Freeze ends this lane; broaden checks only for a concrete review
finding or a new independently derived source premise.

## Independent review and focused correction

The [whole-source review record](2026-10-06-directional-whole-source-review.md)
records the separate compiler-referee and spec-auditor assessments. Neither
found a blocking or major issue. The compiler referee found one minor
coverage overstatement: an unused `Xi` value was constructed in each of four
iterations, while the same symbolic closure was checked each time. Those
iterations and the reported `endpoint_valuations` count were removed. The
independent explicit equal-denotation mutation remains. This corrects the
reported executable coverage; it does not change the directional rules,
schedule domain, countermodels or source claim boundary. The focused final
checker and link/whitespace checks were rerun by the primary after correction.
