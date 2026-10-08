# JOINT-DEC: a conditional residual-game decision construction

Date: 2026-10-08
Status: Conditional derivation repaired after accepted MAJOR; delta review pending
Implementation authority: none
Gate status: unchanged; JOINT_DEC remains OPEN-PROOF
Baseline: `87467e190cff6a8c208d07c1b1f0a1769e81389e`
Repair baseline: `20375f34eeae91c7f29473f3a787514c37c74abb`
Original artifact commit: `6967ac589` (primary-supplied identifier)
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only

## Objective, authority and method

Formulate a sufficient effective residual decision certificate that keeps
every original active predicate, original binder position, and simultaneous
witness. The method is induction on the original finite formula/binder tree,
using a finite abstraction of legal *prefix extensions*. It is an alternative
residual route, not another candidate-count experiment or halting extension.
The derivation below supplies an algorithm once its certificate exists; it
does not construct that certificate for the whole Yulang source envelope.

Exact governing inputs:

- [successor-proof-obligations.md](../theory/successor-proof-obligations.md#joint-dec), PURE-DEC, PRIMITIVES, ALL-WORLD,
  CTX-FINITE and JOINT-DEC. The edges are prerequisites of a sufficient route,
  not a theorem that their names jointly imply a solver.
- `2026-10-05-pure-structural-effective-decision-corollary.md`, Claim and input
  boundary, Proof, Boundary: the `8^N` bound is for the normalized pure package.
- `2026-10-03-source-context-finite-closure.md` §§2–6: supplied comparison
  contexts and conditional terminating closure, not finite semantic worlds.
- `2026-10-03-open-residual-factorization.md` §§2–5, 7: successful normalization
  preserves the same residual operands; finite residual syntax leaves joint
  satisfiability open.
- `2026-10-07-successor-global-synthesis.md` §§2.1–2.3, 6: one original
  `xi=(nu,K,D)`, original binder tree and independent source predicates.
- `2026-10-07-successor-effective-projection-round2.md` §§1–4, and
  `2026-10-07-successor-round2-review.md`, projection review: finite incidence
  and eligible equality orbits do not decide untouched non-name leaves.
- `2026-10-05-residual-admission-source-premise-audit.md`, Result and Minimum
  missing source rule: no exhaustive varying-endpoint primitive law is supplied.
- Approved `production-function-inlet-context-domain/approved-answer.md`,
  Decisions 1–5: all independently compatible punctured contexts, including
  other-program and future use, with comparison-independent admission and
  Option 2 extras. This tracked answer is unchanged from the pinned baseline.
- `2026-10-02-source-interface-adequacy-theorem.md` §§2, 4: complete observations
  retain future interaction; the exact interface can be infinite.

No new source clause, support limit, finite-world restriction, projection
meaning, or gate promotion is proposed. The authority and concurrency rules
were read before this attempt. Unintegrated question directories were neither
used as authority nor modified.

## 1. Smallest certificate for this constructive route

Fix a finite residual formula `F_C` at its original rigid imports and original
`xi`. Its leaves are the original predicates on their complete operand tuples.
It has its original finite Boolean/binder tree; this notation does not prenex
it, move a binder across a connective, or expand a recursive future predicate
into finitely many sampled histories. A leaf can itself have an independent
all-history meaning. Deciding such a leaf is part of the certificate below.

A **legal prefix** `a` is an assignment/evidence tuple at one position `n` of
that original tree. It retains all earlier choices and actual scope/incidence.
`Ext_n(a)` is the independently specified domain of the next binder. It must
not be defined by successful checking or by a chosen source execution. Empty
domains use the ordinary existential-false/universal-true convention.

Candidate premise **EPR (effective prefix residual certificate)** has four
parts. These are research hypotheses, not established source rules.

1. **Effective finite presentation.** From admitted finite `C`, construct
   finite layered state sets `Z_n`, successor sets `Next_n(z)` at binder nodes,
   Boolean-node references and terminal predicate labels. Construction and
   enumeration terminate. There is a certified semantic map `q_n(a)` from
   every legal original prefix into its state at that position. The root
   state is determined by the fixed original inputs. Fixed inputs remain
   parameters; no uniform finite set of actual worlds is required.
2. **Forward extension.** For every legal `a` and `t in Ext_n(a)`,
   `q_child(a,t) in Next_n(q_n(a))`. The maps for Boolean children preserve the
   same prefix. Scope, port sorts, rigid coordinates and original sharing
   remain fixed throughout these maps.
3. **Prefix-local backward extension.** For *each* legal `a`, and *each*
   `z' in Next_n(q_n(a))`, a legal `t in Ext_n(a)` exists with
   `q_child(a,t)=z'`. The certificate supplies a terminating symbolic lift
   constructor for existential choices at effectively represented prefixes.
   Its independent interpretation proves legality for all original earlier
   parameters, not only source-reachable prefixes. A lift extends the current
   prefix; it cannot replace any earlier choice with a different representative.
4. **Exact leaf laws.** Every terminal state's computable label is the vector
   of truth values of *every actual active original predicate* on the whole
   original tuple at that leaf, for every prefix mapped to that state. Any
   leaf evidence required as a solver result has a certified effective lift
   at that same tuple. This includes actual effects, Guard/Phi/K,D, profile,
   descriptor and independent admission/future predicates when active.
   A structural witness with the same head is not sufficient. Different
   evidence alternatives stay separate whenever a retained predicate reads
   them; irrelevant alternatives may be represented parametrically rather
   than discarded. Constructing an exact public projection remains PROJECTION.

Mathematical backward existence is enough for truth equivalence at universal
binders. The semantic `q_n` in clause 1 need not be computable. Effective
existential/evidence lifting therefore does not alone supply an effective
original-scope solution recipe. That stronger conclusion additionally requires
candidate premise **ER (effective prefix classification and replay)**:

- Specify a finite-data encoding interface for prefixes and challenges, with
  an independent interpretation at each original tree position. An initial
  prefix code represents the fixed original inputs. Codes retain the whole
  earlier prefix and its original scope/incidence. Symbolic parameters require
  an interpretation contract; they are not unexplained semantic oracles.
- A terminating classifier `qhat_n(e)` returns `q_n(a)` whenever prefix code
  `e` interprets as legal `a`. Its correctness holds for every permitted
  interpretation of symbolic parameters. Computing it cannot assume access
  to an uncomputable predicate or to the semantic `q_n` as an oracle.
- For every represented legal prefix and every actual legal universal
  challenge, the interface effectively provides a challenge code, and a
  terminating replay operation computes the extended prefix code at the
  original child position. It interprets as exactly `(a,t)` and classifies as
  `q_child(a,t)`. Coverage includes every independently legal challenge,
  rather than only a sampled or source-reachable challenge set.
- Boolean descent preserves the same encoded prefix at its child position.
  Each existential/evidence lift accepts the current prefix code and selected
  abstract child and produces the original witness/evidence and its extended
  prefix code. These operations preserve interpretation and remain in the
  classifier's domain at every subsequent node. All encoding, classification,
  replay and lifting operations terminate under the declared interface.

ER is an additional research hypothesis; it does not follow from EPR's four
clauses. Arbitrary semantic worlds are not assumed to be executable objects.
If symbolic codes stand for them, the classifier/replay laws must hold under
every independent interpretation. Without that contract, EPR gives the
conditional truth decision below, with semantic winning choices where the
ordinary set-based choice principle or total semantic lift maps supply them;
it does not give an effective solver emitting the original certificates.

This is smaller than requiring a finite structural graph bound for every
original solution: it only requires a finite decision presentation with legal
prefix lifts. It is still a substantial missing theorem. Clause 4 cannot be
supplied by merely attaching uninterpreted predicate names to finite nodes.

## 2. Conditional theorem and derivation

**Claim class: conditional theorem, unreviewed.** If the actual admitted
residual satisfies EPR, its truth is decidable by finite backward evaluation.
If ER also holds and the existential/evidence lifts are effective on its
encoding interface, a true result yields one effective original-scope
simultaneous witness strategy. Neither EPR nor ER is constructed for Yulang.

At a leaf use the original Boolean expression on the exact predicate vector.
At a Boolean node evaluate its children. At an existential binder take OR
over `Next_n(z)`; at a universal binder take AND over that set. Memoize each
state at its original formula position. The finite layered presentation and
terminating leaf checks make this algorithm terminate. With `V` states and
`E` listed references/edges, it takes `O(V+E)` Boolean work after construction
and label computation; this says nothing about the cost of building EPR or
interpreting its primitives. No practical compiler bound follows.

Prove at every legal prefix `a` that concrete truth of the remaining original
subformula equals abstract truth at `q_n(a)`. Leaf equality is clause 4.
Boolean cases apply the induction hypotheses without changing `a`.

- Existential forward: an original successful `t` maps to a listed child by
  clause 2; induction makes that child successful. Existential reverse: a
  successful listed child has a legal lift *at this a* by clause 3; induction
  makes this lifted extension successful.
- Universal forward: for every listed child, clause 3 supplies a legal
  extension of this same `a`; original universal truth and induction make
  the child true. Universal reverse: each original legal extension maps to
  a listed child by clause 2; abstract universal truth and induction cover it.

These four implications prove preservation and reflection, including empty
domains, without requiring computability of the semantic `q_n`.

For the effective strategy conclusion, start from ER's initial prefix code.
Classify it with `qhat_n`; at an existential node choose a successful listed
child, apply the effective lift and retain its extended prefix code. At a
Boolean node descend using ER's prefix-preserving operation. After each actual
universal challenge, obtain its challenge code, replay the extension and
classify the resulting prefix at the child position. ER's interpretation and
closure laws justify these steps at every subsequent node. Earlier witnesses
are never reselected. Thus an early existential choice cannot depend on a
later challenge, and all terminal predicates hold of one whole original
tuple. The finite abstract strategy together with ER and the certified lifts
is a finite recipe, not an enumeration of all concrete contexts. Branches
share precisely the original earlier prefix. This extraction paragraph is
conditional on ER; the truth-equivalence induction above uses only EPR.

Recursive semantic operators inside a leaf are not discharged by this finite
tree induction. They need the exact independent leaf decision/lifting law
under their original designated fixed-point meaning. Fair worklist closure
over finite comparison states likewise does not establish that law.

## 3. Where construction from the four prerequisites stops

PURE_DEC decides pure structural packages under its finite alphabet and
permission-query conditions. CTX_FINITE, when proved for actual source rules,
bounds comparison states/labels and supplies terminating update closure.
PRIMITIVES supplies independent operand meanings; ALL_WORLD supplies exact
coverage of the independently legal context domain. None of these stated
contracts supplies EPR's effective construction or terminal decision law for
joint non-pure residuals. In particular, exact domain equality is not effective
domain emptiness or an effective finite domain quotient.

The attempted construction is to refine finite structural candidates/context
states by complete active predicate vectors, then use those vectors as residual
states. A finite vector alphabet exists when the active list is finite, but
that fact alone does not make its inhabited cells effectively recognizable.
The pure enumerator cannot decide whether an original joint cell has a witness,
nor show that its regular replacement stays in that cell. Further, terminal
vectors do not determine which child cells extend *each fixed earlier prefix*.
Finding a witness in some other prefix's fiber does not supply clause 3.

There are consequently three exact failure points:

1. **Cell decision/reflection:** an independently proved effective law for the
   active non-pure predicates on original structural/world/witness operands is
   absent. Pointwise decidable checks on proposed finite candidates do not
   decide cell nonemptiness or prove regular-witness completeness.
2. **Coherent prefix extension:** there is no inspected source-derived law
   that each listed abstract child has a legal lift at *every* original prefix
   in its parent fiber, retaining earlier provider identities, incidence and
   admission. Whole-tuple truth labels cannot substitute for that law.
3. **Effective prefix replay:** even a semantic quotient with exact leaves
   and effective existential lifts need not classify actual challenges.
   ER's encoding, classifier and replay laws have not been derived from any
   inspected Yulang source rule.

The reviewed Record-chain extension already refutes the generic inference of
the first law; this attempt does not reproduce that attack. The reviewed atom
orbit theorem already supplies a scoped lift for its equality-only observers;
this attempt does not reprove or extend its selected language meaning. Its
remaining non-name `G` leaves are precisely where this construction stops.
No finite quotient or computable graph-size bound covering all original
Yulang predicates has been produced here. No Yulang undecidability follows.

### 3.1 Accepted reviewer finding and minimized witness

The primary accepted the assigned compiler-referee's **MAJOR** finding:
clause 1 supplies only semantic `q_n(a)`, while effective strategy extraction
must classify/replay each actual universal challenge before selecting later
existential branches. Effective existential lifts do not make `q_n` computable.
The original strategy-extraction claim without ER is withdrawn. Its
truth-equivalence induction remains conditional on the same four EPR clauses.

The reviewer supplied the countermodel

```text
forall n in N. exists b in {0,1}. b = H(n),
```

where `H : N -> {0,1}` is noncomputable and both values are inhabited. This
has the original `forall`-then-`exists` order, one leaf and two witness values.
Use root state `r`, universal successors `{0,1}`, and semantic prefix map
`q_1(n)=H(n)`. At existential state `h`, list terminal successors
`{(h,0),(h,1)}`. Map `(n,b)` to `(H(n),b)` and label terminal `(h,b)` by the
computable equality `h=b`. The existential lift for child `(h,b)` returns `b`
and extends the current concrete prefix with it.

This is a finite effective state/edge presentation with semantic prefix maps.
Forward extension and exact leaf laws hold. Root backward extension holds
because each `h` is inhabited by some `n`; existential backward extension
holds at each fixed `n` because both bits are legal. The existential lift
is effective even though it does not compute `H(n)`. Finite evaluation returns
true: each `h` has the successful child `(h,h)`. Semantic truth likewise holds.
But an effective winning response on natural-number challenge `n` would return
`b(n)=H(n)`, computing `H`, a contradiction. ER fails exactly at the challenge
classifier; adding `H(n)` as an input oracle would change the computation
contract and cannot establish effective extraction from the original inputs.

This witness falsifies the omitted-premise implication; it neither defines a
Yulang primitive nor proves Yulang undecidability. It uses the reviewer's
supplied construction, so the repair producer claims no independent review or
independently discovered counterexample. No executable search, seeds, ranges or
mutation runs were used. A bounded computable stand-in for `H` would not test
the noncomputability premise and is not proposed as another probe.

Repair rationale: retain EPR's four premises and its truth theorem; require ER
explicitly for the effective strategy conclusion and state the encoding
contract in the extraction argument. Residual status: EPR's Yulang construction
and ER's source-derived classifier/replay laws are unproved, JOINT_DEC stays
OPEN-PROOF, and this repaired delta awaits independent review.

## 4. Evidence independence, limits and next action

This is a paper derivation with explicit hypotheses, not an executable
experiment. There is no reference implementation/oracle, random seed, search
range, mutation run or sampled world set. The finite evaluator would share
EPR's transition/label laws with its certificate; implementing and checking
that evaluator would validate internal consistency, not prove source rules.
The independent oracle obligation is the clause-by-clause original semantic
meaning and legal extension domain, established outside the quotient.

Failure conditions are a nonterminating constructor/leaf check, an omitted
original observer, altered rigid/scope incidence, an inhabited abstract child
without a lift at the current prefix, or any primitive whose truth changes
inside a terminal fiber. Any such failure invalidates this sufficient route;
it neither authorizes rejection of ordinary source nor changes its meaning.
Effective extraction additionally fails on an unencodable legal challenge,
noncomputable or incorrect classifier, replay that changes the earlier prefix,
or a lifted prefix outside the encoding interface. Failure of ER alone
withdraws effective extraction without refuting EPR's truth equivalence.

Unverified scope: actual exhaustive primitive inventory, full source-context
closure, recursive future/admission decision, whole Yulang quotient formation,
public projection/principality, production correspondence and cutover. One
bounded constructive attempt was performed; no follow-up toy variant is
proposed. The blocker is the absent effective original primitive/cell,
prefix-extension and challenge-classification/replay laws, rather than a
shortage of sampled cases.

Recommended next action: select one actual active non-name admission/future
primitive at its owning independent definition and prove or refute both its
effective cell decision law and prefix-local lift law. Reuse PURE_DEC only
after that primitive's regularization reflection is established. If the
primitive needs an infinite but effective residual kernel, pursue that kernel
instead of increasing a finite sample bound.

## 5. Original checkpoint snapshot and commit packet (historical)

The original checkpoint packet below records the pre-repair attempt at its
original baseline. Section 6 supplies the current repair handoff.
Pre-write dependency SHA-256 snapshot (all paths unchanged from that baseline):

```text
59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc  notes/theory/successor-proof-obligations.md
37bc762c22d32258355e835a29f598a8b50aa7307a88c01454ef63849c11e133  notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md
dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf  notes/design/2026-10-03-source-context-finite-closure.md
02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43  notes/design/2026-10-03-open-residual-factorization.md
b34c5b3644637bc1340f5636e0b6dc3fcc42c39de5d9cc73bcb48b84293e417e  notes/progress/2026-10-07-successor-global-synthesis.md
214e6a688b84b6ad11adf8446cc0c39cc61f292b8bfd221d2e66749046bc0e89  notes/progress/2026-10-07-successor-effective-projection-round2.md
97367f04b7fa6fd1f21adcc4609129a7d888f9dea6471acf0a06664daadf79bc  notes/progress/2026-10-07-successor-round2-review.md
ac69d1696dbe023d0886d15c0bee0e5e21fca5a189ab89b9b79b3c96bc3587fd  notes/progress/2026-10-05-residual-admission-source-premise-audit.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3  questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
6b8f95cfc2380508d500c447c82b64fd2c26fb32248e6fb3244314cc02023660  notes/design/2026-10-02-source-interface-adequacy-theorem.md
```

- Exact leased/changed path:
  `notes/progress/2026-10-08-joint-dec-constructive-attempt.md`.
- Baseline SHA: `87467e190cff6a8c208d07c1b1f0a1769e81389e`.
- Dependency changes: none at pre-write check; final recheck belongs to the
  accompanying producer report and the primary's integration snapshot.
- Review: unreviewed research checkpoint; producer reread is not independent
  certification. Frozen at submission; no further producer writes for review.
- Checks already run: read-only HEAD/branch/status inspection; targeted source
  reads; SHA-256 dependency capture; `git diff --name-only BASE -- <dependencies>`
  returned no dependency changes before writing. No builds or tests were run.
- Resource use: lightweight sequential/independent read commands and one note
  write; zero search/build/test processes, no experiment output. Peak RAM and
  total wall time were not measured. No explicit numeric assignment budget was
  supplied; work stopped after the one assigned bounded attempt.
- Proposed commit message: `research: derive conditional JOINT-DEC residual prefix certificate`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  this attempt under JOINT_DEC and record the cell-decision/prefix-lift blocker;
  do not change canonical status, prerequisites, language authority or cutover
  claims. No task/index/theory/question files were edited.

## 6. Repair snapshot and commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-08-joint-dec-constructive-attempt.md`.
- Repair baseline SHA: `20375f34eeae91c7f29473f3a787514c37c74abb`.
  Original artifact: `6967ac589` (primary-supplied identifier); original
  derivation baseline and dependency hashes remain in section 5.
- Dependency changes: none. All ten SHA-256 entries in section 5 matched at
  repair start and after the substantive edit, including the approved inlet
  answer and the governing JOINT-DEC ledger. Read-only filesystem inspection
  of `.git/HEAD` and its named branch ref matched the repair baseline.
  No Git command, index/ref mutation or question-bundle edit was performed.
- Claim/review status: conditional research repair; accepted original MAJOR
  recorded in section 3.1; repaired delta pending independent review. Producer
  verification does not certify the repair. JOINT_DEC remains OPEN-PROOF;
  EPR and ER remain unconstructed for Yulang.
- Checks already run: targeted governing-rule/source reads; SHA-256 dependency
  rechecks; Python `difflib.unified_diff` inspection against the pre-repair
  in-memory lease snapshot; exact comparison confirming all four EPR clauses
  unchanged; local Markdown path/anchor resolution; trailing-whitespace and
  final-newline checks. No builds, tests or executable experiments were run.
  Committed-tree/index equality is left to the primary's integration check
  because this repair packet forbids Git operations.
- Resource use: lightweight file reads, note patches and sequential Python
  static-check processes; zero search/build/test processes and no generated
  outputs. CPU time, peak RAM and total wall time were not measured. No numeric
  repair budget was supplied; scope stopped after this one premise repair.
- Recommended next action: independently delta-review ER's encoding/coverage
  and the conditional extraction argument against the accepted MAJOR.
- Proposed commit message:
  `research: require effective prefix replay for JOINT-DEC strategy extraction`.
- Shared-record deltas intentionally left for primary/curator: record the
  accepted effective-extraction gap and conditional ER repair under JOINT_DEC;
  retain OPEN-PROOF, original quantifiers, all prior predicates and prerequisites.
  No task/index/authority/theory/question files were edited.

Frozen at submission for independent delta review; no further producer writes.
