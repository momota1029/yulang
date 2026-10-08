# JOINT-DEC: a conditional residual-game decision construction

Date: 2026-10-08
Status: Unreviewed conditional derivation; one bounded constructive attempt
Implementation authority: none
Gate status: unchanged; JOINT_DEC remains OPEN-PROOF
Baseline: `87467e190cff6a8c208d07c1b1f0a1769e81389e`
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

- `successor-proof-obligations.md`, PURE-DEC, PRIMITIVES, ALL-WORLD,
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

For all-universal binder choices, mathematical backward existence is enough
for truth equivalence. Effective existential/evidence lifting is additionally
needed to return an actual original-scope solution recipe. We do not assume
arbitrary semantic worlds are executable objects: a symbolic lift must have
an independent interpretation over those worlds. If no such witness encoding
is supplied, the result below gives conditional decision only, not an effective
solver that emits the required original certificates.

This is smaller than requiring a finite structural graph bound for every
original solution: it only requires a finite decision presentation with legal
prefix lifts. It is still a substantial missing theorem. Clause 4 cannot be
supplied by merely attaching uninterpreted predicate names to finite nodes.

## 2. Conditional theorem and derivation

**Claim class: conditional theorem, unreviewed.** If the actual admitted
residual satisfies EPR, its truth is decidable by finite backward evaluation.
When its existential/evidence lift constructors are effective, a true result
also yields one original-scope simultaneous witness strategy.

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
domains. To emit a strategy, choose a successful existential child at its
original position, lift it at the current prefix, and continue recursively.
After an actual universal challenge, map that challenge and continue using
the resulting child. Earlier witnesses are never reselected. Thus an early
existential choice cannot depend on a later challenge, and all terminal
predicates hold of one whole original tuple. The finite abstract strategy
plus certified lift constructors is a finite recipe, not an enumeration of
all concrete contexts. Branches share precisely the original earlier prefix.

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

There are consequently two exact failure points:

1. **Cell decision/reflection:** an independently proved effective law for the
   active non-pure predicates on original structural/world/witness operands is
   absent. Pointwise decidable checks on proposed finite candidates do not
   decide cell nonemptiness or prove regular-witness completeness.
2. **Coherent prefix extension:** there is no inspected source-derived law
   that each listed abstract child has a legal lift at *every* original prefix
   in its parent fiber, retaining earlier provider identities, incidence and
   admission. Whole-tuple truth labels cannot substitute for that law.

The reviewed Record-chain extension already refutes the generic inference of
the first law; this attempt does not reproduce that attack. The reviewed atom
orbit theorem already supplies a scoped lift for its equality-only observers;
this attempt does not reprove or extend its selected language meaning. Its
remaining non-name `G` leaves are precisely where this construction stops.
No finite quotient or computable graph-size bound covering all original
Yulang predicates has been produced here. No Yulang undecidability follows.

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

Unverified scope: actual exhaustive primitive inventory, full source-context
closure, recursive future/admission decision, whole Yulang quotient formation,
public projection/principality, production correspondence and cutover. One
bounded constructive attempt was performed; no follow-up toy variant is
proposed. The blocker is the absent effective original primitive/cell and
prefix-extension law, rather than a shortage of sampled cases.

Recommended next action: select one actual active non-name admission/future
primitive at its owning independent definition and prove or refute both its
effective cell decision law and prefix-local lift law. Reuse PURE_DEC only
after that primitive's regularization reflection is established. If the
primitive needs an infinite but effective residual kernel, pursue that kernel
instead of increasing a finite sample bound.

## 5. Frozen snapshot and commit packet

Pre-write dependency SHA-256 snapshot (all paths unchanged from baseline):

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
