# Literal Call argument origin: a conservative record extension

Date: 2026-10-08
Baseline: `3a88196610fe6b8fb93df79730cae01ef85422bb`
Branch: `research/simple-sub-intrusion`
Status: frozen unreviewed research; conditional representation derivation
Exclusive lease: this file only
Method: dependent disjoint extension, constructor inversion and commuting actions
Semantic adoption, production implementation and aggregate closure: none

## 1. Objective and result

Can the argument `u_x` in the old Gen-Call-0 index be extended to
`ArgOrigin = NameOrigin | LiteralOrigin`, preserving old Name records and the
selected O0/O1 equations? **Yes as an explicitly defined record extension.**
Its old summand has an injective inclusion and an exact inverse on that
summand. Its literal summand retains the genuine literal child, not a Name
proof. Selected demand/root/slot/owner equations can be transported on the old
summand without changing their values, dependent indices or witnesses.

**This does not make the literal summand an actual original emitted record.**
The supplied Gen-Call-0 introduction really has a resolved Name/Name premise.
The selected O0/O1 definitions consume actual emitted records; they do not
introduce literal membership. A rule accepting the tagged argument at the
original emission owner, together with installation and inventory preservation,
remains unsupplied. Neither the representation nor schema equality proves it.

No inspected authority requires every ordinary source argument to be a Name.
The obstruction is applicability of the supplied introduction and the actual
record family it produces, rather than an approved language restriction. An
extension of that family requires primary adjudication and focused review; this
note proposes one and adopts none. No additional semantic alternative is chosen.

## 2. Baseline, exact premises and authority boundary

The following govern this bounded derivation:

- [Original Call formation](../design/2026-10-07-original-call-formation-definition.md)
  §§2–4: actual emitted dependent record, `demand`, complete invocation root
  and OC-CallEff's eight projections. Its §1 explicitly does not assert
  all-source record generation and preserves old derivations for other Calls.
- [Original ownership](../design/2026-10-07-original-call-owner-definition.md)
  §§2–5: actual callee Name/capture route, shared registration, actual record,
  O0 and independent SeedExposure; lexical/checking facets remain distinct.
- [Source generator](../progress/2026-10-06-source-call-generation-construction.md)
  §§4.2–4.4, with §3's child definitions: resolved singleton Name/Name Call,
  ordinary Value interfaces, complete invocation address and whole action.
- [Source-introduction contract](../design/2026-10-07-original-call-source-introduction-contract.md)
  §§2–4: owning source responsibility and separate O0/O1/C0/C1/J0 ports.
  Its unadopted §3.1 kernel is not identified with selected paired ownership.
- [Literal constructor proposal](2026-10-08-flat-apply-literal-original-constructor.md)
  §§2–6: candidate `P_c^cand`, separate H-E enrichment, H-R registration,
  literal incidence, preserved extra atoms and separately required flat seed.
  Its repaired scope is recorded as delta-reviewed in `tasks/current.md`
  immediate work order; the producer note retains its older pending-review
  header. This lane changes neither record nor certifies the earlier proposal.
- [Function views](../design/2026-10-05-inferred-function-call-views.md)
  §§2–5 and integrated function-view q1/a2 decisions 1–6: shared source contract,
  one scoped xi, independent admission, provisional formal view distinct from
  actual provider role, and annotation-dependent protection.
- Integrated ReadInvoke q1/a1 decisions 1–4 and its receipt: retention of
  insertion/lookup evidence at the construction owner in the finite identity
  Name/Name seam; neither missing rules nor literal scope are supplied.
- [Pure-read result constructor](../design/2026-10-08-pure-read-call-result-constructor.md)
  §§1,4–5: immutable Name callee/identity result, independent carrier/challenge
  typing, separate M_E and W/Z obligations. No such typing is inferred here.
- `rules/design-authority.md` authority order and approval gate;
  `rules/research-lab.md` evidence/stopping rules; `rules/git-concurrency.md`
  disjoint lease and frozen dependency requirements.

Hypotheses are explicit:

**H-old:** existing derivation-indexed records of the displayed Gen-Call-0
introduction, with their genuine Name argument child and all original dependent
fields. Its construction/inversion and legal whole action are retained.
This is the supplied Name/Name branch, not an exhaustive original inventory.

**H-cand:** a supplied candidate `P_c^cand` in the repaired proposal's exact
H-B/H-L/H-C/H-R scope, including its actual literal primitive, registrations,
whole argument origins and entire candidate atom inventory. It is a parameter
to this representation derivation; no new proof of its source premises is made.

**H-map:** one legal sorted map acts on every original index and child
derivation together. The old branch uses its existing law; the candidate
branch additionally needs H-R's registration law and candidate emitter
congruence. Semantic assignment actions need the independent kernel law.

Claim classes: the cited selected O0/O1 results remain established in their own
scopes. Section 3 is a proposed representation plus conditional algebraic
theorem under H-old/H-cand. Section 4 gives transport and consumer calculations
under H-map. Section 5 is bounded rule-inventory characterization and a reduced
syntactic witness. Original authenticity/adoption remain open premises.

## 3. Exact dependent family, injection and projections

Remove only the argument coordinate from the old index and call the remainder j:

```text
j = (B,X,xi,Delta_e;
     d_f,A_f,R_f,u_f,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi=(nu,K,D), U_e=F_c, beta=(d_f,R_f)
Idx_old(e)=insertArgument(j,u_x)
```

This is a dependent telescope. Its source graph X and Call c still fix the
actual argument child; removal of a displayed coordinate does not detach that
incidence. J is the sum of well-scoped such frames, permitting either actual
Name or actual literal syntax. A Name frame and a literal frame need not be
the same j. Every old well-scoped frame injects into J unchanged.

For each j, define:

```text
Old(j,u_x) = records/derivations of the supplied old Gen-Call-0 introduction
            at insertArgument(j,u_x)
N_j = genuine typed argument-Name child derivations at c's argument in X
L_j = genuine literal primitive child derivations at c's argument in X

ArgOrigin(j) = NameOrigin(N_j) + LiteralOrigin(L_j)
argExpr(NameOrigin(n)) = n's actual Name expression occurrence u_x
argExpr(LiteralOrigin(l)) = l's actual literal expression occurrence a
```

A Name child retains its actual `u_x -> d_x`, Value interface, source scope
and Name/Return image; it is not just a Use ID. A literal child retains its
primitive, spelling/value/interface and scope/xi action, with no declaration
or Name resolution. `oldChild(e) : N_j` is the genuine old inversion projection.
`litChild(p) : L_j` is H-cand's genuine primitive projection. Neither projection
manufactures original emitted membership.

Let `CandLit(j,l)` be exactly the fiber of supplied literal packages P_c^cand
whose common frame is j and whose literal projection is l. It preserves the
entire package, including all extra candidate coordinates and atoms. Empty
fibers remain empty. Define a new indexed record family by two constructors:

```text
e : Old(j,u_x)
----------------------------------------------- Keep-Name
Keep(e) : Rep(j,NameOrigin(oldChild(e)))

p : CandLit(j,l)
----------------------------------------------- Add-Literal
Add(p) : Rep(j,LiteralOrigin(l))
```

`Rep` is a fresh representation family, not an equation identifying it with
the original emitted judgment. There is no extra equality-proof witness,
quotient, canonicalization or arbitrary matching of independently supplied
fields. Each constructor retains its entire operand. It need not be inhabited
for every origin or for every source graph.

On total dependent sums, define `i_old(e)=Keep(e)` and the partial retraction:

```text
r_old(Keep(e)) = e
r_old(Add(p))  = undefined
r_old(i_old(e)) = e
i_old(r_old(z)) = z  [z has the Keep constructor]
```

Thus i_old is injective, including derivation identity and old dependent index.
There is no claim that multiple old proofs of the same displayed indices become
equal. Name inversion of Keep recovers the old record and its *original*
inversion; literal inversion of Add recovers p and its primitive/registrations/
candidate origins. Literal inversion yields no `Resolve(a,d_x)` and no H-E.

Every common field projects to its retained value. In particular:

```text
demand(Keep(e))=demand_old(e)       demand(Add(p))=p.demand
origin(Keep(e))=NameOrigin(oldChild(e))
origin(Add(p))=LiteralOrigin(litChild(p))
oldArgument(r_old(Keep(e)))=e.u_x
```

The common projection forgets only metadata, retaining the complete source
expression in X/c and every old common field. It is not a projection from the
literal branch into the old emitted family. Erasing a candidate literal tag
leaves the candidate literal command/inventory, as in the prior proposal;
it does not change the literal into Name syntax or create original emission.

**Proof.** Pattern matching gives each displayed equation. Disjointness of
constructors and retention of e give injection and inverse on its image.
No proof irrelevance or semantic solution existence is used. These are finite
dependent-constructor calculations, conditional on the supplied input families.

## 4. Whole action and selected equation preservation

For the one legal whole map theta of H-map:

```text
theta(NameOrigin(n))=NameOrigin(theta(n))
theta(LiteralOrigin(l))=LiteralOrigin(theta(l))
theta(Keep(e))=Keep(theta(e))
theta(Add(p))=Add(theta(p))
theta(i_old(e))=i_old(theta(e))
r_old(theta(Keep(e)))=theta(r_old(Keep(e)))
argExpr(theta(alpha))=theta(argExpr(alpha))
```

The map preserves constructor tags and transports X/c, binder tree, Delta,
original xi, child syntax, callee route, upper occurrence, demand, ElimOrigin,
registrations and all atoms together. Literal values retain the independent
primitive interpretation; substitution cannot turn a literal child into a
Name. Fixed captured imports remain fixed as required. Identity/composition
laws follow by two-case induction from the component laws. They are not proved
for arbitrary maps that violate H-map or for unsupplied original H-E actions.

Selected root construction reads the same projected demand:

```text
rho_z=demand(z)
q_z=Inv(Id(descriptor(rho_z)),descriptor(rho_z))
q_(Keep(e))=q_e
```

Consequently every OSig-Demand defining equation on the old branch is unchanged.
For OC-CallEff, its source origin is the *entire* record. One cannot erase
ArgOrigin there while claiming unchanged provenance. Define a representation
image of that constructor with origin i_old(e), and its old-branch inverse:

```text
i_ce(OC-CallEff(e))=OC-CallEff_rep(Keep(e))
r_ce(OC-CallEff_rep(Keep(e)))=OC-CallEff(e)
```

The eight adopted eliminators commute with these maps: q, p0, u, c, beta,
Delta and ElimOrigin have their original projections; source origin changes
by i_old and is recovered by r_old. This preserves equations under an explicit
record isomorphism on the Name image. It does not claim literal Add(p) can be
passed to the existing OC-CallEff rule. `OC-CallEff_rep` is notation for the
proposed transported constructor, with no original-judgment adoption.

O1's `Route(e)` is the **callee** Name/capture route at u_f. Retaining a literal
argument changes none of that route's equations. On Keep(e), keep reg, route,
O0 and the actual seed; transport the canonical UpperInvokeAttachment through
the same injection, with its inverse on the old image. Both facets keep
`indexedOccurrence(lex)=e.u_f`, `indexedOccurrence(chk)=e.u`, the same owner
payload and shared slot. `SharedInvoke(beta)`'s key remains beta; a proposed
representation transport creates no equation between unrelated local roots.

For a literal branch, forming analogous static certificates still requires
an actual original emission interpretation and, for owner introduction, an
independent actual SeedExposure at that literal Call's upper occurrence. No
seed follows from the tag, Int, annotation absence alone or a provider lower
bound. No old owner, slot or independently licensed alternative is deleted.

This proves representation conservation and commutation on the old image,
not universal conservativity of every predicate over an enlarged original
domain. An arbitrary old predicate quantified over all emitted records need
not be invariant when a new member is adopted. C0/C1/J0, admission, profile,
ReadInvoke source-base typing and whole old-domain interpretation remain separate.

## 5. Actual Name premise and the smallest unsupplied rule

Source-generator §4.2's premises are:

```text
resolved singleton Call(c,u_f,u_x), u_f -> d_f
I(u_f)=Value(A_f), I(u_x)=Value(A_x), original scope sigma
```

Its §3 binds `u_x -> d_x` and constructs J_x from Name/Return. This is an
actual argument-Name requirement for this displayed introduction. It is not
an eliminator of selected O0/O1 and not an exhaustive grammar of all approved
ordinary Calls. O0's §2 display alone gives no generalized argument sort or
literal introducer. O1's callee Route cannot supply the missing argument child.

The reduced separating witness is the scoped elimination in
`my apply f = f 1`: `Apply(Name(u_f),Literal(a,"1"))`. Trying to inhabit the old
fiber leaves `u_x -> d_x` and its Name/Return child unsupplied. Literal has no
such projection. A total retraction Rep -> Old preserving the argument source
expression would require `Name(...) = Literal(...)` on Add(p), contradicting
the disjoint source constructors. This is a structural witness, not a runtime
semantic counterexample or a claim of globally shortest source text.

The smallest unsupplied premise after the representation calculation is:

```text
At the original source owner, an actual introduction at
  Apply(Name(u_f),Literal(a,"1"))
produces an emitted record indexed by LiteralOrigin(actual primitive),
retains original registration/operand/reify/checking/result/suffix origins
and every original atom, and installs that introduction in the original
emitted inventory with a lawful whole-index action.
```

For consumers to accept it directly, that introduction must be an explicitly
reviewed completion of their emitted-record family, preserving the Keep image
and selected equations as above. Alternatively a separately fixed family
needs a typed interpretation bridge. Neither route is adopted here. The
representation construction reduces the old-Name-preservation obligation;
it does not establish H-R/H-E, original insertion, semantic typing or the
literal family's authenticity. Another checker assuming this premise would
leave the same gate open; this lane stops rather than launching that probe.

## 6. Independence, coverage, mutations and frozen boundary

No executable oracle, search, seeds/ranges, mutation execution, test/build or
performance sample was used. The method is derivation/inversion. The cited
records share descriptor operations, source indices and selected constructor
equations; their agreement supplies no independent validation of source rules.
The literal primitive and old source derivation are explicit inputs. No global
absence search or original-family exhaustiveness theorem was attempted.

Three conceptual mutations discriminate the proof's requirements: a total
old retraction fails on the literal witness (§5); keeping only an argument ID
loses oldChild/inverse provenance (§3); independent per-port actions fail the
single-j commuting equations (§4). These are analytic failures, not reported
executable mutation results. Deleting a result atom or deriving SeedExposure
from the literal tag also exceeds the input scope and fails authenticity.

Coverage: old records of the supplied Name/Name introducer, one literal
candidate branch, selected constructor equation transport and legal whole maps.
Other original introducers stay untouched; no exhaustive union is asserted.
Computed arguments/callees, annotations, late or recursive seeds, State/method
sources, arbitrary foreign interpretations, complete CallInitial/I0/action
laws, C0/C1/J0, principality/export, Option 2 and implementation remain unverified.

Resources: one producer and one leased Markdown artifact; zero children,
heavy processes, builds, tests, formatters or Git mutations. Reads and dependency
hash checks are finite lightweight processes. No numeric CPU, RAM or wall limit
was supplied; CPU/peak RAM/reasoning wall time are uninstrumented. Initial
combined captures truncated; all relied-on sections were reread in narrow
slices. No scratch output or unleased file was written.

Stop/failure conditions: dependency changes; Keep loses any old derivation;
literal is coerced to Name; Rep is asserted equal to actual emission without
an owner rule; original inventory is truncated; xi/scopes/provider are split;
whole-map component laws are assumed as proved source action; O0/O1 is used to
generate its own record/seed premise; or a representation result is promoted
to adoption/semantic typing. The artifact is frozen at submission; no writes
continue during review.

Recommended next action: primary should obtain focused independent review of
the tagged dependent family and old-image equations, then supply/adjudicate
the actual original literal emission completion at that source owner. Keep
seed, insertion, CallInitial and production gates separate.

## 7. Dependency freeze and commit packet

The direct snapshot below was checked byte-for-byte against the pinned commit;
all 17 match. The two answer drafts occur exactly inside their approved answers.
No direct dependency hash changed. The primary must recheck at integration.

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6 rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5 rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0 rules/question-board.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110 notes/design/2026-10-07-original-call-owner-definition.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
1dcdfc40990a93c52ced1ae3ee11fd393014634864da8c480f8f943a2065ebc0 notes/design/2026-10-07-original-call-source-introduction-contract.md
c825c668dd8f523a8274aa37a3b11665c177e07b1aa1f1d9559c3f6807a9baa5 notes/theory/2026-10-08-flat-apply-literal-original-constructor.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488 notes/design/2026-10-08-pure-read-call-result-constructor.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536 questions/2026-10-05-function-call-view-formation/approved-answer.md
585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c questions/2026-10-05-function-call-view-formation/answer-draft.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0 questions/2026-10-05-function-call-view-formation/receipt.md
1920f732c255136e4d12f8dba13b2320480d250bdd4b2f778a33cabd3f405f13 questions/2026-10-08-readinvoke-source-presentation/approved-answer.md
9b47291c227bc8c7f3f3bf7209572fb5ec31391fd3b92b3bc3ccdae13d3d2d2d questions/2026-10-08-readinvoke-source-presentation/answer-draft.md
fb87e7eed0b8ffcb069cd18f9972758df919825c64baef1f4f2c840a66783ab0 questions/2026-10-08-readinvoke-source-presentation/receipt.md
```

- Exact leased changed path: `notes/theory/2026-10-08-literal-call-argument-origin-extension.md` only.
- Baseline SHA: `3a88196610fe6b8fb93df79730cae01ef85422bb`.
- Changed dependency hashes: none at freeze.
- Review status: unreviewed conditional representation derivation; no independent
  certification, adopted family extension or aggregate closure.
- Checks already run: scoped source/authority reads, dependency byte/hash checks,
  exact approved-draft embedding, leased output/link/whitespace checks. No model,
  compiler test, build, formatter or Git mutation.
- Proposed checkpoint message: `research: derive conservative literal argument origin extension`.
- Shared-record deltas left to primary/curator: record the exact old Name
  injection/inverse and tag-preserving action as proposed representation;
  retain original literal introduction/installation/inventory and H-R/H-E as
  authenticity cuts. No task/index/authority/question files or gate statuses
  are changed. Residual approval question is the bounded emitted-family
  completion/consumer scope, not a reopened Function or ReadInvoke meaning.

Writes stop before submission for frozen review.
