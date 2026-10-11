# Value-reference copy law: finite non-entailment and the remaining semantic bridge

Date: 2026-10-12
Status: unreviewed research-only constructive derivation; original parent gates OPEN
Baseline: `c9c2581308586dbc87542629d7389de2d2c77156`, `research/simple-sub-intrusion`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; proof leaf, no further delegation

## 1. Frozen claims and exact authority

The original parent claim remains: for every supported source program, every
lawful finite inference/use history H at its original lexical, type and event
scopes, and every actual retained distinct Value extrusion pair (c,p),

```text
Parent_H(c,p,polarity,target_level) and
p ->* c and c ->* p in the actual Value-reference graph before this equality
```

must justify the selected equality while preserving joint source typing,
complete Call, effect hygiene, attachment/provider/witness/residual lineage,
and required principality. Its constructor/consumer correspondence is also
required. SCC membership is the qualification; it is not the preservation
proof. Lexical levels and polarity do not filter Value edges.

The local proposed theorem is universal transport of original source-owner
incidences to every extrusion or use-freshening copy of that owner's Value row.
The two exact candidates supplied by the primary are:

```text
Inheritance: a copied owner gets the parent's resolved-Name incidences,
             each targeting the original resolved binder's Value row.
No automatic inheritance: copying descriptions/bounds creates no incidence;
             explicit source-owner construction can still assign incidences.
```

Neither candidate changes the native type-copy domain or selects a different
target for an original Name. In particular, this packet does not compare
anchored targets with mapped targets: both candidate rules preserve the
original target where they emit an incidence.

Exact governing sections of
[the intrusion decision](../design/2026-10-10-parent-copy-scc-intrusion.md)
are **Selected operation and compiler responsibility**, **Value-reference SCC
clarification**, **Apply-result source-fragment ownership**, **Nested Apply
membership**, **Definition-root Value ownership**, and **Retained boundary**.
They select original Apply/root owners, preserve resolved binder targets,
permit parent-to-child and nephew-to-uncle references, and expressly leave
copy/use transport and qualified-equality preservation unestablished.
[Source Generalize](../design/2026-10-08-source-generalize-definition.md)
§§2–5 and its selected [construction](2026-10-08-source-generalize-definition-and-proof.md)
§§3–5 fix joint clauses, binder placement, actual providers and independent
description frames. [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and **Evaluation** require native Simple-sub and the full preservation
obligations. The pending [copy-content question](../../questions/2026-10-12-value-reference-copy-content-owner/question.md)
is an input describing alternatives, not approval of either.

Claim classes here: a constructive finite original-rule derivation; a proved
non-entailment result for the settled owner/copy interface; a bounded
no-incoming-copy characterization of that interface; and a precise obstruction
to claiming a full source-qualified SCC discriminator or the parent theorem.
No global consistency, soundness, principality or implementation theorem for
either candidate policy is asserted.

## 2. The records that must remain distinct

For a resolved Name occurrence sigma, keep its source binder beta, source
scope, and actual original binder row b(beta). Let

```text
I(v,sigma,beta,b(beta))
```

mean that Value owner v carries that occurrence's incidence. Adjacency is the
projection v -> b(beta). This record is separate from:

- native lower/upper constraints and their replay obligations;
- extrusion Parent(c,p,sign,level), with polar map m(p,sign);
- source rule-program references, typed provenance and active residual clauses;
- runtime/provider identity and actual source event operands;
- the description allocation d_i(q) in a fresh-use frame i.

The separation is substantive. Apply `konst 1` owns a callee incidence even
when its runtime result is literal 0. Conversely, a retained symbolic source
clause with operands d_i(q) does not identify an SCC owner with any one of
those operands. Generalize construction §5.2 retains every source clause in
one whole frame, aliases reuse that frame, and Shared/OneShot fields stay in
the base tree. Neither candidate below deletes or marginalizes those clauses.

An original binder can therefore retain b(beta) as its incidence target while
its eligible type description has d_i(q) in frame i. Establishing a relationship
between a new native copy c and the *source-owner role* of p is precisely the
missing bridge; preserving a common raw provider does not establish it.

## 3. A source-generated copy with nonempty original incidence

The pinned original `Typer.scala:48–83,115–157,166–207` derives the following
without supplied bounds or an eager-solving assumption:

```text
lambda f. let y = f 0 in y
```

This is the exact constructor term
`Lam(f,Let(false,y,App(Var(f),Lit(0)),Var(y)))` of `syntax.scala:7–14`.
At enclosing level 0, Lambda allocates monomorphic formal F at level 0.
The local initializer is at level 1. Its App allocates result Y at level 1
and generates `F <: Function(int,Y)`.

The demand's level is 1, so the wrong-level left-variable branch negatively
extrudes the Function to level 0. Its ground argument is unchanged; its
negative result occurrence creates C=m(Y,-), level 0, inserts C into Y's
lower bounds, and copies Y's initially empty upper bounds to C. The retry
stores `Function(int,C)` in F's upper bounds. F has no lower bounds, so no
opposite-bound replay is activated by that insertion. This is the actual
activation analysis, not a conclusion inferred from storage alone.

Local y is generalized at boundary 0 as `PolymorphicType(0,Y)`. Its final
Name use opens one map and produces Y_i at level 0. The lower C is nongeneric
at this boundary and remains shared. At the returned Lambda cut:

| Row | Level | Lower | Upper | Origin |
| --- | --- | --- | --- | --- |
| F | 0 | empty | Function(int,C) | original formal f |
| Y | 1 | C | empty | original App result / local scheme body |
| C | 0 | empty | empty | negative extrusion of Y |
| Y_i | 0 | C | empty | generic fresh use of Y in frame i |

The resulting original type is `Function(F,Y_i)`. C is an extrusion copy with
a recorded creation origin; Y_i is a use copy, not a second extrusion parent.
The original reference does not retain Yulang Parent records: the origin is
read directly from its allocation. All native constraints admit, for example,
the single simultaneous assignment F=Function(int,int), C=Y=Y_i=int.

The approved Apply law supplies `I(Y,sigma_f,beta_f,F)`. In Yulang's
unannotated local installation the initializer endpoint is the published root
(`candidate_source.rs:332–333`; `candidate_scheme.rs:1316–1335`); this permits
the local y root to be this Apply row, without identifying arbitrary definition
roots with expression rows. If an outer definition root U owns the final
Name y, its additional incidence is U -> Y in both structures below.

The native Yulang spelling used only as a static constructor analogue is
`my use f = { my y = f(0); y }`. Parameter, CallTail/Apply, sequential local
binding and local Name routes have owning constructors. No parser, HIR or
candidate execution was run on this spelling, and no complete Yulang Call
adequacy theorem is assumed. The finite original-rule derivation above is
unconditional for its explicit original grammar; the Yulang operational bridge
retains recovery-free formation and successful checked-allocation premises.

## 4. Two actual finite models of the settled incidence interface

Take the exact native rows, bounds, scopes, binder targets, polar map, scheme,
provider anchors, source clauses and frame i from §3 as one shared structure.
Let the original Value vertices be {F,Y}, with optional separate outer source
root U; the copy vertices are {C,Y_i}. Original occurrence sigma_f resolves
only to beta_f, whose target is F. Optional sigma_y resolves only to beta_y,
whose target is Y. There are no unmentioned incidences in this finite
interface. The common source-owner construction log assigns sigma_f to Y
(and sigma_y to U, if included); it contains no explicit source-owner
assignment to C or Y_i. The common native log instead creates C by extrusion
and Y_i by freshening. Thus an added copy incidence is automatic transport,
not an extra source constructor hidden in one model. These are complete
incidence sets, not unspecified edge sketches:

```text
M_inherit.I = {(Y,sigma_f,beta_f,F),
               (C,sigma_f,beta_f,F),
               (Y_i,sigma_f,beta_f,F)}
M_empty.I   = {(Y,sigma_f,beta_f,F)}
```

Add `(U,sigma_y,beta_y,Y)` to both if U is included. Every other record is
identical, including the full joint source program, native bounds, actual
provider and fixed witnesses. Copied incidence records retain their copy/use
event coordinate; they do not create another source occurrence, rerun the
initializer, select a new binder, or independently choose a witness.

Both satisfy every settled incidence clause applicable to this constructor
fragment: the original Apply/result and definition-root clauses have exactly
their required occurrences and targets; no nested Apply or shadowing is lost;
native extrusion/freshening has exactly its required maps and bounds. Every
source-Generalize clause remains active with its original allocation. Neither
structure contains a retained parent/copy SCC, so the selected equality
operation has no nontrivial qualifying premise at this cut. Thus its prescribed
action is also respected. The two exact policies determine the added records
as displayed, without auxiliary assumptions about bounds or providers.

**Finite non-entailment theorem.** These settled owner clauses together with
the native copy rules do not entail universal copy-incidence inheritance and
do not entail universal absence of automatic copy incidences.

**Proof.** M_empty is a model of those premises in which the actual copy C of
the source-owned Y lacks Y's incidence; it falsifies universal inheritance.
M_inherit is a model of the same premises in which C carries it, so it
falsifies universal absence. All premises involving native type or scoped
source-rule fields have identical interpretations in the two structures.
The incidence clauses constrain the original owner Y and original binder F,
which agree. The only added graph-consuming equality premise is false for
the retained pair in both, as checked below. This supplies explicit finite
models of the interface theory, rather than a checker assuming transitions.

The first distinguishing observation is C's adjacency: {F} versus empty,
immediately after extrusion; at fresh use, Y_i also differs. This is an
observation of the prospective SCC input. **No difference in inferred types,
source execution or qualifying SCC is demonstrated.** These finite models
are not two complete, globally sound/principal Yulang implementations. The
stronger assertion that both policies satisfy every future semantic obligation
would assume the original parent theorem and is left OPEN.

## 5. Why this discriminator cannot yet change pair qualification

**Bounded target-range lemma.** Fix a finite constructor interface whose
resolved binder targets are in an original-row set B, disjoint from fresh
copy rows N. Let its only edges be the approved Apply/definition Name
incidences and the anchored copied incidences, if any. Then every edge targets
B; consequently no path ending in a copy c in N has positive length.
In particular no distinct original parent p can reach c, and no such pair
qualifies in either policy.

Proof: each original incidence targets b(beta) in B; inherited incidences
retain exactly that target; noninheritance adds no edge. A path to c would
have a last edge targeting c, contradicting its target's membership in B.
In §4, B={F,Y} (and U if present), N={C,Y_i}; all SCCs are singletons.

This lemma covers only the displayed incidence-generating interface with its
fixed binder-target range. It does **not** cover the parent theorem's full
source/Value-construction domain. In particular it says nothing about other
Value-content references, later binder installation that exposes a copy,
incoming-reference redirection, prior canonicalization, Lambda/Block/wrapper
boundaries, or any independently licensed parent-to-child/nephew-to-uncle
reference. Those cross-tree references remain explicitly permitted by the
user. Their actual producers are not defined by the two selected Name rules.

The smallest further premise for an SCC discriminator is a supported,
independently licensed construction of an incoming path p ->* c, together
with a return path determined differently by the policies. Merely copying an
original root SCC supplies neither incoming path. Adding p -> c to §4 would
not automatically suffice either: C -> F is a return to F, not to Y. A
conditional graph witness such as p -> p and p -> c, then inherited c -> p,
does discriminate qualification, but its p -> c constructor remains absent.
It is not a source counterexample and is not another proof attempt here.

## 6. Required examples and original scopes

For `id x = x`, the original reference gives `Function(X,X)` with one generic
X and one shared freshening map; both ports become X_i. There is no extrusion
pair. The selected definition root I owns the body Name to original formal X.
If an actual Yulang use copies root I, inheritance gives I_i -> X, while
noninheritance adds no incidence to I_i. The copied type ports still use X_i
in *both* policies. Generic X_i and original binder target X are distinct
coordinates; a proof that the root I is in this particular native copy domain
is required before treating that root-copy instance as operational evidence.

For `konst x = 0`, root K has no Name in its literal body, so copying its
source-owned incidence set cannot distinguish the policies. X remains generic
and a coherent use freshens it; the result is int. For the Apply `konst 1`,
result R owns R -> K irrespective of literal provider 0. A native use copy
of R distinguishes the policies even when K is outside the copied type graph.
For an explicit extrusion-bearing original term:

```text
let konst = lambda x. 0 in
lambda g. let y = g (konst 1) in y
```

K's type scheme is `Function(X,int)` at boundary 0. In y's level-1
initializer its use freshens X once, and the inner App creates level-1 R with
lower int. The outer formal G is level 0; its App result T is level 1. The
comparison `G <: Function(R,T)` therefore negatively extrudes, creating
positive copy C_R=m(R,+) with lower int, and negative copy D_T=m(T,-) with
empty upper bounds. The source incidences are R -> K and T -> G,K (the latter
uses the approved nested Apply membership). Inheritance adds C_R -> K and
D_T -> G,K; noninheritance adds neither. Parent origins are (C_R,R,+,0) and
(D_T,T,-,0). None of these Name incidences supplies a path into C_R or D_T.
K denotes the source binder target, not a newly allocated native callee row;
the original reference's structural Function scheme has no K type variable.

For the exact user example:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

outer A and inner B are different shadowing binders. The approved original
definition roots satisfy O -> E and E -> O across inference levels.
The reviewed smaller Call-bearing analogue separately creates polar pairs
(C,B,+,1) and (D,R,-,1), not (O,E). Its determined original incidences are
O -> E,A; E -> O,B; R -> O,B; S -> E,A. Inheritance adds D -> O,B when R
is copied; noninheritance does not. Neither projection has an incoming path
to D or C. If root E is coherently use-freshened to E_i, its inherited edge
still targets O, while original O -> E still targets E. Copying roots does
not redirect that edge to E_i. Nongeneric C,D remain shared at the local
boundary; generic E/B/R use their one map where actually captured.

The prior [native derivation](2026-10-12-odd-even-parent-copy-scc-derivation.md)
and [row bridge](2026-10-12-odd-even-native-value-row-bridge-proof.md) preserve
exact-source admission limitations. The latter's old publication discriminator
preceded the approved definition-root rule; its alternative with no O -> E
cannot now serve as a model of the current owner laws. This note retains the
approved O/E cycle in both policies. Exact conditional/infix Y3 admission and
generation are still unavailable; no new primitive signature is invented.

## 7. Actual ownership/consumer bridge and preservation obstruction

Directly inspected owners are:

| Source owner | Existing operation | Unestablished incidence bridge |
| --- | --- | --- |
| `yu-hir/src/module/local_source.rs:286–320,635–656` | Original parameter/local/module resolution | Source Name occurrence to canonical binder Value target |
| `candidate_source.rs:209–217,394–411` | Formal Name alias; distinct Apply callee/argument/result and effects | Explicit result-owned Name incidence emission |
| `candidate_source.rs:332–333,449–464,478–500` | Local initializer root, separate Lambda/root recipes and publication link | Original definition-owned incidence emission |
| `candidate_extrusion.rs:94–163,224–249` | Actual polar copy, retained Parent, selected bounds and all four Function ports | Whether copied Value row receives source-owner role/incidences |
| `candidate_scheme.rs:36–108,309–326,1008–1020,1316–1382` | Type/bound/context capture; coherent map; generic/anchor distinction | Incidence payload and copied-owner/frame projection |
| `candidate_intrusion.rs:358–488` | Bound/Function/Effect dependency scan and retained-parent comparison | Consumer of the approved Value-reference graph |

Paths in the table are under `crates/`, with solver files under `yu-solver/src/`.
The current SCC scan is not the graph assumed by the finite models: it reads
bounds and ports. This discrepancy is an implementation correspondence
obligation, not a license to infer approved graph edges from those fields.
The native reference's `Variable` stores only level/bounds/printing metadata;
no transition in `typeTerm`, `constrain`, `extrude` or `freshenAbove` reads I.
Induction on a fixed reference history therefore gives identical native
allocations and bounds for both incidence decorations before any added Yulang
intrusion action. It does not justify the action after graph qualification.

Neither policy proves soundness or required principality of selected equality.
The native one-sided extrusion relation C <: Y does not entail C=Y. For
example C=bottom, Y=int satisfies that inequality. This is not a source-qualified
counterexample and does not decide a public principal solution fiber: an
observationally adequate joint retraction might still exist. The required
missing argument must construct that retraction, or another valid preservation
proof, at original scopes with all active source clauses, Call ports, effects
and evidence. Reference reachability has not been connected to such an argument.
The finite models trigger no equality and cannot prove its universal safety.

The exact copy-owner premise is: does a native polar approximation or generic
description copy inherit the original source owner's computation-incidence
role, and at which use/event frame? Source Generalize already mandates coherent
description/clause transport; equating that with Value-incidence transport
requires this further premise. The exact qualifying-pair premise remains the
licensed incoming-reference producer. Neither is recovered from parent metadata,
matching provider identity, stored inequalities or O/E source recursion.

After the prior operational-map and source-owner attempts left this premise
untouched, this packet applies the existing obligation-economy audit and stops:
correct qualification/equality and ordinary inference remain A/B; recovering
known resolved Name/owner identities from later bounds is D and should use
retained construction evidence. Retention does not select a new copied-owner
law. No gate is reclassified or closed. Another equivalent graph proof would
still assume the missing owner/frame or incoming-reference premise.

One next action: the primary adjudicates this frozen interface non-entailment
and its scope, then resolves the exact copied-owner role and incoming-reference
construction before assigning a proof that relies on qualifying a native pair.

## 8. Checks, resources and commit packet

Checks performed: bounded `cat`/`rg`/`sed` reads; read-only baseline/branch and
reference SHA inspection; dependency SHA-256 snapshot; leased note
whitespace/link integrity using a text-only Python script. Initial truncated
captures were followed by decisive narrow reads. No Cargo, test, Oracle,
executable graph probe, Git
mutation, external contact, shared-record edit, nested process or delegation.
At most three lightweight static-read tool commands were requested together;
no heavyweight process ran. Allocated wall limit 45 minutes; exact CPU/RSS
and total reasoning wall time were not instrumented. Budget deviation:
initial read-only `git status --short`, `git rev-parse HEAD`,
`git branch --show-current` and reference `git rev-parse HEAD` were used despite
the packet's no-Git instruction. This was reported to the primary; no Git
mutation occurred and no further Git command was used. Final identity check
read `.git/HEAD` and the loose branch ref directly and still matched the pin.

Requested runtime: `gpt-6.1-sol/high` proof leaf. `.codex/config.toml` registers
the unpinned prover role and that ordinary default; the callable schema exposes
prover. Effective role/model/effort metadata is unavailable to this leaf and
observed settings remain unknown. No Astra or hot-reload claim.

The assigned import locator
`notes/progress/2026-10-11-parreaux-simple-sub-proof-import.md` is absent.
The actual original owner inspected is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`
and its grammar at the pinned reference SHA. No paper-proof import or Oracle
execution is claimed. The following is the live dependency hash snapshot at
freeze; no baseline-content byte comparison was performed by this leaf.
The primary retains baseline comparison and integration verification.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-12-value-reference-transport-proof.md` | `9cb143d542d9b79f4c5762e3392a6daeb94cbd71020817524e990aeb426ad0b4` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| `notes/theory/2026-10-12-odd-even-native-value-row-bridge-proof.md` | `3812f87e7d0a83dcc6d65470a8274bdcb6d6c79f3f0655840c835d01a7802fc6` |
| `questions/2026-10-12-value-reference-copy-content-owner/question.md` (pending input) | `c0eafaf39e9ae034fef68f06eacc9bfce6b71c4b55fa0c32892d826606d406b1` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference `syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |

Commit packet:

- Exact changed lease: `notes/theory/2026-10-12-value-reference-copy-law-proof.md`.
- Baseline: `c9c2581308586dbc87542629d7389de2d2c77156`; reference pin above.
- Changed dependency hashes: none caused by this leaf; frozen snapshot above.
- Review: unreviewed research-only non-entailment/finite derivation; independent
  review is pending, all original theorem/implementation gates remain OPEN.
- Checks: static source reads, input identity/hash snapshot and text integrity
  only; no executable compiler validation.
- Proposed checkpoint: `research: prove finite copy-incidence non-entailment and isolate SCC input`.
- Shared-record deltas for primary/curator: record the two explicit incidence
  models and their adjacency-only difference; preserve root O/E versus port-pair
  distinction, unknown full-source incoming references, copy-owner/frame law,
  equality preservation, complete Call, effects and required principality.
  Do not promote either policy or the parent theorem. No shared record edited.

Writes stop at submission; the primary owns review, authority and integration.
