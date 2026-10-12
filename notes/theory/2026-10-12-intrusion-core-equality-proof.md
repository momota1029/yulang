# Intrusion equality: shared Function extrusion and the first missing bridge

Date: 2026-10-12
Status: frozen bounded constructive attempt; independently reviewed with no findings; parent theorem OPEN
Claim class: bounded native characterization and conditional derivations
Original soundness / required principality / source correspondence: OPEN
Baseline: `f29de555cfb845b6c6622ffcc6de09f4cbdbe160`
Branch: `research/simple-sub-intrusion`
Exclusive output: this file; leaf producer, no delegation or Git mutations

## 1. Frozen original statement

For every supported resolved Yulang source program `s`, its actual lexical
environment `Gamma`, original binder tree `T`, annotations, definition roots,
recursive boundaries and use occurrences, retain the following obligations.

1. Every successfully published inferred interface has a sound derivation for
   `s` in those same scopes, preserving complete Call and effect hygiene.
2. For every required original derivation `Gamma |- s : tau`, deterministic
   native inference succeeds normally and produces the required principal
   interface, subsuming `tau` in the governing scheme order. One joint scoped
   witness supplies its related coordinates; independent marginal witnesses
   do not suffice.
3. Every actual extrusion copy retains its actual parent, creation polarity
   and target level. If that exact parent/copy pair qualifies in the selected
   Value-reference SCC, solving and subsequent use equate them. Qualification
   comes from constructor-owned Value references, including the accepted
   source incidences, rather than comparison direction or genealogy.
4. Preserve monomorphic sharing inside the selected recursion boundary,
   lawful lexical generalization, independent fresh uses, retained normal
   suspension facts, semantic invalidation, termination and necessary abnormal
   publication safety.

These are the original all-source obligations, not a theorem about the smaller
pure calculation below. They are not discharged here. The imported pure order
is `P <=forall Q` iff some substitution of `P` is a subtype of `Q`; the
principal scheme is on the left. No alternative Yulang public order is adopted.

The local hypotheses used below are a subtype preorder with ordinary arrow
variance, one joint interpretation per variable identity, the exact pinned
reference constructors, and explicitly successful finite operations. A Value
SCC does **not** imply an inequality or equality. No unspecified copy-content
law, Call constructor, replay completion or generalization theorem is assumed.

Unverified cases are exclusions from this result, not restrictions on source:
all-source acceptance, complete Call, effects/protection, joint attachment,
provider, witness and residual lineage, qualified source equality, original
generalization adequacy, complete termination and production/F5 cutover.
No eager solving, speculative typing search, annotation requirement, recursion
restriction or canonical gate promotion is introduced.

## 2. Exact authority and dependency order

The governing operation is
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`: **Direct decision**,
**Selected operation and compiler responsibility**, **Value-reference SCC
clarification**, **Apply-result source-fragment ownership**, **Nested Apply
membership**, **Definition-root Value ownership**, and **Retained boundary**.
The top-level principles, §§1–5, **Evaluation**, and **Authority and
integration**, govern native structure and necessary abnormal safety.

`2026-10-08-source-generalize-definition.md`, §§2–4, preserves original Shared,
Desc, ViewLogic and event scopes, the complete simultaneous recursive relation,
actual fixed anchors and the final formed source root. The native pure level
calculation below is not a replacement for this selected source judgment.
`2026-10-10-local-self-recursive-binding.md`, **Selected source behavior** and
**Required invariants and evidence**, requires one open monomorphic initializer
root and later ordinary live capture/freshening. Apply the later top-level
principles before its historical general rollback clauses.

Workflow sources: `rules/agent-orchestration.md`, **Model routing and Astra
escalation**, **Proof delegation and decomposition**;
`rules/research-lab.md`, **One semantic baseline, explicit dependency
invalidation**, **Evidence quality and stopping unproductive loops**;
`rules/compiler-engineering.md`, **Natural compiler behavior and
proof-obligation economy**, **Deterministic Simple-sub inference**;
`rules/design-authority.md`, **Authority order**; and `rules/git-concurrency.md`,
**Disjoint-file mode**. The primary retains authority, independent review,
shared records and integration.

Original source: Lionel Parreaux, *The Simple Essence of Algebraic Subtyping*,
paper §§3.2,3.5, Figs.6–9; §5, Figs.10–12, local
`/home/momota1029/rust/simple-sub-reference-paper.pdf`. The original operational
checkout is `/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`. Reference line numbers below are
in `shared/src/main/scala/simplesub/Typer.scala`.

The correctly located import is
`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`, not the absent
`notes/progress/` locator in the initial packet. It imports theorem statements
and sketches, explicitly retaining the omitted proofs and §5's non-let scope.
The paper's extrusion explanation on printed pp.18–19 expressly retains
independent later instantiations inside the approximating bounds. It contains
no Value-reference intrusion theorem.

The proof clauses have this dependency order; this is not a new gate taxonomy:

| Clause | Required evidence | Result here |
| --- | --- | --- |
| Native formation | Actual binders and Function/Apply demands | Direct reference source trace, §4 |
| Native extrusion | Joint polar copies, links, levels and actual parent records | Direct reference trace; Rust creation owners identified |
| Qualification bridge | Constructor-owned Value contents and their transport on those exact copies | First missing premise, §7 |
| Equality preservation | Joint required source witnesses survive the qualified equality and future consumers | OPEN; algebra alone does not supply it |
| Generalization/fresh use | Original fixed/template scopes and simultaneous recursion preserved | OPEN; explicit discriminator, §6 |
| Complete source/implementation use | Call/effects, actual replay, invalidation and publication | OPEN; owner crosswalk only |

The older native-spec proof's quotient algebra and continuation obstruction
remain conditional results. No third quotient proof is attempted here.

## 3. Small native transition system, with its missing operation explicit

A pure native state contains exact variable identities with immutable reference
levels, lower/upper lists, pending comparison invocations, schemes and lexical
environment entries. Structural terms are canonical primitives, variables,
Functions and records. Structural syntax is finite between variable occurrences;
bound references may cycle. The level of a structural term is the maximum
variable level. Polarity belongs to an extrusion occurrence, not a new source
binder.

Generation, accumulation and consumers are the actual native operations:

```text
Name(x)       = instantiate(Gamma(x))
Lambda(x,t)   = Function(a,infer(t,Gamma[x:=a])), fresh a at current level
Apply(f,t)    = b, after submit(infer(f) <= Function(infer(t),b))

Function(a,r) <= Function(b,s)  ->  submit(b <= a), submit(r <= s)
a <= u, level(u)<=level(a)     ->  prepend u to U(a); submit every l<=u, l in L(a)
l <= a, level(l)<=level(a)     ->  prepend l to L(a); submit every l<=u, u in U(a)
level violation               ->  extrude offending side, then retry comparison
```

Matching order matters: equal-level variable pairs use the first applicable
branch; storage need not occur on both endpoints. Identity returns and the
cache are reference `:93–103`; Function and insertion consumers are `:106–126`.
Submitting a replay is a real invocation in this synchronous reference, but
an analogous pending/cache field in Rust does not prove complete activation.
Bulk initialization and merged cross pairs retain their separate coverage
premises; the repaired native-core Lemma 1 is not bypassed.

For target `k`, `E_k^q(t)` returns an acceptable-level term unchanged. It maps
Function argument polarity to `-q` and result polarity to `q`. For an above-level
variable `a`, memoize one fresh `c` for `(a,q)` before descending:

```text
q=+: U(a) := c :: U(a); L(c) := map(E_k^+, L(a))
q=-: L(a) := c :: L(a); U(c) := map(E_k^-, U(a))
```

The selected extension records `Parent(c,a,q,k,creation)` at that creation;
the Scala reference has no such retained record. One operation memo shares
same-polarity occurrences and distinguishes opposite polarities.

Reference lexical publication at boundary `h` retains `(h,t)` after inference
at `h+1`. Recursive introduction first exposes one monomorphic placeholder,
submits the initializer below it, then publishes (`:48–55`). A use memoizes one
image for each reachable variable above `h`, copies **both** bound lists, and
shares variables at/below `h` (`:166–207`). Different use memos are independent;
aliases and initializer recursive references are not separate uses.

Separately retain Value source incidences and actual owned Value descriptions:

```text
Apply result R --occurrence o--> original resolved binder row B(o)
definition root D --owned occurrence o--> original resolved binder row B(o)
```

Nested Apply callee/argument subtrees contribute their resolved Names; they do
not add an edge to an intermediate Apply result merely by containment. Nested
declaration initializers belong to their own root. The accepted decisions do
not identify these roots with Function ports or Lambda/Block/Apply rows.

The selected intrusion transition is a **guarded specified operation**:

```text
Parent(c,p,q,k,e) and sameSCC(actual Value references, rep(c),rep(p))
   -> equate(c,p), redirect actual row occurrences, retain all owned constraints
```

The source-reference transport at extrusion and fresh use has no independently
established transition in this packet's inputs. Consequently this is a small
native system plus a partial approved extension, not a complete new semantics.
Filling its missing Value-content operation by assumption would defeat the
assigned proof. Complete Yulang Call/effects remain their original judgments,
not extra axioms inferred from the pure Function comparison.

## 4. Decisive shared-parent Function: exact finite construction

Freeze an initially empty variable `a` at level `h>k` and the shared term
`Function(a,a)`. Both occurrences are the same original variable identity.
Execute **positive** extrusion with one initially empty memo. Scala evaluates
the Function argument before the result (`:144`).

1. Visit its argument negatively. Allocate `m` at `k`, memoize `(a,-)->m`,
   and write `L(a)=[m]`. `U(a)` was empty, so `U(m)=[]`.
2. Visit its result positively. The negative memo key does not match. Allocate
   distinct `p` at `k`, memoize `(a,+)->p`, and write `U(a)=[p]`.
3. The positive copy now traverses `L(a)=[m]`, including step 1's new bound.
   `m` has acceptable level, so it is retained unchanged. Thus `L(p)=[m]`.
4. Return `Function(m,p)`.

The complete nonempty lists are therefore

```text
L(a)=[m]   U(a)=[p]   L(p)=[m]
```

Their comparison meanings are `m<=a<=p` and `m<=p`. This last bound is a
real order-sensitive write, not a separately chosen result witness. Both
selected parent records would point to `a`, with opposite polarities.

Under ordinary arrow variance, `m<=a<=p` gives
`Function(a,a)<=Function(m,p)`: reverse the argument inequality and preserve
the result inequality. For every interpretation `A` of the initially empty
`a`, the joint extension `m=A,p=A` satisfies this creation snapshot. Neither
this existence statement nor the approximation inequality proves qualified
equality under later source constraints or generalization.

For comparison, negative extrusion of the same empty shared Function first
creates a positive copy `p`, then a negative copy `m`; the second write copies
the already installed upper and produces `U(m)=[p]`. The same inequalities
hold, but the physical owner of the extra `m<=p` comparison differs. Neither
physical storage is declared to be the approved Value incidence.

### Source reachability of this pure extrusion, without invented SCC membership

The exact reference AST

```text
Lam("f", Let(false,"r", App(Var("f"),Lam("x",Var("x"))), Lit(0)))
```

at level 0 constructs the positive extrusion just traced. The outer lambda
allocates `f`'s monomorphic row `phi` at 0. The let initializer runs at 1;
its inner lambda creates `a` at 1 and returns `Function(a,a)`. Its Apply result
`b` is at 1 and submits

```text
phi <= Function(Function(a,a),b).
```

The right-hand demand exceeds `phi`'s level, so `:121–123` extrudes it negatively
to 0. Its argument is extruded positively and is exactly §4's shared Function;
its result obtains a separate negative copy `n`. The retained demand is
`phi<=Function(Function(m,p),n)`, and the Apply returns `b`.

This is a manual source-constructor derivation, with no parser or inference
execution. It establishes reachability in the **reference calculus**. No Yulang
lowering or complete Call equivalence is claimed. The accepted source Name
`f` supplies the applicable Apply incidence to `f`'s original binder row;
it does not turn that Name into an edge to `a`, `m` or `p`. Apply membership
through the inner Lambda subtree remains outside the approved nested-Apply
rule. Definition-root ownership cannot identify its root with `a` either.

## 5. Actual Rust constructor/consumer correspondence and gap

The pinned compiler is source evidence, not semantic authority for the rebuild:

| Actual owner | Exact locator | Established inspection fact / limit |
| --- | --- | --- |
| Name / Apply source construction | `candidate_source.rs:369–410`; `shadow_apply.rs:1192–1285` | Resolved Names retain use/formal identities; Apply retains callee/argument/result recipe and source input. This does not exhibit the approved recursive Name-incidence payload on the result row or its copy transport. |
| Parent retention | `candidate_extrusion.rs:81–124`; `candidate_intrusion.rs:171–220` | Fresh copy and actual parent, polarity and target are retained before copying selected bounds. |
| Mixed Function extrusion | `candidate_extrusion.rs:213–259,308–324` | Four actual ports retain composed polarity; row copies and structural copies have separate operation-local memos. Bounds are installed by a separate pending-bound phase. Thus the entire Rust bound snapshot cannot be inferred merely from Scala's recursive evaluation order. |
| SCC construction | `candidate_intrusion.rs:358–486` | Scans both bound sides and structural Value **and Effect** ports, then tests retained parent pairs against component numbers. It is not inspection evidence of the new Apply/definition-root source-incidence SCC on those exact pairs. |
| Equality use | `candidate_intrusion.rs:515–605` | Appends bound sides, transfers origins, canonicalizes representatives, takes minimum levels, invalidates/reopens a root and calls replay. This is an actual equality consumer, not a proof that its qualification or replay closure is semantically adequate. |
| Capture / fresh-use decision | `candidate_scheme.rs:302–326,981–1020` | Generic rows require level above boundary and non-generic metadata false; current canonical row and current level are rechecked when freshening. |

The SCC scanner's bound fields are actual Rust payload references. The missing
bridge is **not** a claim that these physical handles do not exist. It is the
unproved identification/coverage of that scan with the approved constructor-owned
source incidence on original roots and exact copies, including its Value-only
qualification. Adding the accepted source incidences can create cross-level
root SCCs that the reference level invariant never described. Conversely,
cross-level root reachability does not show any recorded extrusion pair belongs
to that SCC.

No all-writer level invariant, complete replay, rollback conformance or source
acceptance theorem is derived from these bounded reads. The earlier native
reference-map characterization predates the new source-incidence decisions;
its bound-reference inventory remains evidence, not a substitute graph.

## 6. Generalization discriminator: the original quantifier cannot disappear

Freeze the §4 store at publication boundary `k`, an interface
`Function(a,a)`, and shared captures `m,p`. Ordinary reference freshening
quantifies `a` above the boundary while retaining its constraints to `m,p`.
Two independent uses allocate **different** `a1,a2`, each with

```text
m<=ai<=p             interface Function(ai,ai), i=1,2.
```

The captures remain shared. Within each use the argument/result and both bound
sides use the same `ai`; no marginal choices occur.

For a bounded pure semantic discriminator take `m=Bottom,p=Top`, incomparable
canonical `Int,Bool`, and client demands

```text
Int<=a1<=Int         Bool<=a2<=Bool.
```

One joint assignment `a1=Int,a2=Bool` satisfies all clauses. If an intrusion
equates `a` with either level-`k` copy before publication and generic eligibility
uses the canonical minimum level, both uses now share one captured `d`.
The same demands imply `Int<=d<=Int` and `Bool<=d<=Bool`, hence
`Int<=Bool` by transitivity, contradiction.

This is a finite **conditional generalization discriminator**, not a
source-qualified counterexample to the approved intrusion. It supplies no SCC,
and does not establish that the selected source Generalize regards this
particular `a` as an eligible Desc in a qualifying source run. Its purpose is
to expose exactly what a preservation proof must derive: original publication
scopes and required independent descriptions cannot be removed simply because
an equal witness existed at extrusion creation. The controlling Rust minimum
level and fresh-use tests have actual owners in §5.

A source proof could show that the original typing fixes this coordinate under
the qualifying construction, or establish another scope-preserving joint
correspondence. Neither is assumed. Requiring all such coordinates to be fixed
as a new source restriction would weaken the original theorem. Declaring
freshening to recover a lost generic variable by itself would change the native
operation and requires separate authority.

## 7. Precise OPEN obstruction and obligation-economy audit

Two distinct attacks were made: (i) derive the exact shared Function polar
construction and its semantic inequalities; (ii) invert a real reference source
term and match the accepted source ownership rules and actual Rust consumers.
Both stop before the same operational premise. No further equivalent quotient,
bound-SCC reconstruction or arbitrary hand-added return edge is used.

The **first unproved premise** is this source/operational sequent on exact
objects, not the old undecided Apply ownership question:

```text
For the actual supported source prefix, original scopes T and state Sigma:
  extrusion event e creates c from parent a, at polarity q and target k;
  constructor-owned Value descriptions/incidences are transported by that event;
  the resulting explicit reference occurrences, with their actual targets,
  are exactly the references consumed for the qualifying SCC test on (c,a).
```

The required evidence must name the owner and reference payload for `a,m,p`
in the shared Function case, determine whether resolved binder targets remain
original rows or acquire a lawful transported image, retain each source
occurrence and its ownership boundary, and derive any two-way paths on those
exact objects. It must similarly state what fresh use and canonical equality
do to those references. Level ordering, comparison direction, provider shape,
copy genealogy and definition-root SCCs cannot supply that missing sequent.

After this premise comes the still-unproved **semantic** induction step:
for every required original scoped source typing represented before a qualifying
merge, obtain one joint typing witness afterward with the same original scopes,
complete Call/effects and required principal relation, including ordinary later
constraints and lawful generalization. SCC qualification is not that proof.

Economy audit under `compiler-engineering.md`:

- Qualification/transport conformance is A; maintaining ordinary recursive
  inference and lawful independent publication uses is B. Both remain required.
- Reconstructing occurrence owners from solver bounds or result providers is D.
  Apply and definition construction already know the resolved occurrences;
  retain their canonical incidence instead of proving an inverse relation.
- The copy transport law and qualified equality/generalization preservation
  are genuine A/B semantics, not debt removed merely by keeping a field.
- Equality of **every** internal valuation is a possible stronger C route,
  not silently added as a requirement. Required joint source witnesses remain
  the original obligation; neither classification nor a changed plan closes it.

One next action: the primary obtains the exact Value-content/copy transport
constructor law and an actual creation-to-SCC trace for this family from its
responsible source/construction owner. Resume equality and original binder
preservation on that trace, using the §6 discriminator. This leaf selects no
answer to pending ownership questions and does not contact their recipients.

## 8. Checks, resources and runtime

Static reads only: `cat`, `sed`, `nl`, `rg`, `pdftotext -layout ... -` with
bounded section capture; read-only `git rev-parse`, `git branch --show-current`,
`git status --short`, dependency-scoped `git diff --name-only`; `sha256sum`.
The Yulang and reference revisions matched their pins. The inspected direct
compiler/authority inputs had no diff against the assigned baseline. Unrelated
untracked leased artifacts and question directories were not consumed or changed.

No tests, builds, Oracle invocation, instrumentation, executable checker,
benchmark, compiler edit, Git mutation or child assignment ran. At most three
parallel lightweight inspection shells; zero heavyweight jobs and measurement
samples. CPU/RSS were not instrumented. Work remains within the 45-minute
static-attempt bound; exact whole-task wall time is not inferred from individual
shell timings. The primary remains the verification and integration owner.

Requested route: ordinary Sol/high proof leaf, as configured by
`.codex/config.toml`; `prover` is registered there and omits model/effort pins.
No effective leaf runtime model/effort metadata was exposed: observed settings
are **unknown**. No override, Astra execution or hot reload is claimed.

## 9. Frozen dependency snapshot and commit packet

Content SHA-256 of direct semantic/source inputs inspected:

```text
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
parent-copy decision fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c
source Generalize    46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
local self-recursion 38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895
original import     cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113
native-spec proof   ea09a810be20984ca6c2711c4372e77cc7c360b2b208946465fcf6dad5bd4b33
repaired native core 08f178b448c711c43938ec26dd438c18bbee5d47ee4d11f1a03d2e88839f6597
native reference map 66f8f068c453d491d45c09fe22a27f7a63ea5a31ca200b4cb15c4c21f4dbaad0
candidate_extrusion fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_intrusion aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
candidate_source    13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_scheme    9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
shadow_apply        cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411
reference Typer     f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
reference paper     5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
```

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-intrusion-core-equality-proof.md`.
- Baseline SHA: `f29de555cfb845b6c6622ffcc6de09f4cbdbe160`.
- Changed dependency hashes: none; revalidate against the snapshot before integration.
- Review: independent compiler-referee review found no issue. It confirmed
  the ordered polar-copy writes, source reachability, the explicit separation
  between accepted incidences and unproved copy-content/SCC qualification,
  and the conditional joint-use discriminator. The original all-source
  equality/principality theorem remains OPEN; the discriminator is not a
  qualified source counterexample.
- Checks already run: bounded static owner/pin/hash inspection and final
  whitespace/dependency integrity check; no semantic execution.
- Proposed checkpoint message: `research: trace shared Function intrusion proof frontier`.
- Shared-record deltas left to primary/curator: link the exact shared Function
  source trace and original-quantifier discriminator; keep the parent theorem
  OPEN at Value-content transport/qualification, followed by joint equality and
  generalization preservation. Do not report the new source ownership decisions
  as still undecided, or treat a reference term as a Yulang qualifying witness.

Producer writes stop at handoff. Primary owns independent review and integration.
