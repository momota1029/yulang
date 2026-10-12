# Source publication classification: nested recursive-f helper

Date: 2026-10-12
Status: independently reviewed bounded constructor obstruction and
conditional application of the selected closure/allocation rules
Assigned baseline: `ba93e1739`, branch `research/simple-sub-intrusion`
Exclusive lease: this file only; prover leaf, no delegation

## 1. Frozen objective and scope

Determine the Source Generalize classification for the **existing** witness
in [correlated helper search](../progress/2026-10-12-intrusion-occurrence-counterexample-search.md)
§§1–3:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

This is the recorded original-Simple-sub AST witness, not a claim of exact
Yulang parsing, admission, or builtins. No new witness is introduced. Fix its
original resolved binders, definition roots F/G, source binder tree T, actual
source objects/worlds and the actual G-origin/F-receiver demand occurrence c.
The integrated definition-root origin decision applies under the wrapper and
is not reopened. Native types B,C,D,R remain distinct from source Values and
from the validating component, which is written K throughout this note.

The required question ranges over every lawful finite independent client
allocation of this publication and its monomorphic aliases, retaining the
whole dependent source program and all its active clauses. At p_g, identify
the registered validating component K_g, f's typed relation/contract edge,
Parameter's B declaration, and the source operands/telescopes of both
qualified equalities `C=B` and `D=R`. Apply the selected least retain/fix
closure and whole-component allocation. A native cutoff is not a premise
that C is a source fixed anchor.

**Claim class and result:** bounded source-to-construction obstruction. The
inspected producers do not supply the registration/dependency input or the
typed extrusion operands required to instantiate this closure on the witness.
Consequently no actual fixed-versus-frame-relative classification of C, and
no complete allocated equality clause, is derived. Sections 4–5 give a
constructive conditional discriminator and show exactly why the existing
contradiction cannot yet be applied. This is neither an impossibility theorem
for a future constructor nor a refutation of source admission.

Authority is existing; behavior change none; artifact scope internal research;
runtime impact none. No compiler, tests, expectations, semantics, shared
records, questions, configuration or Git mutation is authorized. Source
admission, L4, full allocation, soundness, required principality, complete
Call/effects, normal progress, termination and F5 retain their OPEN gates.

## 2. Authority, scopes and independently established native facts

Governing sources are [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md)
§§2–3; and its [construction](2026-10-08-source-generalize-definition-and-proof.md)
§§3.1–3.3, 4, 5.1–5.3. The parent-copy decision's Selected operation,
Definition-root ownership and Retained boundary, together with the association
clarification's Approved extrusion-event qualification and Definition-root
origin section, fix qualification only. They do not supply registration K_g
or the source realization of a native copied coordinate.

The reference `Typer.scala:48–55,62–83,115–156,166–188,201–207` constructs:

| Actual reference owner | Constructed fact |
| --- | --- |
| Recursive `typeLetRhs(f)` | One placeholder o at level 1, monomorphic in f's RHS, and recursive completion below o |
| Nonrecursive `typeLetRhs(g)` | Infer the RHS at level 2 and then form `PolymorphicType(1,Function(B,S))` |
| Lambda y / Lambda z / App c | B and Z, and demand `o <: Function(B,R)`; wrapper yields `R <: Z`, `B <: S` |
| Negative extrusion of demand | Actual positive copy C of B and negative copy D of R at level 1; `B <: C`, `D <: R`, `o <: Function(C,D)` |
| Two g Names / `freshenAbove` | Distinct coherent B0/S0 and B1/S1 maps; the native level-1 C is retained |

These are native constructor facts already derived by the existing witness,
rechecked against the reference bodies here. They do not introduce Source
Generalize's `Desc`, `Established`, `Internal` or event fields. In particular
the reference's complete local context entry is an algorithmic TypeScheme;
`SimpleType.instantiate=this` establishes native monomorphism, not the source
provenance tag Established.

Original semantic scopes stay in place. p_g is g's closure publication inside
an actual outer-f invocation, preceding that invocation's subsequent g uses.
Parameter's logical y-description scope is before g's invocation challenge;
g's returned closure/capture is an actual object within the outer event. At a
g invocation the wrapper Lambda captures the actual rebound y. In the selected
complete Call meaning its bare z entry forces the inert `f y` argument through
the designated consumer; that inner Call retains the actual wrapper-entry
event and pending suffix. This is not a license to move that Call to g's
initializer event or to replace its whole argument by one scalar Value port.
The exact semantic telescope of native R/C/D is one of the missing outputs;
their equal numeric levels do not define it. No finite postfixedness or
complete Function checking proof for actual recursive f is assumed.

## 3. Owning constructors and their actual output boundary

The selected source grammar requires original local operands and §3.3 typed
records *before* §4 Build and §5's dependency walk. Semantic satisfaction is
later: missing L4 validity does not prevent structurally registering K_g,
but a structural registration is not a proof of L4 validity.

The implementation locators below audit the common nested binding/Call
constructors. They do not establish a Yulang lowering route for the original
Record/Bool/builtin AST above. After this derivation, the primary supplied the
frozen [complementary owner census](../progress/2026-10-12-source-registration-owner-audit.md)
at the same assigned baseline. That census audits the already recorded
116-byte Int/Unit source fixture, a distinct existing witness with the same
publication seam; its exact-source observations are not transferred to the
reference AST. Its constructor-field findings agree with these direct reads.
It is complementary evidence, not independent review of this derivation.

| Owner / locator | Actual retained output | Required source output not supplied by that output |
| --- | --- | --- |
| `crates/yu-hir/src/module/local_source.rs:104–171,329–374,710–819` | Resolved local/formal IDs, original source keys, lexical scope, Lambda/Apply/Block syntax; temporary parameterized self entry and sequential Publish | Publication/component relation and typed f edge. Publish installs a lexical name; it does not emit `ScopedClosure` or a validating K registration |
| `crates/yu-solver/src/candidate_source.rs:12–34,200–217,254–328,369–410` | Slots; formal endpoint incidence; active f lookup becomes `Action::Link`, later g lookup becomes `Action::Local`; `Action::Install` retains slot/initializer/boundary | `Desc(K_g,y,Value,sigma_y,Delta_y)` with semantic dependencies; f's `Internal(K_g,f)` versus full `Mono/Established` contract |
| `crates/yu-solver/src/candidate_source.rs:624–651`; `candidate_scheme.rs:116–120,1320–1334` | Native publication stage stores `LocalScheme { id, root, boundary }` | p_g's source Generalize package, final full root and complete validating relation |
| `crates/yu-solver/src/candidate_call.rs:12–56,83–124,215–250` | Formal/Apply source incidences and native interface; explicit missing complete-Call suppliers | Original Gen-Call operands, whole carrier, receiver/entry, complete result/future interface and their source telescopes |
| `crates/yu-solver/src/lib.rs:12411–12439`; `candidate_extrusion.rs:21–35,95–126,210–250` | Crossing dispatch passes endpoint/polarity/level; copy retained before selected bound traversal; four-port polarity recursion | Original source declaration/field/term realized by C/D, its scope/dependencies, and one complete scoped occurrence equality clause |
| `crates/yu-solver/src/candidate_intrusion.rs:171–219,358–402` | `Parent { copy,parent,polarity,target }`; settlement starts a graph over native endpoints/bounds | Approved source-Value occurrence qualification and source registration/classification. Native endpoint graph is not K_g |
| `crates/yu-solver/src/candidate_scheme.rs:301–321,568–572,981–1020,1354–1378` | Native locality/copy test uses boundary, level, non_generic and representative; coherent capture/fresh maps and bound restoration | Correspondence to the selected source retain/fix result and whole-component dependent allocation |

HIR has enough syntax to locate the prospective g-publication site and the
original y introduction. It cannot decide the semantic registration from its
single carrier `DefinitionRootId`: both nested locals are carried by the outer
source object, while HirLocalId still distinguishes them. Neither that shared
carrier nor its local parameter-owner map determines validating K membership.
Likewise `component_levels` uses numeric solver component positions, not the
selected validating component record.

The source grammar itself is precise *given* its registration operands:
same-K recursive registration supplies Live/Internal and the whole joint
relation; external monomorphic capture supplies Mono/Established and all
free contract fields. §5.3 constructs the particular simultaneous bare pair
and the particular nested helper capturing an actually rebound formal.
Neither supplies this nested nonrecursive g's registration with active
recursive ancestor f. Nonrecursion of g does not choose that classification:
the reference merely refrains from allocating g a self placeholder.
Inferring singleton K_g, merging F/G by their Value SCC, or classifying f from
its raw provider would fill the missing registration by an unsupported rule.

There is a second independent obstruction even if K_g were supplied. C/D
are fresh native rows with polar parents. No inspected source introduction
identifies them with an ordinary Desc, a fixed field, or a well-scoped derived
endpoint term in T. Parameter's B record cannot stand in for the complete
call-demand/extrusion realization. The Source Generalize walk classifies
existing records; it does not manufacture the missing operand from its row
number. Build cannot append `C=B,D=R` as source clauses without those operands
and their legal scopes.

The focused symbol search for `Desc(`, `MemberEntry`, `Internal(`,
`Established(` and `ScopedClosure` found no such implementations in the
inspected HIR/solver source trees. This is bounded evidence about these
constructors, not a theorem that no differently named or future implementation
can provide the records. The field/body traces above are the operative evidence.

## 4. Conditional least-closure derivation and a constructive discriminator

Fix any **independently supplied** well-formed p_g/K_g record graph G from the
selected owning rules, with original telescope T. Form the finite reachability
closure on pairs `(record, retain/fix)` starting from §5.1's exact seeds.
Follow rule 2's complete fixed dependent fields, rule 3's complete Internal
relation in retain mode, and rule 4's original Shared/ViewLogic/event regions.
Record a free ordinary Desc as fixed whenever a prescribed fix traversal
reaches it. This monotone walk has a unique least visited/marked set: iterating
the fixed transition rules adds only reachable states; induction on path
length proves every legal finite path is eventually included. Cyclic Internal
edges add no extra fixing rule. This is an application of the selected walk,
not a new registration or inverse reconstruction layer.

Thus, for an actually introduced ordinary declaration q owned by K_g:

```text
eligible(q) iff retained(q) and not fixed_mark(q).
```

If q is eligible, §5.2 `new(p_g,i,g)` gives `(i,q)` at the translated original
scope. If fixed, its original field/binder incidence is shared. Aliases route
to the same frame. For an endpoint *term* C rather than a Desc, apply the
declaration map to its actual free operands in its legal telescope; this can
give a frame-relative term without creating a new C declaration. Frame-relative
incidence does not guarantee different semantic values in different frames.

Here is the requested constructive discriminator, **conditional on real owner
records**, with no claim that either footprint is emitted for this witness:

| Typed footprint to be tested | Selected walk and allocation consequence |
| --- | --- |
| The actual f capture is `Mono(h_f,Contract_f)` with a free C field in that complete established contract | Fix reaches C and every free dependency required by Contract_f. Uses retain that original C incidence even when B is eligible |
| The actual f edge is Internal to K_g; C is an own-K_g ordinary Desc or a lawful term of eligible own-K_g declarations; no actual fixed contract/Shared/OneShot dependency reaches those declarations | Raw f provider is fixed separately; Internal enters retain mode. Those declarations are eligible, and C's source incidence follows the whole frame's translated terms |

Same-K Internal alone is insufficient for the second conclusion: an actual
external or executed dependent field can still mark those descriptions fixed.
Established f alone is insufficient for the first conclusion unless its
**complete contract actually has C free**. These qualifications are exactly why
the missing operand/dependency output matters.

An active inequality or equality does not by itself create an Established
dependency edge. For example B can be an allocated eligible declaration with
the active clause `B_i=C_shared`; all its possible values are then constrained
by that same shared C. Treating equality as a new fixing edge would change the
selected walk. Treating a copied eligible declaration as independently free
of its retained equality would change the selected program.

This discriminator requires no new source annotation, restriction, provider,
marginal witness or schedule. Numeric levels and Value SCC can stay identical
in its two conditional inputs: neither is a transition of this typed walk.
It does not establish that both inputs are legal completions of the witness.

## 5. Complete clause transport and the existing conditional contradiction

Suppose the real owners supply one complete well-scoped extrusion/equality
clause Q_c with C/B/D/R operands, the same origin/receiver and every dependent
Call/checking/effect/residual field. Whole-frame allocation must apply one
coherent declaration/term map m_i to **that whole clause in its original binder
region**, alongside all background and component conjuncts:

```text
Q_c,i = m_i(Q_c), including m_i(C)=m_i(B), m_i(D)=m_i(R).
```

The notation is conditional: it does not construct the missing Q_c or flatten
the nested event/Pi/Sigma telescope into four unscoped variables. A scoped
coordinate family needs its actual lawful transport map. Shared runtime
operands remain shared; frame-owned ViewLogic/EventProof witnesses retain
their respective dependencies and actual-event incidence. Complete Call,
attachment/provider/witness/residual identities remain distinct.

If C is shared and Q_c is active in both lawful g frames, the existing native
projection's two-use chain is

```text
bool <: B1 = C = B0 <: S0 <: V0 <: int.
```

This reproduces the existing conditional `bool <: int` obstruction. D=R is
retained in the same clause; it is not the cause of this projected conflict.
If C instead has lawful frame-relative incidences C0/C1, these equalities alone
give no C0=C1, so this particular transitivity chain cannot be imported.
Additional retained component clauses may correlate them; no satisfiable
complete alternative allocation is proved here.

The reviewed [ALG theorem](2026-10-12-quotient-solution-correspondence-proof.md)
§§3–6 can represent the equality-augmented allocated presentation *after* its
coordinate interpretation and telescope transport have been established.
It neither chooses the shared incidence nor constructs Q_c, and does not
establish joint source witness preservation or lawful generalized eligibility.
After publication a stored native equality also supplies no theorem of its
activation/replay into existing use frames. The current approved operation
leaves that schedule/transport bridge open. No source-qualified contradiction
follows from the present inputs.

## 6. Exact missing producer output and economy stop

The smallest decision-relevant source output has two independent parts:

1. **Registration/publication owner:** the actual p_g in its enclosing event,
   registered K_g and retained complete relation, f's typed relation/contract
   edge, and Parameter's `Desc(K_g,y,Value,sigma_y,Delta_y)` with its actual
   dependency telescope. Its fixed seeds and field edges must expose every
   free dependency relevant to C/B; provider and lexical IDs are locators.
2. **Complete Call-demand/extrusion owner at c:** the source declaration,
   field or lawful endpoint term realized by each native C/D/B/R occurrence;
   their original sorts, scope/dependency maps; and the qualified whole clause
   Q_c with all dependent fields, retaining the actual generated pairs. This
   output must come from an authentic source construction law, not a guessed
   tag attached after observing native success.

For the classification query, a complete typed dependency cone from the
selected seeds to those operands suffices for the walk. Omitting K/edge
classification leaves Internal-versus-fixed traversal undefined. Omitting the
operand realization leaves no source node to traverse or substitute. Omitting
free dependencies makes the least fixed set unjustified. Omitting the clause
scope leaves allocation transport undefined. Full semantic admission and L4
remain separate obligations even after these structural outputs exist.
This specifies a necessary interface cut, not a proposed runtime representation
or an authorized implementation policy.

The prior publication construction and quotient/allocation audit already left
this source operand/classification premise untouched. This pass refines its
two independent producers and conditional consumer test; it does not claim
closure or new evidence for the absent producer. Economy audit: faithful
scope/publication/equality transport is A, ordinary independent helper use and
required principality are B, while recovering original incidence/owner data
from numeric rows is D debt inside that bridge. A retained constructor output
can remove reconstruction debt but cannot invent a recursive law, complete
Call admission, or equality-preservation theorem. No A/B gate is relabeled.

**One next action:** the primary assigns a bounded constructive owner packet
for the above registration plus c's source operand/dependency output, supplying
the already selected source laws and preserving T. Consume that real output
with §4's discriminator before another fixed-anchor proof or quotient probe.
If no selected law constructs the output, return that precise unprovided law
to the existing authority path. This leaf neither selects a replacement
classification nor asks the user for a new decision.

## 7. Checks, dependencies, resources and frozen handoff

Checks performed: static rules/skill/configuration and exact source/design
reads; manual native constructor trace, least-closure argument, conditional
whole-clause allocation and transitivity derivation; focused producer-symbol
search; dependency SHA-256 capture. No tests/builds/probes, parser runs,
measurements, child launches or Git operations. At most one lightweight shell
command was awaited at a time; no heavy process. CPU/RSS and OS descendant
counts were not instrumented; 30-minute wall ceiling. A failed reference-path
lookup was corrected by `rg --files`, with no state mutation.

Requested runtime: `gpt-6.1-sol/high`. Observed effective model/effort: unknown;
this leaf received no effective runtime metadata. `.codex/config.toml`
registers prover and normal Sol/high defaults; prover.toml has no model/effort
pins. The live schema exposes prover. Those facts do not certify this session's
effective routing. No Astra, reload or child launch is claimed.

Only the exact leased artifact is changed. It is unreviewed and frozen at
handoff; the primary owns fresh independent review and any promotion. All
classification, admission, source-to-native and parent closure limits above
remain unverified beyond the stated bounded derivations. Dependencies were
read from the shared filesystem and hashed; no Git commands were used to
establish equality with the pinned revision. Primary must compare the snapshot
against `ba93e1739` and revalidate any movement before integration.

### Direct dependency snapshot

| Dependency | SHA-256 |
| --- | --- |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Source Generalize selection | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Occurrence association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Parent-copy selection | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Reviewed ALG note | `5c93588f2fce49ce2dad6ece1c7265a61b8bac7f648263c098ba2c5746443711` |
| Quotient/allocation audit | `692903a8e5c8866b24102b5223700d50815a4b8a9cc6239c17027555936c1953` |
| Existing correlated helper | `ef308b68e967d916278b2d6e106731c723368f0477ecc947a12eb99c7f17a956` |
| Prior publication construction | `f103bfd39d7cca5012315246e154bd6c1c7f8c3f044b1f27bc2219be2b41d0a1` |
| HIR local_source.rs | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| candidate_source.rs | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| candidate_extrusion.rs | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_scheme.rs | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| candidate_call.rs | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| candidate_intrusion.rs | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| Solver lib.rs | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Complementary owner census | `c5e6c02f867d4e2454887bd747fdc2c5dfc953100e8c2148f18b204cdf11387a` |

## Commit packet

- Exact leased/changed path:
  `notes/theory/2026-10-12-source-publication-classification-proof.md`.
- Assigned baseline: `ba93e1739`; no dependency was changed by this leaf.
  Direct hashes above; pinned-revision comparison remains primary-owned.
- Honest status: unreviewed bounded producer obstruction and conditional
  closure/allocation discriminator; no actual C classification, source
  refutation, theorem status promotion or implementation authority.
- Checks already run: static producer/consumer tracing, manual conditional
  derivations and dependency hashes; zero tests/builds/probes. Artifact
  integrity and dependency stability are reported in the final handoff.
- Proposed checkpoint: `research: isolate source publication classification producer cut`.
- Shared-record delta left to primary/curator: keep C classification and
  allocated equality OPEN; record registration/typed-f-edge and scoped
  extrusion-operand output as separate missing producers. Retain the existing
  correlated-helper contradiction as conditional on shared C plus active
  complete equality transport. Keep L4, complete Call/effects, soundness,
  required principality, full allocation and F5 OPEN. No shared record edited.

## Independent review

A fresh `compiler_referee` reviewed the frozen artifact and all 18 listed
dependency hashes. The reviewer confirmed that the least-closure result is
conditional on supplied well-formed typed records; the two footprints are not
asserted to be actual. The `bool <: int` chain requires shared C, complete
well-scoped clause transport and activation in both frames. The original
Simple-sub Record/Bool AST and the distinct Yulang Int/Unit fixture remain
separate. Direct owner inspection supports the bounded missing-output claim
for K_g, typed dependency edges, C/D source operands and scoped equality.

The review found no blocking, major, or minor correctness finding. It does not
establish actual C eligibility, a source-qualified contradiction, parser or
inference behavior, complete Call validity, replay, soundness, required
principality or parent-theorem closure.
