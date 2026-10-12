# Intrusion association: native construction and the missing owner law

Date: 2026-10-12
Status: frozen, unreviewed research characterization and conditional derivation;
original association/equality-preservation gate OPEN
Baseline: `0e621f549035537e4d3e799c78f79dd9385df350`
Branch: `research/simple-sub-intrusion`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`,
`/home/momota1029/rust/simple-sub-reference`
Lease: this file only; leaf, no delegation, semantic adoption or code authority

## 1. Frozen obligation and result

The parent A/B obligation ranges over supported natural source programs, their
original resolved bindings and lexical/type/event scopes, and actual retained
extrusion pairs `(alpha_copy, alpha_parent)` in their native inference histories.
It requires an association constructed by the actual source/type operations
between those **type occurrences** and semantic Value variables. For the
associated values `v_copy,v_parent`, the approved activation condition is

```text
SCC_G(v_copy) = SCC_G(v_parent),
```

where `G` has semantic Value vertices and actual approved source-reference
incidences. The required conclusion is that enforcing equality of the actual
extrusion-related type variables preserves source soundness, ordinary inference
and required principality, with the complete Call/effect/generalization contracts.
Activation must be decided before the proposed equality. No uniqueness of an
owner for a type variable, total assignment for Function ports, or transport law
for a copy is part of the frozen hypotheses.

Keep the source providers, complete operand tuples, guards, attachment and
residual lineage, witnesses, shared binders, independent incoming description
frames and original event telescopes. Do not infer Value edges from subtype
comparisons, bounds, Function ports, providers, levels or parent metadata. Type
copying does not inherit incidences or retarget resolved Names. Required source
inputs and original theorem quantifiers are not narrowed to the examples below.

**Result:** native Simple-sub determines the original type introductions,
sharing, polar copies, level guards, bound activation and freshening in the
examples. It does not supply the occurrence-to-Value owner/transport law needed
to evaluate the approved activation condition. The approved Yulang source and
Generalize rules do not supply that law either. Section 4 gives a smaller
discriminator than the existing two-function nested-call frontier: the same
actual native pairs and approved Value graph admit different activation answers
under explicit candidate completions of the missing law. Neither completion is
adopted or proved semantically adequate. There is no refutation or proof here of
the original equality-preservation theorem, which cannot yet be instantiated.

Claim classes:

- **Bounded static characterization:** the inspected source fields/operations
  and their absence of the required association output.
- **Native derivation:** the reduced reference term's actual generated pairs
  and completed bound replay, without a proposed intrusion step.
- **Conditional discriminator:** given either explicitly displayed candidate
  association completion, the fixed graph gives the displayed activation answer.
- **Open A/B claim:** source-qualified equality soundness, normal inference and
  required principality for the original source domain.

No executable probe, newly established universal theorem, certification or
production correspondence is claimed.

## 2. Authority and exact source boundaries

The governing documents, read at the pinned baseline, are:

| Source | Exact governing portion |
| --- | --- |
| [Parent-copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md) | Selected operation; Value-reference SCC clarification; Apply-result ownership; Nested Apply membership; Definition-root ownership; Retained boundary |
| [Value/type association](../design/2026-10-12-intrusion-value-type-association.md) | Entire document, especially Qualification and Reviewed source-construction frontier |
| [Copied-description ownership](../design/2026-10-12-value-reference-copied-row-ownership.md) | Decision; Scope and proof boundary |
| [Source Generalize](../design/2026-10-08-source-generalize-definition.md) | §§2–5, selecting [construction](2026-10-08-source-generalize-definition-and-proof.md) §§3–5 |
| [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md) | §§1–5 and Authority and integration |

The [cross-level derivation](2026-10-12-cross-level-odd-even-inference-derivation.md)
§§3–6 and [copy note](2026-10-12-odd-even-copy-qualification-proof.md) §3 supply
only their conditional native generation/replay facts. Their type-copy-vertex
nonqualification application is withdrawn and is not used here.

Original Simple-sub is inspected directly in `shared/src/main/scala/simplesub/`:

- `syntax.scala:7–14`: the reference source grammar has Literal, Name, Lambda,
  App, Record, Selection and Let; it has no Yulang effects or Branch constructor.
- `Typer.scala:48–55,59–83`: recursive registration, term typing and publication.
- `Typer.scala:88–159`: constraint caching, insertion before opposite-bound
  replay, level guards and one-sided polar extrusion.
- `Typer.scala:163–188,196–233`: fresh allocation, coherent two-sided
  freshening, scheme/monomorphic lookup, and actual Variable fields.

Parreaux's local paper `/home/momota1029/rust/simple-sub-reference-paper.pdf`,
§3.2.1, §3.5 and Figs.6–9, gives the same type construction and approximation
purpose. Its §5 restricts the soundness/principality proof sketches to the
non-let-polymorphic version. It contains no approved Yulang Value-reference
graph, retained-parent intrusion operation or occurrence-association law. The
paper's theorem sketches cannot establish the present let/Call/effect extension.

Source Generalize construction §3.3 introduces `Desc(C,q,sort,sigma,Delta)` and
typed provenance at the actual owning rule; §4 retains declarations and original
rule clauses; §5 preserves publication, component relation and scope. These
records distinguish a formal declaration from a body result and a source
component from an external monomorphic contract. They do not assign an additional
describing Value to every suboccurrence of a Function demand, or transport that
association through polar extrusion. In particular, the source validating
component `C` must not be inferred from a Value SCC.

## 3. What the original constructors establish

The original algorithm's context maps a resolved Name to a TypeScheme. Lambda
allocates the formal's type variable and places it in that context. Monomorphic
lookup returns exactly that SimpleType; published lookup uses one coherent
freshening map. App returns a fresh result type and generates the full native
two-port demand `callee_type <: Function(argument_type,result_type)`.

These facts give source origins for type introductions and a relation between
terms and returned types. They do not give a unique inverse map from a type
coordinate to a semantic Value. Nor do they say which occurrence of a reused
coordinate is associated with the enclosing definition's Value when constructing
a copied demand. The actual `Variable` fields are level, lower/upper bounds and
internal identity; the extrusion memo key is `(Variable,polarity)`. There is no
source occurrence, semantic Value identity, describing-root identity or Value
association certificate in this representation. Pure recursive-let registration
also supplies no separate Variable for every nonrecursive definition root.

### 3.1 `id x = x`

For a nonrecursive boundary-0 definition, `typeLetRhs` infers its RHS at level 1.
Lambda creates `A` for the formal x; Name x returns that same A; the formed type
is `Function(A,A)`, published as `PolymorphicType(0,Function(A,A))`. A later Name
use coherently maps both occurrences to the same fresh A_i. There is no extrusion
pair in this bare derivation. If id is syntactically recursive, it additionally
has a recursive placeholder and the ordinary formed-type lower check, with no
level violation in this example.

Thus the parameter declaration, argument port, body Name type and result port
share one coordinate. The native source rule explains the actual returned
provider (the same formal) and the description correlation. It does not justify
replacing every occurrence's association by the enclosing id Value, nor prove
that each structural occurrence requires a different semantic Value. A source
occurrence law may distinguish the formal origin from its occurrence inside the
complete callable description; that additional law is exactly what must be
provided rather than guessed.

### 3.2 `konst x = 0`

Lambda introduces A for x and `Lit(0)` returns the shared primitive `IntType`, so
the type is `Function(A,IntType)`. The bare definition creates neither a fresh
result variable nor an extrusion pair. On `konst 1`, App creates R and compares
`Function(A_i,IntType) <: Function(IntType,R)`: it generates `IntType <: A_i`
and `IntType <: R`, with native opposite-side replay if applicable.

The approved Value incidence is `R_value → K`, for the resolved konst binder K.
It holds although the returned provider is literal 0. Accordingly a provider
analysis cannot replace source-result ownership. The shared primitive IntType
also cannot select a unique semantic literal Value by its type identity.

### 3.3 A nested App, `f(0)(0)`

The first App allocates R1 and generates `type(f) <: Function(IntType,R1)`.
The second allocates R2 and generates `R1 <: Function(IntType,R2)`. At one
level this ordinary demand need not extrude; no parent pair is invented merely
because R1 occurs as a callee. Existing bounds activate native consumers in the
usual way.

The approved recursive Apply-fragment membership gives `R1_value → F` and
`R2_value → F` from the same resolved Name f. It supplies no containment edge
`R2_value → R1_value`. Native demand occurrence, source result Value, returned
callable/provider and enclosing definition root are therefore distinct possible
construction facts. Sharing R1 between two native demands does not itself choose
an owner for a later copy of its type occurrence.

## 4. A reduced source discriminator with actual polar pairs

Use this exact original-reference AST term:

```text
let rec f =
  let g = lambda y. f y
  in g
in f
```

This removes unused recursion on g, the outer lambda/formal and the outer App
from the frontier's `lambda x ... in g x` term. It retains one nested let, one
Lambda and one App: the necessary structures in this exhibited witness for a
level crossing, a demand with wrong-level variables, and two definition roots
with references in both directions. No global syntax-minimality theorem is
claimed. The original reference grammar accepts this recursive-let RHS shape;
this is not an assertion that the current Yulang frontend admits its exact
spelling, nor a translation of complete Yulang Call into the two-port App.

Freeze separate semantic source values F (definition f), G (definition g), Y
(formal y) and V_R (inner App result); separate type coordinates o,B,R,C,D; and
the original let/type scopes. F and G are source definition owners, not names
invented for arbitrary Scala type rows.

### 4.1 Native derivation without intrusion

Start with the ordinary reference environment; none of the free builtins occurs
in this term. The following is a direct finite execution derivation of the
cited rules, not an execution command:

1. `typeLetRhs(true,f,...)` allocates o at level 1 and infers the RHS under
   `f ↦ o` at level 1 (`Typer.scala:48–55`). The inner nonrecursive g RHS is
   inferred at level 2. Lambda allocates B at level 2.
2. Inner lookup f returns o monomorphically; lookup y returns B. The App
   allocates R at level 2 and generates `o <: Function(B,R)` (`:62–72,207`).
   At this cut o,B,R have empty bound lists.
3. The direct insertion guard fails: `level(Function(B,R))=2 > level(o)=1`.
   Negative extrusion to level 1 traverses the Function, flipping argument
   polarity. One memo creates actual C for `(B,+)` and D for `(R,-)`:

   ```text
   U(B) = [C]; L(C) = [];
   L(R) = [D]; U(D) = [];
   U(o) = [Function(C,D)]; L(o) = [].
   ```

   The actual creation provenance is `(C,B,+,1)` and `(D,R,-,1)`
   (`:115–126,134–156`). Original Simple-sub does not store the parent pair;
   these are its exact copy/parent identities at creation. Yulang's selected
   extension requires retaining them. No source incidence is created here.
4. Publish g at boundary 1 as `PolymorphicType(1,Function(B,R))`. The `in g`
   Name coherently freshens B/R to B'/R' at level 1, retaining C/D. It returns
   `Function(B',R')`, with `U(B')=[C]` and `L(R')=[D]`
   (`:81–83,166–188,201–202`). Freshening creates no extrusion parent pair.
5. Outer recursive completion checks `Function(B',R') <: o`. Insertion into
   `L(o)` replays the existing `Function(C,D)` upper demand, generating
   `C <: B'` and `R' <: D` (`:52,106–108,118–120`). The first adds B' to
   `U(C)`. The second adds D to `U(R')`, replays `L(R')=[D]`, and reaches
   `D <: D`, which terminates by existing identity (`:93,115–117`). All
   variables in these replayed constraints have level 1; no further extrusion
   occurs. The result is published as `PolymorphicType(0,o)`.

The comparisons do not merge C/B or D/R. The immediate post-copy cut and the
later completed replay are distinguished; storage is not substituted for
activation. The derivation has no primitive/Branch uncertainty, and introduces
no arbitrary future client constraint.

### 4.2 The fixed Value graph and two conditional completions

Apply the approved source rules, without deriving any edge from that store:

```text
F → G                    f's own final Name g
G → F, G → Y             g's initializer Names f and y
V_R → F, V_R → Y         inner Apply's callee/argument Names
```

The nested initializer's references belong to G, not F. In the graph generated
by these specified source rules, `{F,G}` is one SCC, Y is a singleton with no
outgoing edge, and V_R is outside the root SCC. No edge targets a type copy and
no copied type coordinate is required to be a graph vertex.

Hold a **candidate** copy-occurrence association to F fixed in both completions.
It is stipulated to isolate the parent-occurrence ambiguity; it is not inferred
from storage on o and is itself an unestablished part of the missing law:

| Actual pair | Candidate immediate operand/result association `(copy,parent)` | Candidate enclosing-description occurrence association `(copy,parent)` |
| --- | --- | --- |
| `(C,B)` | `(F,Y)` | `(F,G)` |
| `(D,R)` | `(F,V_R)` | `(F,G)` |

The first completion does not qualify these pairs in the displayed graph. The
second qualifies both and requests actual equalities C=B and D=R. Both use the
same original source references, original native constraints, distinct source
values, levels and retained pairs. Neither copies incidences or changes their
resolved targets. Every expressly approved condition on copying and graph
formation remains identical; the difference is wholly in the unspecified
association of type occurrences. These are logical completions of the missing
local data on this witness, not full algorithms proved to preserve ordinary
source behavior. A candidate returning the same associated Value for both
occurrences would also qualify reflexively; the clarification permits that
criterion but does not select that transport rule.

The discriminator therefore establishes **underdetermination by the cited
construction/authority**, rather than failure of the selected SCC criterion or
a source-qualified unsound equality. The more familiar frontier term with
outer `lambda x` and final `g x` has the same initial pairs and root SCC; it
does not remove this missing rule. The reduced witness is sufficient to expose
it before arithmetic, effects or a complex provider analysis is introduced.

## 5. The unchanged `odd`/`even` example

Keep the original text and distinct binders O=odd, E=even, a=outer n, b=inner n:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

The approved root rules force O→E and E→O across levels, independently of the
typing of minus, test and Branch. Conditional on faithful local argument
inference yielding T at level at most 2, the inner recursive Name is the
monomorphic outer o at level 1. Fresh level-2 result R forces negative
extrusion in `o <: Function(T,R)`, giving `(D,R,-,1)` in the same polar memo
used for T. Wrong-level argument copies belong to the actual variables in T;
there is no generally forced `(C,B)` where B types the formal b.

Immediate operand/result and enclosing-description associations remain
different on that same D/R creation. The root O/E SCC supplies no answer about
the result Value versus E as the parent type occurrence's association or O as
the copy's association. Original Simple-sub and Source Generalize preserve
the scopes and monomorphic root, but do not choose these owners. Missing
minus/Branch/complete-Call laws and frontend admission are additional existing
boundaries; they are not used to discard this source or evade the association
obligation. The reduced term in §4 isolates the association gap independently
of those boundaries.

## 6. Actual implementation bridge and exact obstruction

At the pinned Rust baseline:

| Producer/consumer | Retained fact; missing bridge |
| --- | --- |
| `candidate_source.rs:254–307,375–411` | Source levels, active local root lookup, Apply source operands/result and `owner` definition ID. An owner field is source provenance, not a selected association for every port/suboccurrence. |
| `candidate_call.rs:91–143` | Complete original Gen-Call-0 inputs remain explicit requirements; scalar checking provenance and native negative Function do not constitute original typing. |
| `shadow_apply.rs:1335–1385` | Four-port native demand and separate callee, argument, invocation/application effect coordinates. No occurrence-to-semantic-Value association is produced at this seam. |
| `candidate_extrusion.rs:82–163` | Copy allocation, typed parent retention and selected bound traversal, memoized by endpoint/polarity/target. It supplies no source/Value association for the new type occurrence or its parent occurrence. |
| `candidate_intrusion.rs:23–28,171–220` | `Parent {copy,parent,polarity,target}` contains solver RowKeys, not the two associated semantic Values or their source occurrence evidence. |
| `candidate_intrusion.rs:358–488` | The consumer constructs adjacency from Value/Effect bounds and Function/effect ports, then compares components of solver parent/copy endpoints directly. It does not consume the corrected semantic Value graph/association criterion. |

This is a direct field and call-path inspection, not an inference that an
uncited emitter does not exist anywhere in the repository. It suffices to show
that the actual inspected owning producer-to-consumer path cannot supply the
required bridge. Production remains frozen; reversing bound edges, adding
copy vertices or treating `owner` as the selected semantic rule would introduce
unsupported meaning.

**Precise missing premise:** the App/source-description constructor must specify
which semantic Value is associated with each relevant type occurrence, and the
extrusion constructor must specify the association evidence transported or
created for an actual parent/copy pair, including repeated/shared occurrences
and polarity memo reuse. The source law must decide the §4 table, including its
stipulated copy-to-F premise; no currently cited law does. Association is not
incidence inheritance. Once the association is chosen, its complete scope and
fresh-use transport must be established without turning independent description
frames into new runtime objects or altering original Name targets.

Proof-obligation-economy audit: this is a required A/B activation and equality
premise. Recovering occurrence owners afterward from solver bounds or IDs would
be D reconstruction debt. The original construction retains enough ordinary
source origins to name the gap, but it never established the missing semantic
association choice. A retained certificate can preserve a source-selected rule
after that rule exists; retaining guessed owners now would smuggle in the
unproved premise. The two earlier source/bound-graph routes do not justify a
third equivalent SCC proof. Stop at this exact constructor frontier.

One next decisive action: the primary obtains/adjudicates the App-demand and
extrusion association law on the §4 actual pairs, preserving the approved graph
and source scopes; then assigns its construction/transport bridge and the
original qualified-equality proof. Independent review of this obstruction may
proceed now. Soundness, required principality, ordinary progress, termination,
complete Call, hygiene and F5 replacement remain OPEN.

## 7. Static checks, dependencies and submission

Checks: bounded `cat`, `rg`, `sed`/`nl`, local `pdftotext -layout ... -`, read-only
`git rev-parse`, `git show`, `git diff <baseline> -- <exact inputs>`,
`git status --short -- <lease>`, and SHA-256 reads. The inspected design,
construction and Rust direct inputs had no diff against the pinned baseline.
No tests, builds, probes, Oracle execution, compiler writes, child launches,
Git mutation or external contacts. The delegating primary is the verification
and integration owner. Two read-only command processes were briefly requested
in parallel during initial rule/skill reads, exceeding the packet's one-process
read budget; all subsequent reads were sequential. No heavy process ran.
CPU/RAM and exact elapsed reasoning time were not measured; this is one bounded
pass within the 45-minute cap.

Requested route: normal `gpt-6.1-sol/high` prover leaf. Project role registration
is present; `prover.toml` leaves model/effort unpinned and project subagent defaults
are Sol/high. Observed effective runtime model/effort metadata: **unknown**.
No Astra, model switch or hot reload is claimed.

Direct SHA-256 snapshot:

| Dependency | SHA-256 |
| --- | --- |
| parent-copy operation | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| association clarification | `a5c69e3bf7661e5212abfd38ae4c757f2e9a02cb7ed1409bb2c2bf40bafae1d3` |
| copied-description ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| source Generalize design | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| cross-level derivation | `839e80f5c1426531bb761d9ae6ef9475d8f89104e766a5973c356656f89ae41c` |
| earlier copy note | `efffb130ce708d6cbe89a42a0b482d62c9dd93dceedb345fd084ad6370cc3bae` |
| candidate_source.rs | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| candidate_extrusion.rs | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_intrusion.rs | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| candidate_call.rs | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| shadow_apply.rs | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference syntax.scala | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| reference paper | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

## Commit packet

- Exact leased/changed path:
  `notes/theory/2026-10-12-intrusion-association-proof.md`.
- Baseline: `0e621f549035537e4d3e799c78f79dd9385df350`; reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none caused by this leaf; snapshot above. The
  primary must revalidate any later concurrent dependency changes.
- Review status: unreviewed research characterization/conditional discriminator;
  no parent closure, self-certification or semantic adoption. Writes stop on
  submission before independent review.
- Checks already run: static source/paper reads, scoped baseline-diff comparison,
  dependency hashes and narrow artifact inspection. Runtime verification omitted
  by packet. No Git mutation.
- Proposed checkpoint: `research: isolate native intrusion association owner gap`.
- Shared-record deltas left for primary/curator: retain the parent association
  and equality A/B gates OPEN; record the smaller native source discriminator,
  actual C/B and D/R creation/replay and missing App/extrusion owner law; keep
  frontend, complete Call/effects, source Generalize, implementation/cutover
  obligations separate. No task/index/theory-status/question files were edited.
