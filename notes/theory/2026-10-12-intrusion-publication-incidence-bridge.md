# Intrusion publication incidence: native-to-publication adequacy gap

Date: 2026-10-12
Status: reviewed bounded source-correspondence audit; source-to-publication bridge OPEN; original parent A/B theorem OPEN
Baseline supplied: `e5e7b5878`, branch `research/simple-sub-intrusion`
Producer: prover-equivalent generic fallback, leaf only
Exclusive lease: this file
Authority: existing selected source Generalize and occurrence qualification only
Budget: one bounded reasoning attempt, at most 30 minutes; no executable inference
Correction review: `compiler_referee` and `spec_auditor` confirm that separate
C-term formation is not a qualification premise; `compiler_referee` PASS on
the corrected falsifier and shared-record handoff, 2026-10-12

## 1. Original claim and result

The original A/B claim quantifies over **all admitted source programs and
lawful uses in the original supported Yulang envelope**. Original scopes,
recursive sharing, complete Call, effects, lawful publication and use,
soundness, required principality and normal progress are preserved. Every
actual extrusion event retains its origin Value, receiving Value and actual
signed parent/copy pairs. When its Values share the approved Value-reference
SCC, equality is imposed on those pairs. The required conclusion is source
soundness and preservation of the required principal coverage and ordinary
formerly lawful inference, subject to the selected resource envelope. It is
not preservation of every arbitrary pre-intrusion solver assignment.

This packet tests the decisive nested source incidence from the frozen
[occurrence proof](2026-10-12-extrusion-occurrence-intrusion-proof.md), §§1–8.
It neither proves nor refutes the parent claim. Its original attempt asked
for a source declaration or endpoint term for C. Independent review found
that requirement too strong: approved intrusion qualification needs the
actual event, Value endpoints and native parent/copy pairs, not a separate
source term, binder or `Desc` for C. The result below is a bounded audit of
the missing **native-constraint-generation to complete-source-publication
correspondence**. It does not establish that correspondence, nor does it
prove the fixed-anchor rejection for admitted Yulang source.

The parent A/B theorem remains open. No classification, schedule, source
restriction or implementation decision is adopted.

## 2. Frozen sources and source instance

The governing definitions are:

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–5.
- [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md), §§2–3, selecting [construction](2026-10-08-source-generalize-definition-and-proof.md) §§3–5.
- [Parent/copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md), including separate definition-root reference ownership.
- [Extrusion occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), retaining origin/receiver Values and actual polar pairs.
- The frozen occurrence proof §§3–5 supplies the native derivation and its conditional rejection/allocation consequences.

Use exactly the frozen original-Simple-sub source:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

The original reference provides `succ:int->int`, `true:bool`, and the actual
Let/Lambda/App/Record constructors. Its successful native inference and the
fixed-anchor rejection path are established in the frozen dependency. This
note does not assert that the same whole source is admitted by Yulang's
private carrier. In particular, inspected `LocalSourceForm` includes neither
Record nor a Bool literal. Source Generalize has a Record schema, but its
local laws and actual Yulang admission are distinct inputs. No int/Function
variant is substituted for this witness.

Keep three domains distinct. `F,G` are source Value roots; `B,C,R,D` are native
type coordinates; `K` below is a **validating source component**, supplied by
recursive-group/definition registration. `K` is not defined to be the Value
SCC and is not a numeric inference level.

## 3. Actual construction prefix and the first absent incidence

At the original `f y` demand, the native reference constructs

```text
o <: Function(B,R)
C = extrude(B,+,1)        D = extrude(R,-,1)
B <: C                   D <: R
o <: Function(C,D).
```

The approved normative occurrence is `e:(G,F)` with actual pairs `(C,B,+,1)`
and `(D,R,-,1)`. Definition-root references give `F -> G -> F`, so e qualifies
and adds `C=B` and `D=R`. This activation decision is an input already
selected by the user. It supplies no source-component or Generalize
classification.

The owning-rule audit gives this exact partial incidence derivation:

| Coordinate or edge | Actual owner and output | Selected source incidence obtained |
| --- | --- | --- |
| B | Native Lambda parameter `y`, reference `Typer.scala:64–67`; Yulang Parameter schema, construction §3.1 | Its source introduction is `q_y`; if the source derivation is supplied, Parameter emits `Desc(K_g,q_y,Value,sigma_y,Delta_y)`. `sigma_y` precedes g's challenge. The actual `K_g` and its registration remain required. |
| C | Native `extrude`, `Typer.scala:143–156`, calls `freshVar` at target level 1 and emits the positive parent/copy bound | C is a native solver coordinate and the approved event associates this actual copy with receiver F for qualification. No separate source declaration, endpoint term or `Desc` is required. What remains unproved is how the native demand/bound occurrence is represented in the complete source clause relation passed to publication, with lawful dependencies. |
| R,D | Native App result and negative extrusion copy | Their numeric generation is known. Complete Yulang Call distinguishes body and invocation ports; the native two-port derivation does not by itself prove the source-to-complete-Call translation or its dependency incidence. |
| `C=B`, `D=R` | Approved occurrence-qualified intrusion | Actual solver operands and activation are selected. The missing bridge is to show that these same generated constraints/equalities occur in the complete source relation and are retained through publication/use allocation. |
| F/G references | Definition-root source ownership | Value-graph SCC qualification only. No equality with `K_g` or validation tuple is emitted by this rule. |

This table deliberately does not identify every type coordinate with a fresh
`Desc` declaration. Native C can be carried as an internal endpoint in the
generated constraint relation and, after the approved equality, may be
represented through its B alias. The proof obligation is to establish how
the actual App/extrusion generation and event record enter the complete
source program and its scopes. No separate source endpoint term is a
prerequisite.

The current compiler seam confirms the missing producer input:

- `candidate_extrusion.rs::candidate_extrude` accepts endpoint, polarity and
  target level. In its row-copy case it calls `fresh_value_at_level` or
  `fresh_effect_at_level`, retains parent/polarity/target, memoizes the copy
  and inserts a bound. These outputs identify native copies. They supply
  neither `Desc(K,q,sort,sigma,Delta)` nor `Established`/`Internal` typed
  source-field provenance for C.
- `candidate_source.rs` installs active parameterized initializers before
  traversal, routes recursive local Names through `Action::Link`, and later
  installs local schemes. Its actual `ApplySourceInput.owner` is the enclosing
  definition root. Neither that owner nor its numeric `component_levels`
  establishes the selected source component K or C's original scope.
- `candidate_scheme.rs::install_candidate_local_term` stores
  `LocalScheme { id, root, boundary }`; local Name routing captures its live
  graph at that boundary. Capture classifies rows using level and existing
  non-generic metadata. This is a concrete private solver mechanism, not the
  selected typed fixed-dependency walk of source Generalize.

These are direct interface/constructor observations. They do not claim that
the native copy lacks a semantic association: the approved event record
provides its qualification. They show that candidate extrusion metadata is
not itself a proof that the generated constraint graph is faithfully
embedded in the complete source publication relation.

## 4. Exact failed declaration/frame derivation

Let `N_e` be the actual native Call-demand/extrusion graph for occurrence e,
including its coordinates, signed parent/copy bounds, memoized images and
approved event record. Let `S_g` be the complete source clause program
consumed when g is published. The missing correspondence must relate `N_e`
and its qualified quotient to `S_g` at their actual scopes. This is a proof
relation between generated constraints and the complete source program; it
does not require a separate source term for each coordinate.

Attempt the prescribed construction in its actual dependency order:

1. The native source derivation constructs `N_e`, and approved Value SCC
   qualification adds its selected equalities. This part requires no new C
   declaration.
2. The complete source Call constructor must represent the same call demand,
   its original carrier/receiver/result/effect/future interfaces, and the
   native constraint graph (or a proved equivalent quotient) in `S_g`. The
   selected Code-Call construction records complete interfaces and checking
   origins; those origins are not semantic inclusion truth and do not
   currently state this native-to-source translation.
3. Source Generalize §4 Build can retain actual local source clauses and
   their owning dependency records. It cannot import every native solver
   bound merely because it exists in the candidate/native graph. The missing
   premise is that actual App/extrusion generation supplies the matching
   complete source clause and scope incidences.
4. Given that premise, §5.1's registered-component walk and §5.2's
   `new(p_g,i,g)` allocation must preserve the same relation through two
   independent whole frames. Their rules preserve the actual source input;
   they do not prove the missing generation-to-source correspondence.

This stops the construction before a valid scheme input exists; it is not
a derived rejection of g's publication. The remaining consumer obligations
are located exactly, rather than assumed:

| Consumer | Consequence of its selected rule | Missing event input |
| --- | --- | --- |
| Publication `p_g` | Retain every original local conjunct and the complete K relation, including constraints to fixed fields | The source-to-generated-constraint correspondence for `N_e` and its scoped equality incidence in `S_g` |
| Two independent published Names of g | Distinct `new` events open complete frames, not marginal g-only fragments | Whether the retained native equality and dependencies route to one shared base relation or frame-local coordinates under the original source allocation |
| Alias of either use | Same handle routes to the same complete frame and binders | No alternate incidence can be created by Alias |
| Recursive reference inside either frame | Same validation tuple and complete simultaneous relation | Actual registration of f relative to g's K; no per-reference `new` |
| Record/join of the two uses | One shared context; base fields and Shared witnesses are literally common | Actual equality incidences for both frames |
| Final f publication/use | Retain final formed root and all original relations at their source scopes | Does not reconstruct the missing original e incidence or silently replace earlier use handles |

Thus the desired use-frame equations do not follow merely from the existence
of Source Generalize. Its allocation theorem is total on its well-formed,
source-produced input; it is not itself the proof that native extrusion
constraints and event-qualified equalities occur in that input.

## 5. Counterexample attempt and exact residual premise

The attempted real source counterexample uses the already established native
use path, without introducing handwritten clients:

```text
first actual use:   int <: B0 <: S0 <: V0 <: int
second actual use:  bool <: B1
```

If the complete source construction proves that the qualified native equality
is represented across both independent use frames and its quotient routes the
copy-side C through one shared base incidence while parent-side B is an
independent template in each frame, the frozen allocation lemma yields
`B0=C_base=B1`; the source path requires `bool <: int` and native inference
rejects. If B is fixed as well,
the same shared-incidence rejection follows under those established operands.
This consumes the frozen result as a precise conditional falsifier. It does
not establish those premises for this Yulang source.

Neither of the following is a derivation of the missing premise:

- `C.level=1`: the source fixed walk follows typed contract dependencies,
  not levels.
- `F,G` in one Value SCC: this activates the native equality, but does not
  establish its complete source-publication incidence or register source
  component K for Generalize.

Nor is preservation established by assuming both rows can be independently
freshened, retaining only g's marginal root, delaying equality past its uses,
or reclassifying f's still-live root as an environmental scheme. Each changes
an unestablished construction/transport fact and would need its actual owning
law while preserving the complete recursive relation.

The single reduced correspondence obligation is:

> **Native generation to complete source publication.** At the owning App/
> Call-demand/extrusion constructor for e, show that the actual native demand,
> signed parent/copy constraints and event-qualified equality are represented
> in the complete source clause program consumed at g publication, with the
> original complete interfaces, scopes, recursive registration and dependency
> incidences. Show that the existing whole-relation allocation transports
> this same relation into lawful independent use frames. C is a native
> coordinate; no distinct source term or `Desc` is required solely for C.

This premise names the evidence needed to connect the already selected
operation to source soundness/principality. It does not prescribe a new
semantic rule, force C to be fixed/template, choose the SCC schedule, or
authorize code. The owning producer is App/Call-demand plus extrusion's
generation correspondence, with recursive registration providing K;
Generalize consumes the resulting complete source program. Adding an event ID
alone does not discharge the premise.

The parent A/B gate remains OPEN under the primary's existing ownership.
The absence of this correspondence proof is not a counterexample to the
approved operation and not proof that no adequate translation exists. This
packet identifies the first unresolved construction/adequacy step; it does
not close or reclassify the original obligation.

One next action: prove the exact App/extrusion-to-complete-Call clause
correspondence above, first using the approved equality quotient `C ↦ B` and
preserving complete interfaces and original scopes. Then apply the existing
Generalize allocation to independent uses. The fixed-anchor source rejection
falsifier remains conditional until this construction and actual source
admission are established.

## 6. Verification, runtime and commit packet

Verification was direct rule/constructor reading and a hand derivation of
the partial source incidence and failed Build/allocation inference. Bounded
`rg`, `sed`, `cat`, and SHA-256 reads were used; some early large captures
truncated, and all decisive source sections were reread in bounded captures.
Two initially guessed source-note/module paths were absent; neither was used
as evidence. No tests, builds, parser runs, Oracle runs, executable inference
or performance experiments, Git operations or delegation occurred. At most
one lightweight shell read process ran at once; zero heavy processes and zero
inference/measurement samples. CPU/RSS and exact reasoning wall time were
not instrumented; this bounded attempt stayed within its 30-minute cap.

Requested role/settings: generic proof leaf, `gpt-6.1-sol/high`.
Observed assignment identity: `/root/intrusion_publication_bridge_fallback`;
effective model/effort metadata: **unknown**. No custom prover execution or
Astra escalation is claimed. Fresh independent reviewers established the
qualification/publication distinction and found no overlooked source rule;
the corrected record passed delta review. No parent theorem closure is
claimed. The
`yulang-proofs` skill and `.codex/agents/prover.toml` contract were applied
under the explicit generic fallback/no-delegation packet.

Unverified: whole-source Yulang admission, native-generation to complete
source Call/effect correspondence, recursive registration, all equality
scheduling and existing-frame transport paths, public principal coverage,
normal progress, termination and production/F5 cutover. No dependency was edited.

Direct dependency SHA-256 snapshot:

```text
08b963a7e2356a400dcb05b53c6fe6d3a917abe9e0df1582779c5c83858eb4f8 notes/theory/2026-10-12-extrusion-occurrence-intrusion-proof.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903 notes/design/2026-10-08-native-recursive-interface-definition.md
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Commit packet for the primary:

- Exact changed lease: `notes/theory/2026-10-12-intrusion-publication-incidence-bridge.md` only.
- Baseline: supplied `e5e7b5878`; branch/ref/blob comparison remains primary-owned.
- Claim/review: reviewed bounded native-generation/source-publication gap; original parent A/B OPEN; no theorem promotion.
- Checks: direct reads, hand incidence derivation, dependency hashes and leased-note whitespace inspection; no executable verification.
- Proposed checkpoint message: `research: record native Call publication gap`.
- Shared-record delta: record the missing native-generation to complete-source-clause correspondence, including its original scopes and independent-frame transport; preserve the fixed-anchor result as conditional and retain the unchanged parent scope. Primary owns tasks/progress/theory-map synchronization.

Writes stop at handoff; artifact hashing is reported separately.
