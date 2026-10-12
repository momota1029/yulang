# Intrusion publication incidence: exact source-construction obstruction

Date: 2026-10-12
Status: unreviewed bounded source bridge; original parent A/B theorem OPEN
Baseline supplied: `e5e7b5878`, branch `research/simple-sub-intrusion`
Producer: prover-equivalent generic fallback, leaf only
Exclusive lease: this file
Authority: existing selected source Generalize and occurrence qualification only
Budget: one bounded reasoning attempt, at most 30 minutes; no executable inference

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
It neither proves nor refutes the parent claim. The first missing premise is
the **source realization of the actual extrusion copy C**, including its
declaration/term incidence and typed dependency edges. The selected source
Generalize rules consume that premise but do not produce it. Consequently,
they do not force `rho_i(B)=rho_i(C)=C_base` for this actual event, and they
do not establish a lawful mechanism avoiding that equation either.

This is an owning-constructor obstruction, not a new conditional preservation
theorem. Work stops at this missing premise. No classification, schedule,
source restriction or implementation decision is adopted.

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
| C | Native `extrude`, `Typer.scala:143–156`, calls `freshVar` at target level 1 and emits the positive parent/copy bound | No selected source rule identifies C with a source declaration, existing typed field or endpoint term. No source provenance or dependency telescope follows from this allocation. |
| R,D | Native App result and negative extrusion copy | Their numeric generation is known. Complete Yulang Call distinguishes body and invocation ports; the native two-port spelling cannot establish their source port/declaration realization. |
| `C=B`, `D=R` | Approved occurrence-qualified intrusion | Actual solver operands and activation are selected. Their incidence as original source local clauses, including scope and publication history, requires the same missing realization. |
| F/G references | Definition-root source ownership | Value-graph SCC qualification only. No equality with `K_g` or validation tuple is emitted by this rule. |

This table deliberately does not identify every type coordinate with a fresh
Desc declaration. C might represent an existing source field or a derived
endpoint term. That possibility requires its real constructor law and is
not excluded. The obstruction is the absence of **any established lawful
realization** of C, rather than a requirement to invent a new source binder.

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
searching all other compiler files could never find related metadata, or
that a source realization cannot be constructed. The selected governing
source clauses themselves contain no extrusion realization law.

## 4. Exact failed declaration/frame derivation

Write `chi_e(t)` for the source declaration, field or well-scoped endpoint
term realized by an actual coordinate t of e. This is notation for the
required correspondence evidence, not a newly adopted semantic relation.
If its operands existed, the qualified equality would be the source clause

```text
E_e = [chi_e(C) = chi_e(B)] and [chi_e(D) = chi_e(R)].
```

Attempt the prescribed construction in its actual dependency order:

1. Construction §3.3 gives Parameter's declaration at `q_y`, conditional on
   the actual source derivation and registration. It does not classify a
   later solver row from level or provider identity.
2. Construction §4 `Build` allocates one symbolic declaration per **actual
   inference introduction**, and generates each original local clause with
   its original operands and typed records. Its clause generation needs the
   source owner of `chi_e(C)`. The occurrence decision names the solver pair
   but supplies no such source introduction/field law. Therefore E_e's
   source operands cannot yet be formed by the selected Build rules.
3. Construction §5.1 seeds the complete registered K relation and follows
   actual Established/OneShot dependencies in fix mode and same-K Internal
   dependencies in retain mode. It cannot run this decision for C from its
   native level or from `SCC(F)=SCC(G)`. Even a known raw F provider is
   insufficient: an Internal description edge and an Established full
   contract have different behavior under this exact walk.
4. Construction §5.2 `new(p_g,i,g)` allocates the already classified entire
   K relation. It gives eligible declarations frame keys and routes fixed
   fields to base incidences. Allocation supplies no rule that repairs the
   absent source operands/classification. There is thus no actual derived
   `rho_i(C)` for this event in the premises presently available.

This stops the construction before a valid scheme input exists; it is not
a derived rejection of g's publication. The remaining consumer obligations
are located exactly, rather than assumed:

| Consumer | Consequence of its selected rule | Missing event input |
| --- | --- | --- |
| Publication `p_g` | Retain every original local conjunct and the complete K relation, including constraints to fixed fields | Well-formed E_e operands and their owning component/scopes; if equality is discovered later, its faithful source publication incidence |
| Two independent published Names of g | Distinct `new` events open complete frames, not marginal g-only fragments | Whether C refers to a shared base field, an eligible frame declaration or a legally derived term |
| Alias of either use | Same handle routes to the same complete frame and binders | No alternate incidence can be created by Alias |
| Recursive reference inside either frame | Same validation tuple and complete simultaneous relation | Actual registration of f relative to g's K; no per-reference `new` |
| Record/join of the two uses | One shared context; base fields and Shared witnesses are literally common | Actual equality incidences for both frames |
| Final f publication/use | Retain final formed root and all original relations at their source scopes | Does not reconstruct the missing original e incidence or silently replace earlier use handles |

Thus the desired equation does not follow merely from the existence of
Source Generalize. Its allocation theorem is total on its **well-formed,
source-produced input**, not a constructor for missing extrusion provenance.

## 5. Counterexample attempt and exact residual premise

The attempted real source counterexample uses the already established native
use path, without introducing handwritten clients:

```text
first actual use:   int <: B0 <: S0 <: V0 <: int
second actual use:  bool <: B1
```

If source construction proves that the retained equality is present at both
uses and `chi_e(C)` is a shared fixed field while B is eligible, the frozen
allocation lemma yields `B0=C_base=B1`; the source path requires
`bool <: int` and native inference rejects. If B is fixed as well, the same
shared-incidence rejection follows under those established operands. This
consumes the frozen result as a precise conditional falsifier. It does not
establish those premises for this Yulang source.

Neither of the following is a derivation of the missing premise:

- `C.level=1`: the source fixed walk follows typed contract dependencies,
  not levels.
- `F,G` in one Value SCC: this activates E_e, but does not register source
  component K, classify C or select its allocation scope.

Nor is preservation established by assuming both rows can be independently
freshened, retaining only g's marginal root, delaying equality past its uses,
or reclassifying f's still-live root as an environmental scheme. Each changes
an unestablished construction/transport fact and would need its actual owning
law while preserving the complete recursive relation.

The single reduced producer premise is:

> **Source realization of the extrusion occurrence.** At the owning complete
> Call/demand construction of e, establish the lawful source declaration,
> field or endpoint-term realization of each actual signed pair, beginning
> with C and B; retain its actual validating registration, original telescope
> and typed Internal/Established/Description dependencies through publication
> and existing/new use incidences. Show that the active equality has those
> same operands on the complete source relation.

This premise names evidence needed to apply existing rules. It does not
prescribe a new semantic rule, force C to be fixed/template, choose the SCC
schedule, or authorize code. The owning producer is Call/demand plus
extrusion's source bridge, with recursive registration providing K;
Generalize consumes the resulting typed incidence. Adding an event ID alone
does not discharge the premise.

The parent A/B gate remains OPEN under the primary's existing ownership.
The absence of a source realization is not a counterexample to the approved
operation and not proof that a lawful realization exists. This packet adds
the exact first failing construction step to the previous conditional result;
it does not close or reclassify the original obligation.

One next action: the primary should route this exact missing source
construction to the existing design/authority path, before another proof
attempt or a large dependent implementation slice. A lawful owner-supplied
realization permits the fixed-walk/use derivation to resume; evidence of an
admitted actual fixed-base realization would immediately activate the frozen
source rejection falsifier. The exact source admission and complete Call
premises remain separately required for an actual Yulang refutation.

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
effective model/effort metadata: **unknown**. No custom prover execution,
Astra escalation, independent review or closure is claimed. The
`yulang-proofs` skill and `.codex/agents/prover.toml` contract were applied
under the explicit generic fallback/no-delegation packet.

Unverified: whole-source Yulang admission, complete source Call and effects,
actual source realization/registration of e's pairs, all equality scheduling
and existing-frame transport paths, public principal coverage, normal
progress, termination and production/F5 cutover. No dependency was edited.

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
- Claim/review: unreviewed source-construction obstruction; original parent A/B OPEN; no theorem promotion.
- Checks: direct reads, hand incidence derivation, dependency hashes and leased-note whitespace inspection; no executable verification.
- Proposed checkpoint message: `research: locate extrusion copy source incidence obstruction`.
- Shared-record delta: record the missing C realization at Build's owning input, with Call/demand/extrusion and registration as producers; preserve the existing native fixed-anchor refutation and unchanged parent scope. Primary owns tasks/progress/theory-map synchronization.

Writes stop at handoff; artifact hashing is reported separately.
