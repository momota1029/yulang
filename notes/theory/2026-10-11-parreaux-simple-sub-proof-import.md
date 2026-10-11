# Ordinary Simple-sub: original proof import and `λf. f 1`

Date: 2026-10-11
Status: frozen, independently reviewed source import; no Yulang gate closure
Yulang baseline: `f7f123a8f36aa4b5d4a7f0738ac07601af5ae214`
Branch: `research/simple-sub-intrusion`
Reference baseline: `LPTK/simple-sub` / `mlsub-compare`, `9bae772624c23b52a93c1b226157e16898b4d9db`
Producer: leaf proof assignment; no delegation, compiler changes, or Git mutations

## 1. Frozen objective, sources, and claim classes

The user's correction is to obtain the ordinary Simple-sub proof from its
original source. This note imports that source's statements and proof
architecture, then derives the exact ordinary lambda/application example.
It does not replace an open Yulang theorem with a weaker statement.

Primary mathematical source: Lionel Parreaux, *The Simple Essence of Algebraic
Subtyping*, PACMPL 4 (ICFP), Article 124 (2020),
[DOI 10.1145/3409006](https://doi.org/10.1145/3409006),
[official EPFL PDF](https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content).
Persistent local copy: `/home/momota1029/rust/simple-sub-reference-paper.pdf`.
Page numbers below are printed pages `124:n` (PDF page n).

Primary operational source: the author's
[pinned implementation](https://github.com/LPTK/simple-sub/tree/9bae772624c23b52a93c1b226157e16898b4d9db),
persistently cloned at `/home/momota1029/rust/simple-sub-reference`.
Its README, ICFP 2020 section, identifies `mlsub-compare` as the corresponding
paper branch and separately identifies submission commit
`252908c452c9f48643ecb57b69cc2e41cd7483da`. This note audits the pinned later
branch commit, not an uninspected submission snapshot.

Exact mathematical scope: finite, well-scoped terms in the paper's
**non-let-polymorphic** fragment; integer literals, variables, lambdas,
applications, records and projections; the Fig. 3 declarative typing rules
restricted to that fragment; Fig. 10 syntactic subtyping. Types include the
paper's primitive, arrow, record, variable, union, intersection, top, bottom
and recursive forms. Theorem statements start with empty context and empty
bound store. General lemmas explicitly introduce context, store and
substitution quantifiers below. Fresh lambda variables are monomorphic;
top-level scheme subsumption is still meaningful without local polymorphic let.

Required local conclusion: from the actual reference constructors for
`Lam(f, App(Var(f), Lit(1)))`, obtain the demand `α <: Int → β`, the internal
root `α → β`, and its ordinary coalesced scheme. Separately identify the
published soundness/principality claims and their actual proof coverage.

Claim classes:

- **Imported published theorem statements with proof sketches:** paper §5.3,
  Theorems 1–2 and Lemmas 1–5. This note does not supply their omitted proofs
  or promote a Yulang theorem by citation.
- **Direct finite source characterization and declarative derivation:** §§4–5
  below, for this one ordinary term and the stated same-level continuation.
- **Unproved extension obligations:** §6. These remain Yulang obligations.

Exclusions: Yulang source lowering, complete Call, effects, protection/hygiene,
provider/attachment/witness/residual lineage, scoped operation arms, intrusion,
SCC-wide generalization, public scheme publication, and F5 replacement.
No equality-solving rule, annotation requirement, independently selected
marginal witnesses, or restriction on ordinary inference is added.

Governing repository policy: `rules/agent-orchestration.md`, **Model routing
and Astra escalation**, **Proof delegation and decomposition**;
`rules/research-lab.md`, **One semantic baseline, explicit dependency
invalidation**, **Evidence quality and stopping unproductive loops**;
`rules/compiler-engineering.md`, **Natural compiler behavior and
proof-obligation economy**, **Deterministic Simple-sub inference**;
`rules/design-authority.md`, **Authority order**; `rules/git-concurrency.md`,
**Disjoint-file mode**. The Authoritative
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5,
governs the inference direction and abnormal-path limits. The prior
`notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md` is audit history,
not a substitute for rereading the original paper and implementation.

## 2. Exact imported theorem order and proof architecture

Let `σ` map reference variable identities to their mutable lower/upper lists.
Write `typeTerm(t,ctx), σ ⇓ (st,σ′)` for successful inference. Let
`Eσ⁺(st)` and `Eσ⁻(st)` denote ordinary positive/negative coalescing (Fig. 11).
All recursive coalescing binders are distinct from the free variable name
associated with the same identity, and are indexed by **identity and polarity**.

The paper's order is crucial: `P ≤∀ Q` means that for some type-variable
substitution `ρ`, `ρ(P) ≤ Q`. Thus the left scheme subsumes the right;
**more general schemes are on the left**. This is neither equality nor the
claim that the left monotype is below the right for every substitution.
Ordinary `≤` is Fig. 10 subtyping, with arrow arguments contravariant and
results covariant. Empty bound unions/intersections denote `⊥`/`⊤`.

Theorems 1–2, §5.3, p.26, have these quantifiers and directions:

1. **Soundness:** for every `t`, if inference from empty context/store succeeds
   with `(st,σ)`, there exists `τ` with `⊢ t : τ` and `τ ≤∀ Eσ⁺(st)`.
2. **Completeness/principality:** for every declaratively derivable `⊢ t : τ`,
   inference from empty context/store succeeds with some `(st,σ)` and
   `Eσ⁺(st) ≤∀ τ`.

Their type soundness is agreement with the declarative type system. Section 5
does not present an operational preservation/progress theorem for a Yulang
runtime. In particular, these statements cannot directly certify effects or
complete Call.

For soundness the paper switches to **unifying coalescing**, Fig. 12; denote it
here by `U` to distinguish the interpretation, although the paper reuses `E`.
For a fresh nonrecursive variable, ordinary coalescing retains a free variable
alongside the appropriate bounds. Unifying negative coalescing instead uses
only the upper-bound intersection; unifying positive coalescing includes that
negative interpretation together with the lower-bound union. Under consistent
bounds, `Uσ⁺(v) ≤ Uσ⁻(v)`. Recursive revisit cases remain those of Fig. 11.
These proof interpretations are not another production solver.

The five lemmas are stated on pp.26–27:

| Lemma | Frozen statement and proof responsibility |
|---|---|
| 1, general soundness | For every consistent `σ` and successful `typeTerm(t,ctx),σ ⇓ (st,σ′)`, `σ′` is consistent and `Uσ′⁻(ctx) ⊢ t : Uσ′⁻(st)`. The **negative result interpretation** is as printed. Induction is on successful executions of `typeTerm`; auxiliary lemmas are omitted. |
| 2, sound constraining | For consistent `σ`, successful `constrain(st0,st1)` produces consistent `σ′` and `Uσ′⁻(st0) ≤ Uσ′⁺(st1)`. Execution induction requires a stronger invariant linking cache and subtyping hypotheses, recording newly installed bounds and preserving prior coalesced relations. Intermediate consistency exceptions are needed for variables in the active cache. |
| 3, general completeness | Given `Γ ⊢ t : τ`, **for all** `ctx,σ,ρ` with `ρ(Eσ⁻(ctx)) ≡ Γ`, inference succeeds with some `st,σ′`, and **there exists** `ρ′` satisfying both `ρ′(Eσ′⁻(ctx)) ≡ Γ` and `ρ′(Eσ′⁺(st)) ≤ τ`. The environment and result use the same `ρ′`. Induction is on typing derivations. |
| 4, constraining termination | **For all** `st0,st1,σ`, the constrain call reaches an error or terminates successfully with some `σ′`. No ranking argument or complete proof is printed. |
| 5, complete constraining | The printed premise is `ρ(Eσ⁻(st0)) ≤ Eσ⁺(st1)` (substitution appears on the **left only**). It asserts successful constraining, and preservation of that relation after any successful further comparison from the original `σ`, with coalescings evaluated in the resulting store. Induction is on subtyping derivations, with a strengthened cache/context invariant. |

For clarity, the printed preservation clause of Lemma 5 is: for all
`st2,st3,σ′` such that `constrain(st2,st3),σ ⇓ ((),σ′)`,
`ρ(Eσ′⁻(st0)) ≤ Eσ′⁺(st1)`. This note preserves its one-sided substitution
and store quantifiers; it does not silently repair or strengthen that statement.

Fig. 10, p.24, includes reflexivity/transitivity, guarded hypotheses,
union/intersection subtyping, arrow and record rules, and recursive unfolding.
An assumed recursive comparison is initially delayed by `▷`; crossing an
arrow or record removes that delay. Immediate self-justification is forbidden.
The completeness sketch on p.27 identifies the transitivity problem in a
nonempty hypothesis context: arbitrary assumptions can invalidate the desired
transitivity elimination. Its proposed stronger induction must show successful
constraining introduces no such assumptions and admits derivations without
`S-Trans`. That invariant is described, not formally stated or proved in full.

**What is actually present:** §5's opening, p.24, explicitly says complete
proofs are outside the paper's scope. Section 5.2 assumes an omitted immutable
version of constraining equivalent to the mutable one. Section 5.3 gives the
seven named statements and induction strategies, plus the cache/consistency
and transitivity obstacles. It does not give all strengthened hypotheses,
auxiliary lemmas, or a machine-checked development. These omissions must stay
visible when importing the published result.

**Let scope:** §3.5, Figs. 6–9, implements polymorphic and recursive let.
But §5, p.24, explicitly restricts the proof to the non-let-polymorphic
version. Footnote 15 proposes separately proving let correctness by
definition duplication at use sites; it does not carry out that proof.
Neither local let completeness nor Yulang SCC generalization is proved by
Theorem 2 merely because `Let` appears in Fig. 8.

## 3. Actual reference constructors and consumers

Paths below are relative to the frozen reference checkout.

| Responsibility | Paper | Exact reference source |
|---|---|---|
| Literal, variable, lambda, application | §3.2.1, pp.9–10; Fig. 8, p.20 | `shared/src/main/scala/simplesub/Typer.scala:59–84`; `IntType` at :21 |
| Opposite-bound replay and structural comparison | §3.2.2, pp.10–11; Fig. 9, p.21 | `Typer.scala:88–129` |
| Extrusion | §3.5.1, Fig. 7, pp.18–19 | `Typer.scala:134–159` |
| Generalization and use-time instantiation | §3.5.1, Figs. 6/8 | `Typer.scala:48–55,166–189,201–207` |
| Ordinary polarity-sensitive coalescing | §3.3, pp.12–14; Fig. 11, p.26 | `Typer.scala:239–257` |
| Removing a nonrecursive one-polarity variable | §4.3.1, p.22 | `TypeSimplifier.scala:231–239` |

Generation equations, using fresh empty-bound variables at the current level:

```text
literal(n)            ↦ Int
name(x)               ↦ instantiate(ctx(x))
lambda(x,t)           ↦ Function(a, infer(t, ctx[x↦a]))
application(s,t)      ↦ b, after constrain(infer(s), Function(infer(t),b))
record(fields)        ↦ Record(fieldwise inferred types)
projection(s,label)   ↦ b, after constrain(infer(s), Record(label:b))
```

`constrain(Function(a,b),Function(c,d))` recursively enforces `c <: a` and
`b <: d`. A record comparison demands every right-hand field on the left
and compares its field types in the same direction. For a variable left
endpoint with an acceptable-level right endpoint, it **first** appends an
upper bound, then compares every existing lower against that upper. Otherwise
the applicable right-variable branch appends a lower and compares it against
all existing uppers. This is ordered insertion: it does not necessarily
install both endpoints of a variable-variable edge. A later opposite bound
runs the dual replay and therefore activates a previously latent demand.

On a level violation, the relevant structural side is extruded and retried.
Immutable variable levels, structural maximum levels and the bound-level
invariant are at `Typer.scala:209–226`. Extrusion memoizes `(variable,polarity)`
before descent. Positive extrusion links original-to-copy and copies lowers;
negative extrusion links copy-to-original and copies uppers. Function arguments
flip polarity. This is not polarity-erasing parent sharing or Yulang intrusion.

The reference differs in small operational details from paper pseudocode:
`:93–103` returns on object identity and caches only comparisons with a
variable endpoint. `package.scala:12` defines `is` as reference identity.
Fig. 9 explicitly accepts matching primitive names; this pinned implementation
instead relies on shared primitive objects for its ordinary constructor paths
(`IntType`, `BoolType`). A claim about arbitrary externally supplied distinct
`Primitive("int")` objects would require an additional source bridge. The
example below uses the actual canonical `IntType` constructor and needs no
primitive-primitive comparison. Full arbitrary-API equivalence is not claimed.

Ordinary coalescing preserves the free variable: positive occurrences become
the variable joined with its lower coalescings, negative occurrences become
the variable met with its upper coalescings. The arrow flips polarity only
in its argument. Recursive binders are keyed by identity **and** polarity.
An empty bound list therefore leaves the ordinary free variable; it does not
turn every unconstrained positive/negative variable into `⊥`/`⊤`.

## 4. Direct ordinary derivation of `λf. f 1`

Freeze the term `t = Lam(f,App(Var(f),Lit(1)))`, empty context and store,
and one current level `l ≥ 0`. Let `α` be the fresh lambda parameter and
`β` the fresh application result. Both are reference variable identities at
level `l`, distinct from each other and from all previous variables.

1. `Lam` allocates `α`, binds the source name `f` to that exact monomorphic
   variable, and recursively types the body (`Typer.scala:64–67`).
2. `Var(f)` returns `α` itself: `SimpleType.instantiate` is identity
   (`:62–63,207`). `Lit(1)` returns canonical `IntType` (`:73–74`).
3. `App` submits `constrain(α,Function(Int,β))` and returns `β`
   (`:68–72`). Thus the actual generated demand is
   **`α <: Int → β`**, with no equality solving or preselected function lower.
4. `level(Function(Int,β)) = l`, so the left-variable branch at `:115–117`
   inserts `Function(Int,β)` in `α.upperBounds`. `α.lowerBounds` is empty;
   this replay has no child comparisons. There is no level violation,
   extrusion, recursion, or failed primitive comparison.
5. `Lam` returns the internal root `Function(α,β)`. Final nonempty bounds:
   `upper(α)=[Function(Int,β)]`; all other lists remain empty.

At positive root polarity, coalescing traverses the argument `α` negatively
and the result `β` positively. Coalescing the upper arrow negatively makes
its `Int` argument positive and its `β` result negative. The same free `β`
therefore occurs in both required positions. The exact ordinary result is

```text
C = (α ∩ (Int → β)) → β
```

with top-level free-variable closure `∀α,β.C`. This is the direct result of
ordinary coalescing, not `α → β` with the bound silently forgotten.

Only `α` occurs at one polarity, and it is nonrecursive. The paper's
simplification and the actual simplifier branch remove it, yielding

```text
D = (Int → β) → β               top-level scheme: ∀β.D
```

For this example the scheme equivalence has a short independent derivation:
`C ≤∀ D` by substituting `α := ⊤`; `D ≤∀ C` by the identity substitution
and arrow contravariance, since `α ∩ (Int→β) ≤ Int→β`. This uses Fig. 10's
intersection/arrow rules; it requires no distributivity or function-merging
axiom. Hence the simplification does not discard an independent restriction.

Direct declarative typing also holds: under `f:Int→β`, T-Var yields that
function type, T-Lit gives `1:Int`, T-App gives `f 1:β`, and T-Abs gives
`⊢ λf.f 1:D` (Fig. 3, p.4). Under `f:α∩(Int→β)`, intersection subtyping
and T-Sub produce `f:Int→β`, giving `C` by the same derivation.

Applying the paper's **published Theorem 2 claim** to this non-let term says
that `∀α,β.C`, equivalently `∀β.D`, subsumes every declarative typing of the
term. The full universal principality argument is the imported theorem with
its stated proof-sketch coverage; this note's finite trace and direct typing
derivation alone do not prove that universal claim.

The spelling `my invoke f = f 1` denotes a Yulang definition, not a paper term.
If one models its body as the ordinary lambda above, the calculation applies
to that model. In the reference's own top-level nonrecursive binding path,
`typeLetRhs(false,"invoke",t)` runs at `l+1`, then stores
`PolymorphicType(l,Function(α,β))`; both variables are above the boundary.
Each use freshens them **together**, including the upper arrow's occurrence
of `β` (`:166–189`). This is a direct operational characterization of the
reference let implementation, outside §5's proved/sketched theorem scope.
It establishes neither Yulang generalization nor Yulang public acceptance.

## 5. Delayed ordinary provider activation

Continue the same ordinary graph with an actual lower function
`F=Function(A,R)` whose structural level is at most `l`. A successful
`constrain(F,α)` enters `:118–120`, retains that exact lower, and replays
it against `α`'s already stored `Function(Int,β)` upper. The arrow consumer
at `:106–108` generates **both** `Int <: A` and `R <: β` from that same
function comparison. Both obligations must succeed; no pair of unrelated
argument and result witnesses is chosen.

For the ordinary identity provider `F=Function(γ,γ)` at level `l`, these
are `Int <: γ` followed by `γ <: β`. The latter retains `β` as an upper
of `γ` and replays its `Int` lower to `β`, installing `Int` as a lower of
`β`. This is a finite trace of the actual two-sided replay code. It illustrates
how a body can accumulate an unresolved callable demand before a provider
arrives. It is not an executed test or a theorem about every later schedule.

The stipulated same-level continuation isolates this particular reference
branch; it imposes no source-language restriction. Cross-level providers
follow the reference extrusion branches and require their full invariant.

## 6. Shortest import base and precise Yulang obligations

The reusable ordinary base is the paper's generation/accumulation/replay
algorithm plus its declarative soundness/principality theorem claims, scoped
exactly as above. Do not reconstruct ordinary function calling through a
separate original-registry route merely to recover this base. Conversely,
the citation does not prove an extension's semantic interpretation.

The existing baseline Yulang trace is recorded in
`notes/theory/2026-10-11-invoke-build-to-simple-sub-proof.md`, §§2–3.
The exact native Apply constructor actively admits its demand in
`crates/yu-solver/src/shadow_apply.rs:1304–1468`; this packet re-read its
actual admission and value/effect submission at :1400–1468.
`candidate_extrusion.rs:763–837` inserts and replays opposite bounds through
the retained replay consumer. `lib.rs:12493–12541` builds four child pairs:
argument value, argument effect, result effect, result value. These actual
owners preserve more information than an ordinary two-child arrow.
This is a narrow source observation, not complete semantic correspondence.

The extension obligations are therefore concrete:

1. **Source generation and native interpretation:** relate the actual Yulang
   lambda/Name/literal/Apply constructors and four ports to Yulang typing,
   including its complete Call meaning. Preserve one callable/provider and
   whole argument/result incidence; scalar arrow projection alone is insufficient.
2. **Extended constraining:** establish the counterpart of Lemmas 2/4/5 for
   the actual value/effect/context consumers, preserving existing relations,
   scope and temporary consistency across real bound insertion, replay and
   suspended continuation. Stored bounds alone prove no activation theorem.
3. **Levels, extrusion, intrusion and generalization:** prove the selected
   extensions preserve soundness and required principal scheme order,
   with shared outer anchors and independent fresh uses. Reference `freshenAbove`
   is operational evidence; §5 supplies no completed let proof and no intrusion
   or SCC publication theorem.
4. **Effects and publication:** establish hygiene/protection/lineage and
   no-inconsistent-publication for actual successful paths and necessary abnormal
   handling. Ordinary Simple-sub has none of these effect constructors.

These are the original extension responsibilities, not a proposed new
reconstruction layer or a reason to weaken ordinary inference. The original
Yulang normal-inference, soundness, principality and complete Call gates stay
OPEN. No missing premise is declared unnecessary merely because the ordinary
example has a concise proof.

## 7. Evidence, dependencies, resource use and handoff

Checks already performed: original PDF text reread for §§2.2, 3.1–3.6,
4.3.1 and 5.1–5.3; `nl`/`rg` inspection of pinned reference constructors,
consumers, instantiation and simplifier; `git show` of the three named
Yulang consumer files at the assigned baseline; SHA256 source/PDF and
baseline/live comparisons; a Python read-only artifact check found no trailing
whitespace and ten balanced Markdown fence markers. `git diff --check --
notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md` also returned zero,
but the file was untracked, so that Git command alone did not inspect its content.
No Scala/Cargo builds, tests, enumeration or
performance measurements ran. The only filesystem write by this leaf is
this leased note. Network reads obtained the original sources before the
primary supplied persistent copies; the PDF copies were byte-identical.

Frozen external hashes:

```text
official PDF      5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
Typer.scala       f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
TypeSimplifier    618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b
package.scala     c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2
README            e226d6268278cda2604cdc1168bbcb5077726f1d437af2137b1b5f006c4d3d8e
```

Baseline Yulang direct dependencies, all byte-identical to the working copies
at the dependency check:

```text
paper audit       0068fe7c17d3e575377279a867ce757098771e3ac2c9c7b332099493e823479c
principles        edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
Build attempt     b453e05a5add06516a388c3d4470505efdfb264753d1e4027243409c2787816d
shadow_apply.rs   230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
solver lib.rs     c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
```

Resource envelope: one leaf, 30-minute wall bound; read-only lightweight
commands, no heavyweight verification and no measurements. No Astra request.
Requested runtime: normal Sol/high proof leaf; effective runtime model/effort
metadata is not available to this leaf and is **unknown**. Role registration
and unpinned prover configuration were read; they do not establish observed
runtime settings.

Unverified scope: complete original theorem proofs and auxiliary lemmas,
immutable/mutable equivalence, reference arbitrary-context primitive API
equivalence, let correctness/principality, all Yulang extension obligations,
Yulang source correspondence, and every extension gate. No closure or authority
is certified.

## 8. Independent review

A fresh `compiler_referee` compared the frozen statements, source trace, and
example against the pinned official paper and implementation. The review found
no blocking, major, or minor issues in the assigned import scope. It confirmed
the theorem directions, printed lemma quantifiers, coalescing distinction,
`λf. f 1` constraint and simplification, and the proof/let-polymorphism limits.
Review scope did not include any Yulang extension or theorem closure.

Next action: the primary assigns independent review of this frozen import,
then uses its ordinary theorem base to target the actual extended constrain
and complete-Call/source correspondence premises rather than reproving the
ordinary lambda/application calculation.

### Commit packet

- Exact lease: `notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`.
- Baseline: `f7f123a8f36aa4b5d4a7f0738ac07601af5ae214`; no changed dependency
  hashes were found. External dependency hashes are above.
- Review status: independent `compiler_referee` found no issues in the ordinary
  import scope; no Yulang theorem closure.
- Checks: source locators and hashes, pinned consumer inspection, Python
  lease-scoped whitespace/fence check; no executable validation.
- Proposed checkpoint message: `research: import Parreaux ordinary Simple-sub proof base`.
- Proposed shared-record deltas for primary/curator: link this import from the
  normal-inference lane; record the exact published theorem and let-proof
  boundaries; retain every Yulang extension gate OPEN. No shared records edited.
