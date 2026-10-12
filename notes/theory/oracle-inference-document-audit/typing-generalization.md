# Oracle historical typing, generalization and colored soundness audit

Date: 2026-10-12
Status: bounded document audit and counterexample independently reviewed; research only
Current Yulang baseline: `67830dce14e6987b37e47b2540c204fcd06a92c6`
Oracle anchor: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Output lease: this file only
Owner: primary-assigned leaf; no delegation, compiler edits or Git mutations

Review integration (primary): a fresh `compiler_referee` independently verified
the ground CBV I-Let counterexample, Common/prior-mask formulation discrepancy,
original theorem scopes and generalization/extraction gaps. No correctness
findings. The producer's original packet below records its pre-review status;
this paragraph supersedes that status only. Review does not certify the whole
colored metatheory, declarative calculus, Oracle compiler or current Yulang
parent theorem. Frozen producer SHA before annotation:
`8950a1665959019c4613c5babdc3730029e6e87a5ffeeb4e5e149a1b58607774`.

## 1. Frozen objective and evidence boundaries

Audit the original historical typing/generalization and colored operational
claims before comparing them with current Yulang. Preserve each claim's actual
terms, environments, binders, quantifiers, assumptions and conclusion. A theorem
heading or successful historical implementation is not proof closure. This note
does not redefine the toy calculus to make its claims true.

The historical documents are read from Git objects, including deleted files.
The mutable worktree is not an Oracle authority. Current transfer dependencies
listed below were compared byte for byte with the current pinned Git objects;
they were unchanged at inspection. `catalogue.tsv` is a discovery index, not
approval evidence or proof status. No compiler code, tests, runtime probe or
external reference was needed for the counterexample below.

Research `research/effect-mini-language/AGENTS.md` at the Oracle anchor explicitly
says this directory is mini-language discussion rather than the implementation
specification of Yulang. It requires separating definitions, examples,
counterexamples, lemmas and open points. This governs interpretation of all six
TeX artifacts. Neither commit messages nor anonymous theorem headings constitute
user approval.

Active governing sections: `rules/design-authority.md`, Authority order and
Natural compiler behavior and proof-obligation economy;
`rules/compiler-engineering.md`, Natural compiler behavior and proof-obligation
economy and Deterministic Simple-sub inference; `rules/agent-orchestration.md`,
Model routing and Astra escalation and Proof delegation and decomposition;
`rules/research-lab.md`, One semantic baseline and Evidence quality;
`rules/git-concurrency.md`, Disjoint-file mode. The selected top-level inference
principles of 2026-10-11 govern current inference. The leaf owns no adoption,
integration, review assignment, or proof-status promotion.

## 2. Historical revisions and actual authority

| Artifact | Declared date / recovered revision | Relevant claims and limitations | Approval evidence |
| --- | --- | --- | --- |
| `colored_weighted_simple_sub_ja.tex` | June 21; added `b2555e09a`, June 21 13:05:23 +09:00; recovered `1301b1a93^` | §§8–11 jointly quantify type/row/id variables; runtime thunk/force elaboration; cleanup semantic preservation and principal weighted scheme are explicitly **conjectures**. Global solver completeness/principality remain open. | Research draft; explicit user approval not found in inspected document. |
| `weighted_effect_subtraction_core_ja.tex` | June 21; added `5f1e75e7d`, June 21 17:58:18 +09:00; recovered `1301b1a93^` | §8 I-Let returns body computation type; §9 principal extraction is a definition, not a principal-type theorem. | Research draft; unknown. |
| `directed_stack_weight_principal_letrec_ja.tex` | June 22; added `59df62404`, June 22 02:48:19 +09:00; recovered `1301b1a93^` | §§7,9–10 claim declarative soundness, nonrecursive principality and monomorphic let-rec principality. §12 explicitly leaves worklist termination, family arguments, cleanup completeness and self-tail solution preservation open. | Research draft; unknown. |
| `directed_stack_weight_principal_letrec_colored_soundness_ja.tex` | June 22; added `0dd37b900`, 02:54:50 +09:00; recovered `f2c186b3e^` | Adds §§9–10 colored operational interpretation and fundamental theorem, **assuming** well-bracketed elaboration. §13 explicitly leaves concrete compiler marker placement and full implementation correspondence open. Revised `cfd2ef4b5`, June 22 05:19:19 +09:00, to entry-except snapshots. | Research draft; unknown. |
| `directed_weight_row_solver_termination_ja.tex` | June 22; added `fac1aeec8`, 03:26:13 +09:00 | Termination lane is audited separately; no closure is imported here. | Research draft; unknown in this lane. |
| `directed_stack_weight_letrec_complete_ja.tex` | June 22; added `f2c186b3e`, 14:21:19 +09:00; surviving anchor version | §§7,9–12,14 claim the source generation, colored fundamental theorem, soundness and principality together with termination. Normalized marker materialization replaces the earlier explicit compiler-elaboration assumption in the toy theorem. | Research draft; unknown. |

The alternate surviving complete document at `a1952fd32` (June 22 19:13:40
+09:00, “Document var-var replay lowering gap”) is materially different from
the Oracle anchor. Its additional paragraph after exact row termination states
that effect-sequence fan-out normalization is assumed, while actual Rust
application/catch/block/defined-lambda lowering can introduce alias cycles that
the abstract machine does not cover. It adds this normalization to the main
theorem hypotheses and implementation invariants. The anchor omits this
paragraph. These versions must not be merged into one supposed proved claim.
Their I-Let, colored fundamental and principal sections are unchanged by that
delta; the obstruction below applies to both written versions.

`spec/2026-06-13-computed-fetch-value-restriction.md` declares a June 13 decision,
was added at `174b120df` (16:45:23 +09:00), and amended at `24cf3b3ae`
(19:19:12 +09:00) with top-level execution roots. Its declared decision is
document evidence; no separate explicit approval record was inspected.
`spec/2026-06-06-invariant-type-sandwich.md` declares a June 6 decision and was
introduced with `1a8c72450` (17:33:25 +09:00).
`spec/2026-06-02-role-system.md` originates at `b8f78e00b` (June 2
19:17:13 +09:00), with many later amendments. The anchor content of these dated
paths is not necessarily their first revision. Their substantive contracts are
summarized below without treating unknown approval as established approval.

`docs/infer-solver-invariants.md` originates at `c436fc309`, June 23
13:05:27 +09:00, with later maintained sections. It says explicitly it is **not
a complete implementation proof**. `docs/effect-inference-brief.md`, introduced
at `0f9c1080d`, June 23 19:30:47 +09:00, labels itself an outward-facing draft.
It expressly forbids claiming finished public-projection principality and
leaves full implementation-graph termination open. These cautions are part of
the historical evidence, not optional qualifications added by this audit.

## 3. Original frozen claims

The complete document's scope (§1, anchor lines 189–220) is a finite effect
family set with powerset capability algebra; unit, functions, computation
types and effect rows; complete shallow single-family handlers; Damas–Milner
let generalization; monomorphic recursive RHS; finite regular graphs;
fresh static IDs at annotation/protection sites and fresh runtime colors per
scheme instance. Operational semantics is its normalized-marker **call-by-value
core**. Thunk/force and additional constructors are expressly excluded.

Its term grammar (§2) allows arbitrary `e1` in `let x=e1 in e2` and
`let rec f:K=e1 in e2`. It does not restrict either initializer to a syntactic
value or lambda. §7's optional sentence “if adopting a value restriction” does
not select that restriction as a hypothesis of the subsequent theorem.

### 3.1 Generalization and principality

The generated judgment is `Gamma; level |- e => C -| G`. Schemes are
`forall type-vars row-vars ids. C`; instantiate freshens all three together.
Recursive lookup returns the same monotype root and IDs.

I-Let (§7, lines 877–889) infers `e1` at `level+1`, computes
`Sigma1=gen_level(compact(sat(G1),C1),Gamma)`, then infers `e2` under
`x:Sigma1` and returns exactly `C2` with `G1 union G2`.
`gen_level` quantifies variables and IDs above the boundary that have not
escaped into the environment. The document does not define the owner operation
that computes escape or lowers levels.

I-LetRec (lines 891–912) forms `Cs=A_minus(K)`, fresh root `alpha_f` at
`level+1`, inserts `Cs <: alpha_f` before RHS inference, uses `f:alpha_f`
monomorphically, adds `C1 <: alpha_f`, saturates/compacts at `alpha_f`, then
generalizes and infers `e2`. Its final computation type is again exactly `C2`.

The principal order (§12, lines 1949–1960) puts the more general scheme on the
left: `Sigma <= Sigma'` means the latter is obtainable by type/row substitution,
injective ID renaming and permitted subtype widening. The required theorem is
universal over **every** alternative well-typed weighted scheme; it is not
existence of one solution or a successful probe. The nonrecursive theorem
covers unit/ref/lambda/app/perform/complete-handle/let. The recursive theorem
covers all the given terms under monomorphic recursion and the same skeleton.

The recursive factorization premise is explicit:
`Gamma,f:D |- e1:D1`, a skeleton realization `Cs' <: D`, and `D1 <: D`.
The conclusion is one solution morphism from the whole generated recursive
graph to that typing. All recursive occurrences must map to the **same** `D`;
independent witnesses per occurrence do not satisfy this statement.

### 3.2 Colored fundamental theorem and main theorem

The fundamental theorem (§11, lines 1852–1899) quantifies over every generated
derivation `Gamma;level |- e=>C -| G`, every `theta in Sol(G)`, injective
color environment `chi`, every step index `k`, flow `Phi` and semantic
environment `rho`. It requires:

```text
chi;Phi |=_k rho : theta(Gamma)
  implies chi;Phi |=_k Elab_chi(e)[rho] : theta(C).
```

The complete version says normalized materialization plus the code-bracketing
lemma establishes the well-bracketed invariant automatically. The predecessor
colored version instead assumes a well-bracketed elaboration. Materialization
specifies markers for normalized weight entries, not a complete syntax-directed
evaluation/elaboration function for every source construct.

The computation relation (§11, lines 1790–1815) requires every visible operation
observed within the step budget to belong to `theta(R)` when the computation
type is `A!R`. Invisible operations must preserve payload/continuation relations
but are retransmitted. Hence the theorem includes effect soundness of ordinary
CBV evaluation, not merely a property of handler family matching.

The declarative corollary requires
`theta(Gamma) |- e : theta(C)` in a marker-forgetting declarative system.
No full independent declarative rule catalogue is printed. The earlier basic
soundness draft specifies subsumption and weighted relations and sketches a
syntax induction; the complete version instead invokes logical-relation
“adequacy” to conclude declarative typing. Semantic membership does not by
itself establish derivability in an independently fixed syntactic calculus.

The main theorem (§14, lines 2127–2146) quantifies over finite terms and finite
source-admissible environments, assumes the listed exact solver mechanisms,
and claims finite failure for unsatisfiability or a returned hidden scheme that
is declaratively sound, colored handler sound and principal over the full
stated monomorphic/skeleton language. It cannot be promoted from one subordinate
lemma or from a proof of conditional weighted rewriting.

## 4. Direct in-model counterexample: CBV let initializer effects

**Claim class:** constructive document-level refutation of the written colored
fundamental theorem under its stated CBV evaluation; independently checked. This is not a
claim that the actual Oracle compiler accepts an unsound program.

Fix `Fam={h}` and the ground operation signature `h:Unit ~> Unit`. Let
`Gamma` contain that signature only, `Phi` be empty, and consider:

```text
e = let x = perform_h(()) in ()
```

This is a finite term of the printed grammar, without recursion, annotation,
thunk/force, open family arguments, captures or effect aliases. It is admitted
by the stated default rules; no syntactic-value restriction is adopted.

The complete document's I-Unit gives `():Unit!Empty` with no constraints.
I-Perform gives `perform_h(()):Unit!{h}` with no constraints: its ground
signature premise is discharged by I-Unit. I-Let generalizes that ground
computation (no free type/row/ID variables) and types the unused-binding body
as `Unit!Empty`. Its literal conclusion is therefore:

```text
Gamma;level |- e => Unit!Empty -| empty graph.
```

Saturation has no work, so the identity solution satisfies the graph. The
example introduces no annotation/protection weight occurrence requiring
normalized guard or pop materialization. At empty flow the ordinary uncolored
operation is visible. CBV evaluation starts by evaluating the initializer,
which emits `Oper(h,empty,(),K)` before the final body can return.
For a step index large enough to observe that finite prefix, the computation
relation requires `h in Empty`, which is false. Thus the required universal
fundamental conclusion fails on an admitted term.

The document gives no alternate `let` evaluation rule that delays an unused
initializer. Its stated core is CBV and excludes thunk/force. Installing such
a rule or restricting initializers now would change the theorem's language;
neither is a repair authorized by this audit. A hypothetical independent
declarative calculus with the same effect-dropping let rule might agree with
the generated typing, but that agreement would not repair the operational
fundamental theorem. Conversely, an ordinary CBV declarative let rule that
sequences initializer effects cannot derive this purported empty-effect result.

The same I-Let conclusion occurs at lines 765–777 of the principal predecessor,
790–802 of the colored predecessor, and 473–483 of the core-subtraction draft.
The first June 21 colored draft discusses generalization but does not present
the later all-term fundamental theorem; do not retroactively label its
explicitly open principal conjecture a proved or refuted complete theorem.

The owning missing obligation is **A, operational correctness**: show the actual
Let constructor and its elaboration retain initializer evaluation effects and
the actual binding's computation/value status. It is not a display cleanup,
optional all-view characterization, or a reason to weaken ordinary inference.

## 5. Other exact proof gaps and bounded positive results

### 5.1 What follows directly from the printed rules

The syntactic recursive-sharing fact is valid without a principality theorem:
under I-LetRec, `f` is a monotype entry; I-Ref does not instantiate it; every
recursive occurrence refers to the same `alpha_f` and same IDs until RHS
completion. This is a construction fact about these rules, not proof that
actual Yulang source lowering emits them or that intrusion preserves meaning.

Injective color renaming preserves visibility **when the whole correlated
state is renamed together**: for an injective map `r`,
`r(kappa) intersect r(supp(Phi)) = r(kappa intersect supp(Phi))`.
Therefore emptiness, guard snapshot-intersection tests and matching-color
identity are preserved. This elementary local fact supports the substitution
sketch, but does not authorize freshening already executed initializer evidence,
external free colors, provider identity, or only one marginal projection.

The printed bound-closure argument is a conditional operational lemma: if each
new lower/upper is installed first and paired with every existing opposite bound,
and processing is exhaustive, every Cartesian pair is covered when the worklist
empties. It is not evidence that actual constructor, memo, admission and replay
owners implement those conditions. The separate source/weights lane owns those
coverage questions.

### 5.2 Generalization is referenced, not established

All three later documents invoke a “standard generalization lemma” for type
variables, row variables **and static IDs**. They do not state and prove a
joint lemma with these additional requirements:

- retained free environment fields and their reachable bounds stay shared;
- fresh quantifiers occur at the original scopes, with all dependency binders
  above them and all dependent challenges below them;
- aliases of one monomorphic instance share one substitution and runtime color
  frame; independent uses freshen only genuinely quantified coordinates;
- escape/extrusion respects levels and every negative/positive occurrence;
- evaluated RHS evidence, actual returned value/provider and captured external
  identities stay fixed while eligible descriptions may vary;
- graph coalescing and cleanup preserve the joint instance set, not just
  individual lower/upper or observation projections.

The finite-ID freshening clause alone proves none of these. There are no native
level-lowering/extrusion transitions or a Value/type association constructor in
this historical theorem. Damas–Milner is cited, but a citation does not discharge
these weighted, operational and recursive extensions.

### 5.3 Extraction/factorization and recursive scope

The compact-representation lemma (complete lines 1973–1985) asserts both that
every graph solution gives a compact instance and that compact instances lose
no graph solutions. Its proof invokes ordinary Simple-sub coalescing and
polar projection; a proof of polar preservation alone does not establish this
whole joint solution correspondence, cycle handling, weight cleanup or bound
activation. The printed one-layer extraction is an output policy whose
adequacy still needs that correspondence.

The fresh-factorization lemma asserts any alternative typing maps into one
generated graph. Its syntax sketch is useful, but lacks a separately specified
full declarative target and weighted generalization/substitution theorem.
The let-rec argument uses finite graph maps and monomorphic lookup correctly
as a strategy. However, its operational proof speaks of recursive **closures**
while the source grammar permits arbitrary RHS terms. A lower bound
`Cs <: alpha_f` is not itself a proof that every root realization traverses
the exact skeleton's colored boundaries. The term-level elaboration and joint
recursive introduction laws must supply that conclusion.

The recursive principal proof applies the nonrecursive theorem to `e2`, even
though `e2` may contain further let-rec. This can be repaired at the proof level
by a properly stated simultaneous structural induction using the strict
subterm, but that induction does not fill the underlying generalization,
extraction or source-law gaps. No theorem status is changed by identifying it.

The independently reviewed import
`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md` fixes the original
paper §5 theorem scope as **non-let-polymorphic**, distinguishes published
theorem statements/proof sketches from omitted auxiliary proofs, and keeps
let/effects/intrusion extensions open. Thus the historical phrase “as ordinary
Simple-sub” is not a complete imported proof of let-polymorphic weighted
principality. This audit does not rerun the original paper proof.

### 5.4 Colored interpretation and proof dependencies

The complete Common-capturability theorem (lines 1682–1706) states that the
conjunction of ambient membership, absence of existing entry-except masking,
and final visibility is equivalent to `h in Common(L)`. The earlier colored
version keeps absence of prior masking as an explicit **premise**. In the
complete wording, the right side depends only on the family and weight and
cannot imply absence of arbitrary pre-existing colors in an operation.

For example choose ambient containing `h`, one active ID `u` permitting `h`,
an outer active color `c` in `Xi_u`, and operation `kappa={c}`. Then
`h in Common(L)` holds, whereas condition 2 and visibility fail. This is a
literal quantifier/formulation obstruction in the printed boundary theorem,
not a demonstrated actual-source runtime trace. The forward necessary-family
direction can still hold; no equivalence closure is claimed. Renaming or
silently moving condition 2 back to a premise would narrow the original
statement and needs explicit adjudication.

The normalized materialization definition enumerates marker words but does not
define complete syntax-directed marker placement for evaluation contexts,
return/nonlocal exit, repeated recursive activation, or captured values.
The earlier colored document explicitly retains this as “concrete elaboration
placement”; the complete toy-core scope cannot transfer it to Oracle by
asserting code bracketing. Well-bracketed invariant establishment is separate
from proving a transformer implication once that invariant is assumed.

Residual narrowing says removed families do not occur in the ordinary residual
and cannot be captured again. Guard coloring can prove visibility exclusion;
it does not itself prove absence of a runtime operation, especially for a
resumed shallow continuation whose printed type contains the original `S`.
This must be reconciled by a fully defined row semantics, elaboration and
continuation relation, rather than treating a powerset budget as an execution
nonoccurrence theorem.

The self-tail finite-observation lemma, row-split maximality, mixed normalization
and source replay-cycle balance are dependencies audited by the weights lane.
Their theorem headings are not accepted as independent premises here. In
particular finite-step observational preservation does not automatically prove
equality of solution sets needed by global principality.

## 6. Historical implementation contracts outside the toy theorem

The computed-fetch specification makes a distinction absent from the default
toy I-Let: `FetchValue` versus `FetchComputation` is binding metadata, separate
from expression `Evaluation`. Function retrieval is a value even when its body
computes. A computed binding's acquired type, role predicate, effect-row/stack
residual and annotation/associated-type variables must not be quantified
locally; they move to the enclosing owner level. Computed multi-root SCC edges
are rejected, whereas function-reference SCCs are admitted. Computed top-level
bindings are execution roots even when unused. These are substantive source,
owner and publication contracts. Optional syntactic-value restriction in a
toy paragraph does not prove this metadata-sensitive restriction.

The role specification couples levels of variables within a demand, lowers
the owner for explicit computation, includes predicate-only variables in
polarity/co-occurrence analysis, and resolves associated types through a loop
that can emit new constraints and trigger recollection. The sandwich
specification requires same-argument interval cross constraints
`loA <: upB` and `loB <: upA`, including effect-family parameters and role
arguments; root-local component merging is not merely display normalization.
The toy theorem excludes roles, associated types, family type arguments,
ADT/record/tuple extensions and this dynamic generalization loop. Their
source coverage therefore remains separate even if the toy theorem is repaired.

`docs/infer-solver-invariants.md` adds private data-position evidence, ordinary
public residual projection, same-boundary alias-cycle subsumption, row-tail
polarity, maintained owner dirty-scheduling contracts and per-demand
generalization-role snapshots. It expressly says `kappa <: e` is not
`kappa=e`. `docs/effect-inference-brief.md` distinguishes hidden weighted
principality from **principal-style public signatures** and explicitly keeps
the public generality order open. Neither document supplies the missing proof.

There is a concrete revision mismatch: anchor complete §4 flattens both row
weights before head subtraction; the invariant/implementation documents say
not to combine the two weights for row-head consumption. The latter also
describe storage-time alias subsumption beyond exact label keys. The weights
lane owns semantic adjudication of that difference; this lane records that
literal conformance and inherited theorem use cannot be assumed.

Related catalogue documents inspected:
`docs/hidden-effect-evidence.ja.md` describes a distinct HandlerMatchEdge and
typed-IR/runtime evidence responsibility; it is not definitionally identified
with the normalized colored-marker calculus. The approved
`notes/design/2026-08-10-generalized-witness-claim-bridge-provenance-gap.md`
(rev.2 approved August 11 according to its header) retains an exact selected
replay conjunction, carrier/result and original producer in generalized
diagnostic provenance. It is evidence that generalized witness lineage can be
lost at a concrete boundary despite stored constraints, not a general proof
of weighted soundness or principality. The consultation technical brief
expressly asks where hidden/public principality belongs rather than proving
their equivalence. Uninspected catalogue entries remain unaudited.

## 7. Dependency DAG and current transfer

```text
Independent declarative rules / primitive signatures / CBV Let semantics
  -> exact source constraint generation + complete elaboration
  -> weighted rewriting + full bound activation/replay preservation
  -> joint graph solution/extraction correspondence
  -> scoped joint generalization + lawful correlated instantiation
  -> nonrecursive principal theorem
  -> joint monomorphic recursive introduction/factorization
  -> let-rec principal theorem

complete elaboration + well-bracketed color invariant
  -> local guard/paint preservation + Common theorem
  -> weighted constraint preservation + colored substitution
  -> colored fundamental theorem -> operational handler/effect soundness

source graph / replay invariants -> termination
all above -> integrated hidden-scheme theorem
hidden scheme -> separately justified public projection -> public principality
actual compiler constructors/consumers -> implementation correspondence
```

The Let counterexample breaks the effect/fundamental branch before solver
termination. Generalization and extraction gaps independently prevent the
principality branch from being closed. One broken branch is sufficient to
prevent the integrated theorem; no equivalent third reconstruction proof is
useful until the owning premise is supplied.

Current source Generalize (October 8 definition §§2–4; corresponding proof
§§3–5, L1–L5) retains explicit `Desc`, `Shared`, `ViewLogic`, `EventField`,
`EventProof`, `Executed/OneShot`, established contracts and internal recursive
relations at their owning constructors. Eligible descriptions vary at their
original scopes; actual binding/provider, executed choices and shared witnesses
remain anchored. Its reviewed scoped soundness/completeness is conditional on
the genuine local laws L1–L5. It supplies no production solver recognition,
level/extrusion correspondence or public-projection theorem. This is materially
more explicit scope information than the historical “standard generalization
lemma”; it cannot be used retroactively to declare the old lemma proved.

Current complete Call (October 7 §§2–5) retains the original callee computation,
whole argument, actual returned provider/entry, complete ordered pending suffix,
return/future interface, all independently licensed W/Z alternatives and
whole-operation witness. Toy I-App's arrow comparison and effect sequence do
not establish complete C0, source interface formation, active consumer
preservation or this full shared tuple. No marginal provider or observation
witness may be substituted for that dependency.

Current residual identity (October 10 selection) preserves separate constructor
lineages even when row equalities or residual keys agree. The historical global
`resid(source,J,L-minus-J)` reuse key is not an automatic current construction
rule; attachment/filter/origin/context and every later lower/upper replay must
remain with each retained recipe.

Current intrusion clarification (October 12 §§Qualification and Implementation
boundary) compares SCCs of **values associated with actual type occurrences**,
not type-row SCCs. Copying descriptions does not copy value incidence or create
reference edges; fresh-use independence and extrusion pairs remain distinct.
The historical type/row/ID scheme grammar has no constructor assigning this
association. The October 12 clarification explicitly retains open the copied
port association and equality-preservation proof. Neither a source Generalize
`Desc` declaration nor historical monomorphic root sharing fills that premise.

Required current bridge, still open: actual source constructors must retain
value identities and resolved-reference edges, associate each type occurrence
through polar extrusion and fresh use, preserve joint scopes/lineages, activate
all required bound/replay/filter obligations after qualifying intrusion, and
generalize only eligible coordinates at their actual publication boundary.
Then actual consumers must preserve original source soundness, required
principality, normal progress, complete Call and effect hygiene. This audit
does not invent a transport convention or certify the current candidate.

## 8. Checks, resources, frozen dependencies and handoff

Commands: bounded `git show REF:PATH`, `git log --all --follow` and add-history
queries, `git diff a58eefc31 a1952fd32 -- <complete-TeX-path>`, `rg`/section
reads, and one Python standard-library hash/equality read. No code inspection,
build, test, benchmark, Oracle execution, typesetting, probe, Git mutation or
extra agent was run. Local commands were short single processes; no heavy
process budget was consumed. Wall allocation: 25 minutes; this is a bounded
first pass, not exhaustive review of every catalogue item.

Requested routing: primary Sol proof leaf. Configured normal proof default:
`gpt-6.1-sol/high`; `.codex/agents/prover.toml` has no overriding pins and the
callable schema has a prover role. Observed live model/effort metadata:
**unknown to this leaf**. No Astra assignment or routing/configuration change.

Frozen historical content SHA-256:

| Ref / dependency | SHA-256 |
| --- | --- |
| `1301b1a93^`, principal-letrec | `ffb2985b490996545dc969787c71da4dbdcbf32448a8b3550133a4bdd3c9d085` |
| `f2c186b3e^`, colored-soundness | `b9c9acf45af326485ca77403393a0a48dec5823e5c826631df4821892ae80a90` |
| `a58eefc31`, complete | `efed007a3848c94f9d8925985f66e76ab86082dcb094c7ec3851b2bdd7082843` |
| `a1952fd32`, alternate complete | `31911eb0ae8351703e0b1fcfe2b9c3c3443254be0d8fcc5395ff66914dee84bf` |

Current dependency SHA-256 at `67830dce` (working contents equal at inspection):

| Dependency under `notes/design/` | SHA-256 |
| --- | --- |
| `2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `2026-10-12-intrusion-value-type-association.md` | `a5c69e3bf7661e5212abfd38ae4c757f2e9a02cb7ed1409bb2c2bf40bafae1d3` |
| `2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Unverified: actual Oracle compiler Let/fetch/elaboration behavior; exact source
coverage and weighted solver proof assigned to the other lane; all production
correspondence; fresh independent proof review; exhaustive approval history;
uninspected historical catalogue paths. The alternative complete revision is
comparison evidence, not substituted governing text. Parent soundness,
principality, source correspondence and F5 gates stay OPEN.

**One next action:** primary assigns fresh independent review of the literal
CBV Let derivation and original theorem scope, then routes the missing Let/fetch
and scoped generalization premises to their actual source owners. Another
equivalent factorization sketch must not be counted as progress.

### Commit packet

- Exact leased changed path: `notes/theory/oracle-inference-document-audit/typing-generalization.md`.
- Baseline: Yulang `67830dce14e6987b37e47b2540c204fcd06a92c6`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; frozen input hashes above. This new note is the only leaf write.
- Honest status: unreviewed research audit/counterexample; no authoritative or parent-theorem closure.
- Checks already run: Git-object section/history/delta reads and SHA-256/current-byte comparisons; no executable tests or compiler checks.
- Proposed checkpoint message: `research: audit Oracle typing generalization and colored proof gaps`.
- Shared-record deltas left to primary/curator: record the historical fundamental/main claim as challenged by the admitted CBV Let witness; retain principality OPEN with exact joint generalization/extraction premises; distinguish the anchor and fan-out-amended complete revisions; keep all compiler/transfer gates OPEN pending independent review and source-owner evidence. Do not edit dated authoritative specifications from this report.
