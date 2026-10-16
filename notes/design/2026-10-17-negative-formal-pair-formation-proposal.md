# Negative formal pairs on returned-function paths

Status: Draft; candidate source-definition proposal, independent review NOT RUN.
Scope: formation and use of the negative effect port in `a -> b -> [e] c`.
Approved drafting scope: option B, `RECEIVE-NEGATIVE-PAIR-20261017`; no adoption.
Supersedes: none.
Author: `/root/negative_formal_pair_proposal`, sole author, no descendants.
Assignment: `NPAIR-FORMATION-PROPOSAL-20261017`, handoff revision 1.
Contract: `source-formation-proposals-20261017`, revision 1, SHA-256
`bd2cb5723a31ca7335d0e8d96b14296f5af9254bf6bd8e1156bd648e6b419612`.
Supplied baseline: `601e55cfaaf131644d770006532727da33e33059`; not Git-verified.
Requested model/effort: `gpt-6-astra` / `medium`; observed: UNKNOWN / UNKNOWN.

## 1. Parent and proposed change

The parent remains **CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017, OPEN**.
Preserve all original source occurrences, providers, contexts, worlds,
assignments, guards, continuations, interactions, Call demands and futures.
F1 and FK1 remain independent. FIRST-RESULT, H1/H2/JOINT_DEC, complete Call,
effect hygiene, source-Generalize, soundness, principality, F5 and production
remain OPEN. No foreign-continuation quantifier is discharged here.

Propose an occurrence-indexed negative effect port with two projections of
one ordinary flexible inflow row, plus a permission declaration and a
constraint-derived incidence relation. Formation creates no concrete inflow
and no subtraction residual. Elimination at a real local subtraction consumer
uses the actual reached contribution, its permission association and that
consumer's own evidence. This supplies a concrete proposed formation rule at
the frontier isolated by the prior construction audit. Its preservation,
complete-source interpretation and native realization are obligations below.

The notation `e` in the requested source form is interpreted by the actual
resolved annotation: a concrete family grants permission, while a symbolic
variable retains its ordinary connection and grants no concrete permission.
Let `A,B,C` denote the value types, and use `alpha` for the annotation occurrence
to avoid confusing that occurrence with source type `a`. `Q_alpha` is the
requested `Q_a`. The receive specimen specializes `A=B=Unit`, `C=Int`, `e=ctrl`.
This proposal imposes no new restriction to that specimen or to nullary atoms.
Resolved family arguments, when supported by the original source signature,
remain full operands; the inspected native parser's smaller envelope is an
implementation gap, not a proposed source restriction.

The proposal is independent of the concurrent Catch input proposal. It neither
adopts that proposal nor constructs its outside matcher entry judgment.

## 2. Proposed source signature and introduction

Work in the original typed predecessor context `Gamma`. Retain its complete
binder tree and dependent scopes; the following fields abbreviate inputs at
their own original predecessor positions, not a replacement binder order:

- `O,b,alpha,path`: actual definition, formal, resolved row occurrence, and
  structural path `f.result.value.Function.result.effects` in the specimen;
- `sigma,ell`: annotation lexical scope and ordinary formation level;
- `K_alpha`: resolved concrete family operands at this occurrence, with all
  type arguments and their dependencies; `V_alpha`: symbolic variable operands;
- original descriptor/value formation derivations for `A,B,C`, their shared
  type variables, full Function contracts and source substitutions;
- the actual formal's flexible row `P_f` and its source entry identity.

Source parsing/resolution and composed-polarity calculation supply the first
three items. They supply no successful call, provider inhabitant, effect lower,
handler match or residual. Original complete semantic predicates remain
conjuncts at their original scopes. The structural wrapper proposal of 10/13
does not provide those predicates or their inhabitants.

**N-Port-Intro (NEW candidate rule).** At a resolved negative effect occurrence,
allocate a flexible inflow row `x_alpha` at `ell`, or use the corresponding
ordinary shared symbolic row when the source variable rule identifies it.
Retain `D_alpha=(O,b,alpha,path,sigma,K_alpha,V_alpha)` and all ordinary symbolic
constraints `C_sym`. Form:

```text
Q_alpha+ = PositiveProjection(x_alpha ; D_alpha)
Q_alpha- = NegativeProjection(x_alpha ; D_alpha)
Permission(D_alpha,k)                   for each k in K_alpha
C_port = ordinary row constraints on x_alpha + C_sym
```

These projections are proposed decorated source interfaces. Their underlying
row is the same `x_alpha`; they are not a Support row `{K_alpha}`, an Allowance
cap `{K_alpha}`, or two independently chosen rows. Erasing the annotation
decoration gives the usual positive/negative row views. No constraint
`k <: x_alpha`, `x_alpha <: {K_alpha}`, or `x_alpha = empty` follows from this
rule. A fresh row with no known lower is still open, not a proven empty row.
`Permission` is a declaration with lexical scope, not a lower contribution.

For the singleton symbolic case, propose the same shared-variable connection
already used by `candidate_formal_effect_variable`; no new variable is substituted
for that occurrence. For a concrete-plus-singleton-symbolic occurrence, the
candidate choice is that this symbolic row denotes the same whole inflow,
retaining its existing checks, while concrete operands add only permission.
Whether every original mixed/multiple-variable source form has precisely that
connection must be adjudicated against its complete original signature. The
rule is parameterized by that owner's `C_sym`; it does not invent a join or
close an unsupported symbolic case. This is explicit incomplete coverage,
not permission to reject those source forms. No universal formation theorem
for all symbolic syntaxes is claimed.

**N-Function-Intro (NEW use of the proposed port).** Recursively form the
ordinary value pairs, reversing polarity at argument value/effect children
and retaining it at result value/effect children. For omitted computation
annotations, keep shared fresh ports `X,Y,Z` under the original rules:

```text
Inner+ = Fun+(B-, Z-, Q_alpha+, C+)
Inner- = Fun-(B+, Z+, Q_alpha-, C-)
Outer+ = Fun+(A-, X-, Y+, Inner+)
Outer- = Fun-(A+, X+, Y-, Inner-)
```

The Function children are `(argument value, argument effect, result effect,
result value)`. The two result descents preserve the initial negative sign;
the argument descents reverse it. Omitted `Y` remains independent of
`Q_alpha`. Once the full pair forms, emit both ordinary formal constraints:

```text
Outer+ <: P_f             P_f <: Outer-
```

Retain all constraints, sharing and the full descriptor; do not check a
provider's complete future behavior during formation. The formal's own
computation-effect slot is distinct from X/Y/Z. Its separate source rule must
still run. No partial pair is a successful formal declaration.

## 3. Proposed elimination and authentic association

The new part requiring review is how permission associates with *actual*
constraint-derived contributions. Use a source derivation relation, not a
set of bare family names. A contribution occurrence `w` retains its original
provider/observation tuple, assignment, typed position, source origin and
lineage. Those fields keep their existing dependencies and quantifiers.
Different provider witnesses and different residual lineages stay distinct,
even when their effect rows or family/type points compare equal.

**N-Ingress (NEW).** Given an actual ordinary constraint derivation carrying
`w` into the negative projection at `D_alpha`'s exact Function position,
record `At(D_alpha,w,delta)` where `delta` is that derivation. This association
is introduced when a real lower reaches that incidence, including a future
lower. The formal declaration alone does not inhabit `At`. Existing lowers
must acquire/check the association as well as later lowers. For each member
`k`, applicability still requires the original family/type-argument relation;
name equality is insufficient. `At` does not assert that the contribution is
concrete, removable, or the only contribution at the row.

**N-Transport (NEW proof-relevant lifting requirement).** Every ordinary
constraint operation used below retains the authentic incidence derivation:

1. Function decomposition extends its structural position through the actual
   child comparison. It neither skips a child nor changes a provider.
2. Accumulation retains all contributions and their associations. Multiple
   derivations of the *same original contribution* may share storage; two
   distinct contributions cannot be identified because they share a row.
3. Install records the actual initializer value root. Capture/generalization
   retains the complete presentation rooted there, including original
   dependencies, shared variables, permission declarations and live associations.
4. Fresh use substitutes the entire presentation under its ordinary binder map.
   It keeps the original annotation occurrence, remaps the actual eligible
   variables and receiver scope, and adds the actual use instance. Non-generic
   rows remain shared according to the ordinary level rule.
5. Extrusion records actual value-associated parent/copy pairs. Qualifying
   intrusion equates only the pairs licensed by the selected Value-SCC rule,
   with propagation retained. Equality of row representatives never equates
   permission owners, provider witnesses, use instances or residual lineages.

These are proposed lifting obligations on ordinary operations, not an extra
solver that searches for a provider proof. A possible implementation retains
incidence evidence as each operation runs; its representation is unselected.
An inert bundle copy is insufficient.

There can be both a direct `provider -> P_f -> call` derivation and one through
the annotated pair. The candidate relation indexes the **same original
contribution occurrence** at its actual typed incidence, not its route count.
Evidence from the annotated incidence can be available to the corresponding
direct route only with an actual same-contribution derivation. There is no
family-wide propagation of permission. Completeness and scheduling of this
association, especially when a direct route reaches a consumer first, are
explicit obligations P3/P5 below; a missing association cannot be silently
treated as proof of either removal or permanent ineligibility.

**N-Subtract-Elim (NEW interface to an original consumer).** Inputs at the
consumer's original context are:

```text
actual demand d and actual constraint-derived input presentation L_d
actual local subtraction consumer h with its complete original typing
D_alpha, k, Permission(D_alpha,k), At(D_alpha,w,delta)
actual transport derivation from that incidence to w at d
original scope/eligibility evidence for this receiver at h
original consumer evidence selecting/removing this contribution of k
```

All operands belong to their original dependent scopes. The consumer evidence
includes whatever actual handler/matching conditions its original semantics
requires; this proposal cannot provide it by assuming successful matching.
The output is a residual contribution presentation indexed by
`(h,d,D_alpha,w,receiver/use-instance)` and its original dependencies. Remove
only the contribution that this evidence licenses. Preserve other contributions,
other effects, original checks, symbolic dependencies and the consumer's own
additional effects. Equal family points can therefore remain in the output.
With false/mismatching selection there is no corresponding removal; suspended
selection retains the request and dependencies without publishing a solved
residual. This says nothing about construction of the outside Catch input.

For an eligible concrete contributor, the residual calculation is ordinary
contribution-local subtraction. For unresolved inflow, retain a symbolic
subtraction constraint with the same operands and checks, rather than evaluating
it as empty. Every later lower is checked at that retained constraint. These
are required rules, not assertions that current code implements them. A port
has no unconditional `Q_alpha+ = residual` equation. Permission can persist
with no subtraction event at all.

## 4. Application to f() -> install(g) -> fresh local use -> g()

Use the actual two source calls `k1,k2`. Ordinary demand formation provides:

```text
P_f <: Fun-(U1, AE1, J1, R1)       C1 <: B1; J1 <: B1
R1 -- Install(g), Capture, FreshUse(u) --> G_u
G_u <: Fun-(U2, AE2, J2, R2)       C2 <: B2; J2 <: B2
```

These are independent call allocations; no equation `J1=J2` is generated by
nesting. With the proposed ordinary formal edges, Function propagation yields
`Y+ <: J1` and `Inner+ <: R1`. A provider lower constrained by `P_f <: Outer-`
reaches the inner negative effect position through ordinary result comparisons,
where N-Ingress records its authentic association. The positive projection
carries the same inflow through the returned `Inner+`, not through `Y+`.

Applying the proposed whole-presentation use map `rho_u` to the actual installed
`R1` gives a fresh instance of the latent inner Function at `G_u`. Decomposing
its comparison with the second demand yields `rho_u(Q_alpha+) <: J2` and
`rho_u(C+) <: R2`. N-Transport extends the same association derivation through
that route. A reached consumer of `J2` can then request N-Subtract-Elim with
that actual lower and that particular use; the first call's association and
one-shot `B1` cannot be substituted for these operands. Initializer effects
flow into the containing block separately and are never rerun by a fresh use.

This is a derivation **under the new proposed rules**, not a proof that current
source formation or native code emits them. It applies the proposal directly
to the parent's missing path, and identifies the checks needed at every step.
The receive fixture itself contains no Catch. Consequently this route creates
no actual subtraction residual in that fixture and determines no empty or
`ctrl`-containing final output from permission alone. `f0` is not applied to
receive in the pinned specimen and supplies no provider witness. The schema
retains arbitrary actual providers; it does not manufacture a closed example.

## 5. Native producer/consumer map and missing bridges

Direct evidence is read-only inspection of the contract-pinned files. Facts
about `shadow_apply` and `lib.rs` below are inherited from the pinned prior
construction audit, not fresh execution or new direct source dependencies.
Line locators are navigation aids at those snapshots.

| Owner | Existing evidence | Proposed responsibility / unproved bridge |
| --- | --- | --- |
| `source_annotation::parse_type_source`, `parse_row` (529–575) | Retains nested structure, row SourceNodeKey, concrete namespace identity and symbolic names | Supply D_alpha with complete resolved operands; no parse result proves At or subtraction |
| `candidate_effect::candidate_formal_pair` (1118 onward) | Rejects negative concrete row before returning recursive pair | Realize N-Port-Intro and preserve all ordinary source cases; merely removing the guard is insufficient |
| `candidate_formal_effect_port` (1145 onward) | Omitted and singleton symbolic ports share one row; positive concrete views have a separate path | Realize both negative projections, shared variables and active association; do not reuse positive Support as inflow |
| `candidate_signature_effect` (1626 onward) | Separately rejects negative concrete rows before tail/view formation | Corresponding negative constructor/consumer contract remains missing |
| `candidate_formal_annotation` (1191 onward) | Completes pair before slots 43/44 emit the ordinary two edges | Couple new formation to both real emitted constraints; keep complete Function contract |
| `candidate_formal_entry_annotation` | Root computation annotation keeps symbolic equality; concrete handling is left for integration | Distinct owner: no evidence that root handling constructs the nested returned-function interface |
| `candidate_source` Work::Install (823–845), Stage::PublishLocal (1311–1335) | One-shot initialization effects separately join block; actual exposed initializer is installed | Preserve actual R1 and B1 separation with the new interface |
| `candidate_scheme::install_candidate_local_term`, `route_candidate_local_run` | Records ValueRow root, local identity, boundary/capture region; captures and freshens actual use | No provider substitution; whole-presentation association completeness is unproved |
| `candidate_scheme::expand_node`, `prepare_candidate_fresh_use` | Captures all four Function children; freshens eligible rows with canonical sharing; copies original bundle occurrence/set vector | Copying existing bundles does not create or interpret negative incidence; new operands/checks need preservation proof |
| Function propagation in `lib.rs` (prior audit 12638–12675) | Argument children reverse; result children retain direction | Preserve N-Ingress/Transport and same-contribution association across all compared children, joins and equality |
| `shadow_apply::admit_candidate_fact` (prior audit 1558–1717) | Actual source recipe validates call operands and allocates distinct result/effect demands | Deliver actual J2 with reached association; neither negative Function shape nor successful call observation proves original typing |
| Effect subtraction consumer (concrete native symbol not established by these inputs) | Prior audit supplies no implemented negative residual consumer for this source | Luna must identify or authorize the owning consumer under an adopted contract; do not pretend a signature view is that consumer |

Thus **NO_SAFE_CODE_SLICE under this assignment**: the formal pair owner and
separate signature-effect owner both lack the adopted rule, and the residual
consumer correspondence is unsupplied. No code/test execution is needed to
establish these textual availability boundaries.

## 6. Discriminators and exact falsifiers

The following are future proof/source discriminators, not executed tests or
claimed source-qualified counterexamples. Each compares the same original
provider, assignment and complete input presentation unless it explicitly
varies the provider.

| Case | Required distinction | Falsifier |
| --- | --- | --- |
| Proven empty inflow, permission E | No E lower; an actual eligible subtraction has empty residual | Formation or elimination emits E from permission |
| No known lower but open x | Remain symbolic and accept/check later lowers | Treat x as proven empty or drop its deferred checks |
| Inflow E plus W, actual eligible E handling | Associated E removed; W and handler-generated effects survive | Negative interface rejects W merely because it is not E; or removal deletes W |
| Inflow E plus W, no actual subtraction | Permission alone removes nothing | Q+ is automatically E-free |
| Symbolic tail later receives W or E | Original tail sharing/checks remain; evaluate later contribution under same occurrence and consumer | Tail erased, future check skipped, or new permission invented |
| Providers p and q both contribute E; only p has relevant association | q's contribution remains even if flat support coincides | Removing all E after finding one permission witness |
| Same provider, distinct annotation/use/residual lineage | Retain each original occurrence and consumer dependency | Merge by provider ID or canonical row alone |
| First call E/W versus latent second-call effect | J1 stays separate from J2; initializer effect counted once | Attach Q directly to J1 or replay B1 at each use |
| Extruded copies later qualify for intrusion | Equate licensed type pairs, preserve original associations | SCC row equality becomes global annotation permission |
| Conservative non-source extra behavior | Keep complete original provider bound and checks | Define admissible providers only by emitted witness traces |

## 7. Obligations, alternatives and reuse

P1 — **Formation coverage**, formal annotation/Function source owner: give the
literal complete typed meaning of the two projections with the original
provider/future domains and prove the new descriptor clauses preserve them.
Cover mixed and multiple symbolic operands using their original `C_sym`, not
a parser limitation. The present proposal leaves that full application open.

P2 — **No inflow creation and uncapped input**, effect source owner: erasure of
permission adds no lower or closed upper bound; concrete-plus-symbolic sharing
preserves all prior constraints. Prove this for the ordinary accumulated graph,
not just the fresh empty graph. Unannotated and covariant cases retain their
selected meanings; no new negative permission leaks from them.

P3 — **Association completeness and locality**, Function propagation and
constraint owners: every real reached contribution receives exactly the
applicable original incidence evidence, including existing/future lowers,
alternative constraint routes, joins, aliases and repeated calls. Same-row
identity is insufficient. Prove compatibility with independent witnesses and
conservative provider extras; finite source traces are not the domain.

P4 — **Whole transport**, capture/generalization/extrusion/intrusion owners:
prove preservation of the complete dependent presentation and live checks on
all ordinary paths. Pure injective-renaming lemmas cannot justify identifying
extrusion parent/copy variables. Preserve the selected Value-SCC criterion.

P5 — **Residual consumer**, owning effect elimination source/native consumer:
construct its complete input judgment and prove contribution-local removal,
future-lower handling and correct suspension/invalidation when incidence or
matching is pending. The source consumer may not require an upfront solved
provider. Unknown evidence does not permit publishing a solved residual.

P6 — **Parent source/native correspondence**: show actual constructors emit
N-Port, both edges, ingress evidence and the actual R1/g/J2 chain, then prove
original soundness/natural-inference obligations. Review of this proposal is
not any of those results. F1/FK1 and other parent quantifiers remain untouched.

Candidate choice for review is the shared-row pair with occurrence-indexed
incidence and consumer-indexed residual above. Unresolved alternatives are:
(a) direct decorated ports versus an executable relation/view over those ports;
(b) retaining association at each constraint emission versus an equivalent
incremental derivation DAG with completeness proof; (c) the exact original
mixed/multiple-symbolic operand connection; and (d) consumer scheduling and
suspension for late association. These cannot be decided from existing bundle
copying. No representation is selected by this Draft.

Reject closed negative `{E}`, annotation-as-inflow, automatic subtraction on
call, family-wide deletion, independently chosen polar rows, bypassing local g,
and removal of ordinary propagation/levels/intrusion to simplify the proof.
Also reject treating the paired formal as a solved-provider precondition.

Reuse the prior 10/17 construction audit's exact formation obstruction and
native owner inventory; its author is `/root/receive_negative_pair_construction`.
Reuse annotation integration §§1–1.2 as policy and §§3–4's historical lemmas
only with their valid typed correspondence/profile premises. The 10/11 Oracle
singleton cancellation is only a same-binder direct-call result as reported by
that audit; it cannot supply the returned-function route. The 10/12 missing-POP
finding excludes importing a handler into receive. No historical note is
promoted by this proposal. The 10/05 reviewed conditional package preserves
same-provider whole bounds and independent witnesses (§§4–5), explicitly allows
conservative extras, and leaves concrete rules/source coverage open. It proves
neither the new ingress nor the native residual consumer. Historical effective
model identities and unstated author identities remain UNKNOWN.

## 8. Parent application, mutual TODOs and freeze

Before: formation of Q_alpha and lower/residual association had no proposed
owning source clause. After: N-Port/N-Function/N-Ingress/N-Transport/N-Subtract
specify a candidate constructor/consumer contract and a derivation of its use
at J2, with the exact semantic and implementation obligations above. The parent
is still OPEN. This is proposal progress, not a renamed conditional theorem
or proof closure.

- **NPAIR-REVIEW-20261017** — Luna assigns fresh compiler_referee/spec_auditor
  review to these frozen bytes and pins. Output: adjudicated P1–P6 and unresolved
  choices; falsifier: any introduced cap, fabricated inflow, lost source case,
  witness conflation or assumption of automatic handler evidence.
- **NPAIR-SOURCE-ADOPTION-20261017** — Luna routes the proposal for a later explicit user decision and records that decision; no adoption or dependent implementation proceeds without the user’s explicit approval.
  Inputs: reviewed proposal, remaining symbolic/consumer choices and original
  source signature. Output: exact adopted rule or retained OPEN decision.
- **NPAIR-NATIVE-TODO-20261017**, conditional only — after adoption and a new
  lease, identify the residual consumer and minimally observe actual negative
  pair generation, both formal edges, actual g fresh use and J2 association.
  Exact falsifier: guard bypass without the active consumer, no source-emitted
  association, loss of W/tail/future checks, J1/J2 or independent lineage merging.
  Any instrumentation is provisional and cannot establish all-path coverage.
  No such slice is authorized here.

Six stages completed: authority/pin reconciliation; source policy/parent audit;
proposed introduction; elimination and authentic route construction; native
mapping and falsifiers; freeze. Charge the full 900-second assignment cap
conservatively because active time was not continuously metered; zero remaining
budget. No tests, builds, compiler executions, solver probes, Git, network,
nested CLI or descendants. One initial hash command failed because `python`
was unavailable; `python3` performed file hashing only. Large combined reads
truncated; decisive policy clauses and native symbols were reread in bounded
excerpts. Checks: direct pin equality before reliance and at freeze, output
scope, Markdown fences and trailing whitespace. These checks are not independent
review or executable source evidence.

Only new/written paths are this file and
`tasks/agent-loop/inbox/20261017-negative-formal-pair-formation-proposal.md`.
No scratch paths. After final hashes the writer STOPs; no further work or writes
are claimed while review waits. Luna owns review, records and integration.

### Frozen direct dependency manifest

Hashes below are copied from the verified revision-1 contract. Provenance is
the named source's existing authorship; this author claims no authorship of
those dependencies. Native source author identity is not reconstructed.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-13-source-formal-ports-declaration-proposal.md` | `73003fc612fe4a9eb99c4c3915b6e4f53fcc25dce5679ef0a0d7820c18c396c7` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `questions/2026-10-17-receive-negative-formal-pair-formation/question.md` | `74eead9f668ed8a3b8439afaf6dd3ab5e2e94898a5d50e86086cdd30c183a176` |
| `questions/2026-10-17-receive-negative-formal-pair-formation/receipt.md` | `e46635701f5faa8e41e1cb62ee4052575d80e44d83be92e2ea485771398d99ef` |
| `questions/2026-10-17-receive-negative-formal-pair-formation/approved-answer.md` | `d3a51fbca88818d3e4146feb312dcfd693218f2949c6a1ca89f8682fdcf857d0` |
| `questions/2026-10-17-catch-exit-matcher-input-formation/question.md` | `343c3713a05418560888122c0c0d54358b45cc3c484b6cf0048baf16b75c58b7` |
| `questions/2026-10-17-catch-exit-matcher-input-formation/receipt.md` | `7e345361af200585fee97ae39642ef1c97069b4170c987066d25ee13e9a1a846` |
| `questions/2026-10-17-catch-exit-matcher-input-formation/approved-answer.md` | `655748936460bac40f757962552fd339320ebeeb583029afdc3d359b24d67108` |
| `notes/theory/2026-10-17-receive-negative-pair-construction.md` | `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
