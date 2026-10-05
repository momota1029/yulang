# Finite Value(Int) inlet: determined checks and first missing clause

Date: 2026-10-06 (assigned artifact date)
Status: frozen unreviewed research characterization; no adopted semantic rule
Baseline: `45b81a28d614f9f0a4d15c7a861347cb14506566`
Exclusive lease: this file only
Method: direct authority-to-judgment reconstruction; no transition model
Implementation authority: none

## 1. Objective and result

Determine what the approved Function-denotation and typed-core clauses fix for
the finite Int identity challenge before its first call, and isolate the first
undefined admission rule. This note does not repeat the identity execution
trace or a relation-projection counterexample.

The authoritative scalar check `Int <: Int` is determined: F5 §22 says
success. Typed-core §6 also determines the source-interface normalization
`Result(Value(Int)) = Comp(empty,Int)` and the actual unannotated parameter's
Value role. These facts do not make the whole-carrier admission check decidable
from the retained production evidence. The first missing clause interprets the
typed application incidence joining `Comp(empty,Int)` as a **whole carrier**
to `Value(Int)` as a **parameter/entry interface**, with its original paths,
receiver contract and shared constraints. The scalar result check is one
potential consequence of that clause, not its replacement.

This is a bounded characterization of the named committed sources. It proves
neither semantic undecidability nor that retained evidence cannot express the
clause. No finite executable oracle follows from the supplied authority, so no
model was built by assuming the very admission rule under investigation.

## 2. Verified authority and input identities

The approved answers were independently read at this baseline, including their
embedded d1 decisions and explicit approval provenance. Their blobs match the
previous assignment's six pinned authority/conditional-theorem inputs; the
earlier research note was not consumed as semantic authority.

| Committed input | Exact scope used | Git blob |
| --- | --- | --- |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | embedded decisions 1–5: all independent compatible punctured contexts, direct callable/whole-carrier holes, preserved evidence, no comparison premise, concrete rules open | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | embedded decisions 1–5: Option A, original complete `Rel_C` fiber, independent endpoint satisfaction/admission; rule completion unapproved | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | embedded decisions 1–4: Option 2 permits independently licensed non-source observations; grammar and production containment open | `fb4a169a2d748422490cc74c026338587290e90c` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §6, lines 303–425; §7, lines 520–637; §9, lines 912–956 | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | §2.2 active interpretation and provider-contract admission hypothesis | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | §3 Initial/Response/Resume/Future rules; §4 conditional Theorem C | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | candidate Function contract, lines 938–977: typed holes and open exact judgment | `841325b72ab797729b9f26d4569007ec6694c99b` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | Authoritative header; §1 application/effect boundary; §22 total same-kind algebra; §36 branded term lookup | `51d37bb77b069bfbcd8d7c320b7ced64f51c401b` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | §1 approved single inequality and endpoint-dependent resolution; full resolver still open | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| `notes/design/2026-10-04-production-callback-endpoint-generation-draft.md` | §3 whole source incidence/receipt owners and port projections; Draft crosswalk boundary | `25bd3cb4935f50e1b63f2bb1c04b4a9c7e4983c2` |

The last four blobs are separately verified inputs, not uncommitted
replacements. “Authoritative F5” applies within its stated closed-pure
production subset; it does not override the broader approved inlet domain.
The two computation/interface core documents remain Draft outside selected
user decisions. Research/design-authority/Git-concurrency rules read in the
preceding assignment continue to govern this new disjoint lease.

## 3. Finite challenge and determined subchecks

Fix the original assignment and binder tree `xi=(nu,K,D)`; do not replace its
constraints with `true`. Take an unannotated identity callable, its shared
parameter/result coordinate instantiated at Int, one supplied literal-Int
argument, and a direct terminal caller context with callable and whole-carrier
holes. The other environment is empty. Consider the empty interaction history
before invocation. No requests, raw handles or returned latent providers occur
in this finite witness. These restrictions define the examined challenge, not
the approved domain.

“Determined” below means the cited contract gives the particular answer or
source-construction shape. It is not a claim that a general effective
complete-observation decision procedure exists.

| Subcheck | What is fixed for this finite instance | What it does not establish |
| --- | --- | --- |
| Source parameter role | An ordinary unannotated `x` generates `P=Value(A)` and post-entry body binding `Value(A)`; substitute Int at the same coordinate (§6 parameter table). | Complete inlet compatibility, receiver path validity or boundary obligations. |
| Source argument interface | A supplied independently typed integer literal has `I_a=Value(Int)` under §6 literal rule; its normalized execution interface is `Comp(empty,Int)`. | That any particular production artifact interprets this normalized interface as an admitted whole carrier. |
| Scalar comparison | The same-kind F5 live endpoint pair `Int <: Int` succeeds by authoritative §22. | A comparison of the carrier with the parameter interface; semantic satisfaction of arbitrary original `K`. |
| Shared coordinate | F5 uses a common parameter/result binder and one instantiation map. On the stipulated Int instantiation, both occurrences name Int rather than independently chosen values. | The map from these type incidences to complete `Rel_C`, receiver paths or carrier dependencies. |
| Environment side conditions | Quantification over independently valid *other* free values has no value members in this empty-environment challenge. | Context/store/receiver well-formedness. An empty environment does not certify a complete machine state. |
| History side conditions | There is no response, handle reentry or future-provider extension to validate at the empty prefix. | The Initial admission clause. “No future step to check” is not evidence that the initial challenge is admitted. |
| Forbidden self-premise | The hole may be assigned a declared interface in the punctured derivation; the filling cannot be required to satisfy the pending Function comparison to admit that derivation (approved answers; Theorem C §3). | A complete definition of punctured typing or its production realization. |
| Role versus input effects | `Value(Int)` determines entry demand, not input purity (§9). | Either universal admission of all Int-returning carriers or a purity restriction inferred from this role. Other independently interpreted contracts can still matter. |
| Ground structural lookup | Branded `Term` lookup and same-kind endpoint ownership have fixed APIs/contracts under F5 §36/§22. | A typed receiver receipt, a source computation port or the semantic authority of a caller. Those are different judgments. |

If the supplied `nu` or original formulas do not validate the Int
instantiation, this particular challenge is not established. The note does not
solve an arbitrary `K` merely because the scalar endpoint is ground.

## 4. Exact first-open clause

There are two different roles in the examined judgment:

```text
input supplied by the caller: Result(I_a) = Comp(empty,Int), as whole carrier
interface owned by receiver:  P = Value(Int), as demand/rebind parameter
```

Typed-core §6 says the argument constraint relates the first to the second
with existing typed path/contract obligations. It gives no endpoint/path
translation that makes this particular incidence a specific ordinary
inequality with independently interpreted complete admission semantics.
The approved single-inequality decision supplies the resolution framework
once endpoints and their meanings are known; it does not supply that missing
translation.

Typed-core §7's proof-only checking fragment supplies exactly:

```text
Check(Value(A),Value(B))          requires VIncl(A,B)
Check(Computation(E,A),Computation(F,B)) requires CIncl(Comp(E,A),Comp(F,B)).
```

It has no `Check(Computation(empty,Int),Value(Int))` clause. This absence is a
boundary of that representation-preserving fragment, **not** a rejection rule
for applications. The uniform calling convention and actual receiver's entry
must relate carrier and parameter at the source application incidence. Turning
the carrier into its eventual Int before checking would drop the object whose
admission is being defined. Turning the parameter into `Comp(empty,Int)` by
fiat would add an unapproved interface translation.

Even a valid reflexive `VIncl(Int,Int)` proves only its stated same-value
proposition. An inlet lemma must connect it to the designated carrier path
while retaining the other complete-contract predicates. Ground endpoints make
that scalar subcheck easy; they do not eliminate the needed connecting rule.

### Minimal missing-clause table

| Missing clause | Required input/output and exact unresolved premise | Why the finite simplification leaves it open |
| --- | --- | --- |
| M1: carrier/parameter incidence interpretation | Interpret the source application obligation from whole `Result(I_a)`, actual `Value(Int)` parameter, designated demand/result paths and original `xi` into the existing single-inequality/evidence framework. State which endpoint constraints constrain the carrier and which constrain its demanded result. | `Int <: Int` fixes only a scalar pair; §6 supplies no total endpoint/path translation, and §7 has no cross-form check that can substitute for it. This is the first open premise. |
| M2: independent Initial/context validity | Specify the complete punctured-context/receiver/provider contract judgment for that incidence before filling-output satisfaction, using original paths, scope, lineage, state and authority. Establish its evidence formation or reconstruction from retained production inputs. | Empty other environment and empty history remove extensions, but leave receiver receipt/path/context obligations. Naming a hole declaration is not a proof of that complete context judgment. |
| M3: semantic activity and local coverage | Show the clauses of M1–M2 are active admission predicates at the retained production root, not explanatory provenance, and establish their exact coverage for this finite challenge without a pending-query premise. | Source-contracts §2.2 assumes active clauses; approved Option A and the current structural product do not prove this interpretation/conformance hypothesis. |

M1–M3 are proof/interpretation requirements, not proposed new solver atoms or
fields. Their table records the minimal residual for this empty-history ground
instance. An exhaustive production definition must additionally address
arbitrary contexts, operation responses, raw-handle reentry, latent returned
providers and Option 2 extras with their original dependencies. Closing only
this local instance would not close that larger gate.

## 5. Why no finite model is an admission oracle here

Several apparent alternative interpretations are already disallowed:
restricting to actually reached calls contradicts the inlet answer; requiring
the filling's successful Function comparison as a context premise contradicts
both admission decisions; inferring input purity from `Value(Int)`, Pure
introduction or printed `never` contradicts the selected role/entry treatment.
Checking only eventual Int omits the required whole carrier and evidence.
No new experiment is needed to re-establish those exclusions.

Two models that differ only by hand-supplying different M1 or M2 predicates
would measure those assumptions, not derive the accepted production answer.
Neither could be certified against a complete admission oracle that the
committed sources do not yet define. In particular, arbitrary admit/reject
tables for the finite ground challenge are not established authority-compliant
semantic alternatives. The authority does not license inventing them just
because its concrete clause is open.

Theorem C §3 *does* define a sufficient source-certificate Initial subcase:
a locally typed whole carrier supplies its result port, profile and path,
and its empty interaction prefix is admitted. Its independent punctured
certificate can be constructed with a declared hole, no filling-satisfaction
premise and an empty immutable environment. Transferring that result to this
production identity requires M1–M3 or a proved correspondence covering them;
the theorem's input decorations cannot be silently inferred from ground Int
endpoints. Option 2 also prevents treating that certificate grammar as an
exhaustive definition of all production members.

No executable finite model, mutations, seed sweep, range enumeration or
relation-projection counterexample was produced. This negative methodological
decision is deliberate: a supplied-transition checker would leave the first
open premise untouched.

## 6. Next exact proof obligation and claim boundary

The next local obligation is to give and justify an independently interpreted
judgment at the existing source/production incidence, schematically

```text
Initial_F(xi; punctured-context, actual-receiver,
          whole Comp(empty,Int) carrier, parameter Value(Int), retained-evidence),
```

whose clauses establish M1–M3 for the stipulated finite challenge. This name
is a proof locator, not a new semantic relation selected alongside `A <: B`.
The judgment must identify its original operands, show how the scalar
`Int <: Int` check is used, retain the carrier/path/receiver conditions and
explain its meaning before comparison. A failed clause must identify the
specific typed contract/path/state failure, not cite failure of the target
Function inequality.

If that construction needs a new durable interpretation rather than deriving
an already approved source clause, return the exact clause for the primary's
design/approval gate. Do not infer implementation authority or carrier
insufficiency. After local Initial coverage, the broader obligation remains
the same-fiber `D_checked subseteq D_actual` for every approved independent
context, followed separately by whole joint observation containment.

Claim classes: authoritative finite scalar-algebra fact; source-rule
construction shapes within the typed core's stated conditional scope;
bounded missing-clause characterization for production admission. No
unconditional production admission, decidability theorem, language
counterexample, implementation conformance or independently reviewed result
is claimed.

## 7. Checks, coverage, resources and frozen handoff

Checks were committed `git show BASE:path` reads restricted to §2's exact
sections, `rg -n` section locators, and a read-only Python
`git rev-parse BASE:path` pass verifying all ten blob identities. The six
original authority/core inputs matched their independently recorded pins.
The output lease did not exist before writing. Final dependency identities,
output hash and lease scope are rechecked at handoff. No worktree semantic
replacement, prior producer verdict or supplied toy-model result was used.

No independent semantic oracle was available. The source equations and
certificate conventions are common assumptions when comparing the candidate
inlet construction with Theorem C; deterministic reading/hash checks do not
certify those assumptions. Independent review is pending.

Coverage: one ground Value(Int) direct-call challenge with empty other
environment and empty history; ground scalar algebra; source-interface and
proof-only check boundaries; independent Initial/source-certificate and
production-interpretation distinction. No exhaustive source/package audit,
request trace, continuation model, higher-order or mutable-state analysis,
annotation/cast completeness, all-environment construction, complete
production membership or general solver decidability was attempted.

One producer, no child or heavyweight process, no tests/builds/formatters and
no Git mutation. Lightweight commands completed below one second each; CPU,
memory and aggregate reasoning wall time were not instrumented. No unfinished
enumeration or timed-out search is reported as complete. The note is frozen
before submission; prior artifact and all shared records remain untouched.

Recommended next action: the primary should adjudicate or commission the M1
whole-carrier/parameter incidence lemma, with explicit endpoint meanings and
the M2–M3 evidence/coverage requirements, before starting another finite
admission checker.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-function-int-inlet-missing-clause-table.md` only.
- Baseline SHA: `45b81a28d614f9f0a4d15c7a861347cb14506566`.
- Changed dependency hashes: none at baseline verification; all ten direct Git blobs are pinned in §2 and rechecked at handoff.
- Review status: frozen research-only bounded missing-clause characterization; unreviewed, no gate promotion.
- Checks already run: committed governing-section reads, ten dependency identity checks, output lease absence and final output/dependency scope/hash check; zero tests/builds/models.
- Proposed one-line commit message: `research: isolate ground Int Function inlet incidence clause`.
- Shared-record deltas deferred to primary/curator: distinguish the settled `Int <: Int` subcheck from unresolved M1 whole-carrier incidence; link this M1–M3 table from the Function admission dependency record. No task/index/theory/authority/question file was modified.
