# `id` / captured `pick`: a transformed public export and its first supplier

Date: 2026-10-08
Status: Reviewed bounded conditional construction; research only
Baseline: `51714826c2a832471329d04600592476cbfa70b4`
Branch: `research/simple-sub-intrusion`
Lease: this new file only; frozen on submission
Reviewed-by: compiler_referee (conditional constructor and supplier boundary), spec_auditor (q1/public-target conformance)
Review result: no blocking, major, or minor findings within those scopes
Authority / semantic adoption / production implementation / gate closure: none

## 1. Objective, method and result

Construct a candidate actual public `Sigma + alpha` for ordinary `id x = x`
and resolved captured-name `pick ignored = z`, keeping source Lambda solely
as construction evidence. The method is constructor elimination at publication:
replace the resolved terminal Name by a finite result-selection schema, then
specify the interface a source-free use decoder would have to expose. This
extends the prior `id` bridge to a fixed external capture and identifies which
information belongs to the published scheme, an imported contract, or uniform
decoder rules. It does not repeat its conditional six-supplier theorem as a
new public-sufficiency proof.

**Result:** the selected source rules determine the endpoint family and a
source-base projection certificate for these two cases. A bounded candidate
export can contain a displayed arrow, a finite typed result-selection
certificate, and, for `pick`, one fixed imported public-contract incidence.
No proposed `alpha` is established sufficient or minimally necessary under
the selected semantics. The first missing supplier is an independently
meaningful formation/interpretation rule for the descriptor actually decoded
from this export. FVIEW §5 leaves such generation and conformance open;
source-contracts §2.2 explicitly adds active interpretation as a hypothesis.
The construction stops there. Later obligations are inventoried, not assumed
discharged to obtain a theorem.

## 2. Baseline and governing sections

All semantic dependencies below were checked against the pinned committed
bytes. Dirty task/design/index/theory coordination edits, the pending
`readinvoke-source-presentation` question, and remote-only `2ea53e3dd` are
excluded as premises. The integrated root-policy approval and receipt were
read first and match the baseline. The live index was used only as a locator.

| Source | Exact use |
| --- | --- |
| Root-policy q1/a1 approved answer, decision items 1–5, and receipt | Actual public target is transformed/displayable scheme plus only necessary use-time information; a renamed full relation fails. Sufficiency and concrete adoption remain open. |
| FVIEW §§1.1–5 | Public/internal/source distinction; jointly scoped source slots, paths, incidences and `xi=(nu,K,D)`; actual callable roles; comparison-independent admission; all proof gates retained. Neither `apply`'s provisional formal rule nor its annotation permission is generalized to these projections. |
| Source-contracts §§2–3.4, 3.7, 5.3 | Independently interpreted descriptor and active complete clauses; separate source/admission inventories; legal whole transport; exhaustive Option 2 grammar; actual-root finite query rule and explicit resolution-conformance hypothesis. This package is conditional, not adoption of its grammar or calculus. |
| Charter Gates D–E, §§18, 21, 24 | Representation selection follows coherent semantics; implementation requires separate approval; ordinary Pure introduction, Value entry force/rebind before the body, and preservation of latent returned values. |
| PG-1, source-generalization eligibility attack §§3–4.1 | Projection envelope, formal endpoint family, fixed outer capture closure, aligned source-kernel reconstruction; full eligibility and designated-export Direct remain open. |
| Source-result-synthesis §§2–3; typed-computation core §6 and §9 Function contracts | Fresh ordinary parameter, resolved Name forwarding, Value Result, whole argument, actual receiver entry and full invocation obligations. Core primitive/typed-path premises remain conditional. |
| Prior `id` descriptor-source bridge §§3–6 | S1/S2 descriptor supplier, S3/S4 domain/production supplier, separate S6 query; no demonstrated per-export metadata lower bound. |
| Principal-scheme acceptance criteria, expected examples and proof boundary | `id : 'a -> 'a` is an expected public presentation; value skeleton does not prove coupled principality. The constant-function `any` presentation cautions against claiming maximality for `pick`'s template binder. |

## 3. Explicit envelope and construction derivation

Hypotheses for this bounded source-base result: finite, immutable, nonrecursive,
ordinary unannotated value-parameter Lambda outside a callback position; one
resolved terminal Name; no body Call, handler, adapter, mutable capture,
existential opening or explicit computation annotation. For `pick`, resolution
supplies the existing outer binding `Gamma(z)=Value(B_z)` and its original
provider/dependency incidence. This is a decorated source hypothesis. **No
committed raw-source `pick` fixture or compiler acceptance run is supplied by
this assignment or claimed by this note.** Outer values may have latent
providers. Later argument carriers may effect, suspend or diverge.

Parameter registration allocates a fresh inferred value endpoint `a` and
selects `Value(a)`. The ordinary callable has actual Pure role; Value entry
receives the inert whole argument and forces/rebinds it once in that receiver
activation before executing the body. Name and Result inversion give:

```text
id:    Gamma_body(x)       = Value(a)
       Synth(name x)      = Value(a)
       Result(Value(a))   = Comp(empty,a)

pick:  Gamma_body(ignored) = Value(a)
       Gamma_body(z)      = Value(B_z), at its fixed outer binding
       Synth(name z)      = Value(B_z)
       Result(Value(B_z)) = Comp(empty,B_z)
```

The body result is pure Value introduction; this is not an empty-effect or
termination claim about complete invocation. At construction, terminal-name
resolution additionally identifies the returned provider: the rebound formal
for `id`, the fixed captured provider for `pick`. Repeated `a` alone proves
type sharing, not provider identity. Lookup/return consumes no latent provider.

Relative to the independently typed primitive/transport contracts, eliminate
the Name occurrence to obtain these two *source-base* schemas:

```text
id:   Receipt(actual_receiver, whole_argument);
      Force(argument) >>= (v,current_configuration).
        Rebind(formal,v); ValueResult(v); InvocationReturn

pick: Receipt(actual_receiver, whole_argument);
      Force(argument) >>= (v,current_configuration).
        Rebind(ignored,v); ValueResult(captured_z); InvocationReturn
```

These symbols refer to uniform typed primitive contracts, not source nodes.
The source derivation proves which result operand is selected at publication.
For Return, substitute the original rebound or captured value into the suffix.
For Request, the existing Bind law preserves its original witness/raw
continuation and appends that same suffix at current resumed configuration;
it does not replay Receipt. Finite-prefix induction preserves this substitution.
Divergence before rebind provides no later body Return. Returned-provider
transport remains governed by the original typed contract. This is the
bounded conditional source-base rewrite lemma; it does not establish the
ordinary descriptor conjunct, complete admission, or production membership.

PG-1 reconstructs aligned source views by substituting `a := T` once around
the whole Lambda family. `id`'s input/body/result all receive that substitution.
`pick`'s input receives it; `B_z` and every outer dependency remain fixed.
If later source constraints equate `a` with an outer coordinate, the equation
must remain. This derives a template candidate, not semantic eligibility or
an irredundant principal binder set.

## 4. Proposed actual public object and use interface

The following is a candidate interface, not a selected representation:

```text
id:   Sigma_id   = forall a. a -> a
      alpha_id   = TypedSelection(FormalResult, formal/result port schema)

pick: Sigma_pick = forall a. a -> B_z
      alpha_pick = TypedSelection(FixedCapture(j), result port schema)
                   + ImportIncidence(j, original public contract C_z)
```

`B_z` is a printable monomorphic outer endpoint in this publication; its
original scope is not moved into the `forall a`. The scheme records type
sharing and scope. `alpha` records only a finite typed selection/incidence,
not a Lambda, source pointer, arbitrary predicate, full relation program,
history table, or a handle whose use implementation traverses source.
`C_z` must be an independently supplied external **public** contract; renaming
the full captured source relation `C_z` would also fail the root-policy goal.
No already sufficient external public contract is assumed here.

Each selection field has a proposed use: select the provider operand of the
decoder's source-base ValueResult schema. The import incidence associates the
selected captured output with its actual fixed contract, rather than inventing
a fresh result provider with matching type. These uses justify investigating
the fields; they do not prove that all are necessary for approved ordinary
typing. A general conservative arrow may forget exact source-base provider
identity. A uniform decoder may supply incidence without per-export metadata.
Neither route has been proved sufficient here. Selection cannot in general
be inferred solely from a displayed arrow: the same arrow may describe other
implementations. Source construction can furnish the proposed certificate.

Pure role, Value entry, actual receipt, and Value-result consumer can be
uniform rules of the projection decoder rather than duplicated tags in every
export. This decoder envelope must be distinguished internally from other
source entry forms; no new user-visible annotation or acceptance restriction
is proposed. Selecting a universal arrow interpretation remains a design gate.
The candidate `forall a. a -> B_z` records PG-1's family. It does not establish
whether unused input normalizes to `any -> B_z` in a principal public scheme.

Use would call the following interface:

```text
Decode(Sigma, alpha, external_public_contracts, xi, actual_call_inputs)
  -> actual_descriptor r_u
     + active Admission(r_u)
     + complete Membership(r_u), including DescMem and production alternatives
     + finite ordinary-query operands at r_u
```

Freshening acts once on eligible local binders and port/incidence operands;
external rigid imports and original capture identity stay fixed. Any uniform
graft or hiding needs its whole original-scope certificate. The caller supplies
the actual argument/receiver/receipt and independent typed context. Its
constraints and one `Direct(r_u,F_use)` are conjoined at this actual descriptor;
only then is the original whole projection `Pi_xi` applied. No query uses a
retained source Lambda as a substitute root.

### Fixed capture contract semantics

For `pick`, the actual immutable closure holds the same captured value, and
its type-use import fixes the corresponding original public contract and
transitive dependency closure. Subsequent uses do not independently freshen
the outer result endpoint, provider identity, challenge domain, capture
permission, role/entry, future input interfaces, operation-instance witnesses,
continuations, scopes or `K,D`. If the outer binding originally has legitimate
instantiation events, their source-established instances must be supplied by
the import contract; this local `forall a` does not create those events.

This describes preservation of the source-selected fixed capture. It does not
require exact source-execution membership for every conservative observation.
Source-contracts §4's allowance variation leaves the capture contract and
other non-coverage fields fixed; it cannot manufacture a new capture grant by
widening effects. `C_z` needs a canonical finite public interface sufficient
for these checks. Its construction and sufficiency are another unsupplied
interface after the first decoder blocker, not an invitation to retain the
entire source relation inside the import.

## 5. First blocker and complete obligation inventory

**First missing supplier D0:** a legal rule defining the independently
interpreted ordinary descriptor produced by `Decode(Sigma,alpha,...)`, and
exposing its semantically active clauses at that same root. FVIEW specifies
source direction and preservation, not this rule. Source-contracts §2.2 assumes
the active interpretation and independently meaningful `DescMem`; it does not
derive them from printing an arrow. The prior bridge likewise lists this as
S1/S2. No semantic public-sufficiency theorem is claimed by adding D0 as a
hypothesis here. A further checker implementing D0's assumed transitions would
only verify consistency with those assumptions.

The exact supplier interface is the displayed `Decode` signature plus a
descriptor-formation derivation at `r_u`, an independently justified local
typing/activation lemma for each schema leaf, and explicit exhaustive
admission/membership rules. **Falsifier:** a source-base witness accepted by
the independent typed constructor derivation that is rejected by
`DescMem(r_u,...)`, or a descriptor whose alleged active clauses are only
metadata. Four correctly printed ports do not exclude either failure.

The following remain obligations for that supplier and later work, rather
than hidden premises discharged in this note:

| Obligation | Exact required evidence / failure condition |
| --- | --- |
| Independent admission | Initial typed punctured context with actual receiver/receipt/whole argument/result path and joint dependencies; responses at the exposed original operation witness and current configuration; original raw resumption; every finite future use at each returned provider's designated typed port. Include admitted divergent carriers. `Direct` success, `never` spelling, and absence of Return cannot define admission. `pick` also needs the fixed captured provider's reachable domains. |
| Source-base membership | Constructor/primitive lemmas prove every emitted observation satisfies the actual ordinary descriptor and scope/authority predicates. Preserve current resumed state, original suffix and returned-provider transport. Defining `DescMem` as the projection wire's image does not supply an independent lemma. |
| Complete Option 2 membership | Account for every alternative of the actual production root, including unanchored extras and any introduced providers. Source-contracts §3.7's candidate `H_G(R)` uses independently licensed `W,Z`, a complete guard `G`, all typed operands, original bounds and `K,D`; no actual primitives/grammar are selected by that note. A source-base-only proof or setting `W=Z=empty` does not prove conformance to an unspecified production root. |
| Option 2 domains / transport | Any abstract provider or change to admission-live coordinates needs its own domain certificate. Positivity proves no domain law. Freshen source/guard/abstract/primitive operands uniformly; retain rigid imports and joint scopes; final guard may not grant capture authority from row-family equality. A result-selection source certificate need not constrain every Option 2 member to exact source provider identity. The actual complete guard must decide that. |
| Production conformance | At the transformed export, establish comparison-independent complete domains and `D_C(xi) subseteq D_A(xi)`; for every `c` in `D_C`, establish `P_A(c;xi) subseteq P_C(c;xi)`, including production-only observations. Source correspondence alone proves neither. Equality of complete exports would require both directions of the relevant grammar/guard argument; one-way `Le` yields only the stated containment. |
| Generalize / instantiate | Prove local eligibility, legal binder placement, one action across all shared operands, fixed external capture closure and any original-scope joint hiding/admission certificate. PG-1 reconstructs aligned source kernels; it does not prove transformed public eligibility. |
| Actual ordinary Direct | Source-contracts §5.3's conditional sufficient rule requires same Function head, actual role/entry/consumer and fixed non-coverage interface, finite `Eq` of complete admission and `Le` of complete membership including descriptor/residuals/all alternatives, under one scope/incidence map. The actual resolver must expose and accept these operands at `r_u`. This local resolution-conformance supplier is independent of source generation. Semantic inclusion, successful child queries, or a query at a hidden source root cannot replace it. |
| Natural inference / principality | Independently define the required valid-view class and prove its factorization at the transformed export with ordinary query evidence. PG-1 kernel-aligned views, output displayability, or source reconstruction cannot prove arbitrary public-view coverage, maximality, or discovery of the query certificates. Approved ordinary behavior and FVIEW's role/annotation distinctions remain obligations. |

There is no complete production membership grammar, descriptor decoder,
external capture summary sufficiency proof or accepted Direct supplier in
the named authorities that this bounded inspection can use to close these
rows. This is a finding about the inspected suppliers, not an exhaustive
repository absence claim. Gates D–E and all relevant proof gates remain open.

## 6. Coverage, independence, checks and resources

Coverage: two resolved decorated source projections; no alias chain added;
arbitrary admitted carriers/finite histories appear only in the conditional
source-base derivation. No executable oracle, random seeds, search ranges,
mutation executions, compiler runs, tests, builds or formatting. This method
uses the selected source rules and reviewed typed primitive/Bind laws as
shared assumptions. It does not independently validate those laws or D0.
The prior bridge already leaves D0 open; this note supplies the captured-import
interface and stops rather than running another equivalent assumed-transition
probe. The blocker concerns actual compiler safety/natural use, while source
pointer reconstruction would be avoidable debt; no gate is reclassified here.

The falsifier in §5 is a specification discriminator, not an executed witness
or proof that it occurs. Replacing the fixed capture by a freshly instantiated
matching type, skipping unused-argument entry, or traversing a source relation
at use are named candidate failures; this note does not rerun their existing
toy mutations or claim new falsification evidence for them.

Documentary commands: bounded `git show`, `sed`, `rg`, read-only HEAD/status
inspection and SHA-256 comparison with pinned bytes. Final integrity check
checks this file's headings, local Markdown links, trailing whitespace, exact
lease status, baseline and dependencies. These are document checks, not
semantic verification. Only this leased file is written; no children, Git
mutations, shared-file or question writes. The primary owns review/integration.

No numeric process/CPU/RAM/wall-time budget was supplied. Work used lightweight
read commands and one short integrity process, with no heavy process. CPU time,
peak RAM and total research wall time were not instrumented; individual captured
commands completed below one second. No incomplete enumeration exists. Raw
source acceptance of `pick`, recursive SCCs, aliases, explicit annotations,
callbacks, adapters, mutable captures, full production semantics and all-view
principality remain unverified.

Recommended next action: freeze one proposed source-free decoder rule for the
actual public projection export, expose its ordinary descriptor clauses and
typed external-import interface, then obtain independent review of D0 before
another proof assumes it. Keep production/domain/query/principality suppliers
explicitly separate.

## 7. Dependency snapshot and commit packet

SHA-256 of direct committed dependencies; final recheck is reported on return.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `rules/orchestration-budget.md` | `32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/progress/2026-10-06-source-generalization-eligibility-attack.md` | `2445a67ab8ce3372e7acd62fd90d598ca1ea3bc92872ff9b8588f176fc077d3e` |
| `notes/theory/2026-10-08-id-descriptor-source-bridge.md` | `dcc91b8cb958f68208b61f490b68cbc3d42318b65f14604b0ad80742b1798a10` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md` | `13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337` |

- Exact leased/changed path: `notes/theory/2026-10-08-id-pick-transformed-public-export-candidate.md`.
- Baseline SHA: `51714826c2a832471329d04600592476cbfa70b4`.
- Changed dependency hashes: none at initial comparison; final comparison in return packet.
- Claim/review status: independently reviewed bounded conditional source-base rewrite and candidate public interface; no transformed sufficiency, adoption or gate closure.
- Checks already run: authority/receipt reads, pinned-byte/hash comparisons, read-only baseline/status inspection; final document integrity results in return packet. No tests/builds/semantic executions.
- Proposed one-line research checkpoint message: `research: bound id and captured pick public export decoder interface`.
- Shared-record deltas intentionally left to primary/curator: link this candidate if useful; record D0 as the first public decoder supplier and `C_z` as a later independent import-summary obligation; retain actual-root Direct, Option 2 production and all-view principality gates. No task/index/design/ledger/question status change is made or proposed as closure.

Writing stops before frozen review submission.
