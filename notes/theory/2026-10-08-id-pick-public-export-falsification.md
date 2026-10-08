# `id` / captured `pick`: public-export collisions and metadata minimality

Date: 2026-10-08
Status: Unreviewed bounded research; conditional discriminators only
Baseline: `d67fab6fbd81837a0be15b1cf35b06a6e1046f16`
Branch: `research/simple-sub-intrusion`
Lease: this file only; frozen on submission
Authority / production implementation / gate closure: none

## 1. Objective, method and result

Independently attack the sufficiency and minimality claims that could be made
for the committed [public candidate](2026-10-08-id-pick-transformed-public-export-candidate.md)
§§3–5. The method is information-collision analysis: hold every supplied
public/use input fixed, vary one unsupplied semantic premise, and ask whether
the required domain, observation or ordinary-query result changes. This is a
derivation, with small conditional semantic countermodels; no assumed-transition
checker, compiler execution or production counterexample is claimed.

**Result:** no source-admitted separator of the full candidate is established.
The candidate explicitly leaves the independent decoder/import/production/query
suppliers open, so the countermodels below attack dropping those suppliers,
not its stated conditional construction. Conversely, a separate result-selection
tag is redundant in a restricted, unambiguous two-template encoding. This is a
conditional minimality improvement, not public sufficiency or a new scheme rule.
The concrete source premise needed for an actual same-scheme separation remains
unproved: two admitted captured providers whose complete future-use contracts
differ in a distinction omitted by the proposed public import, with a typed
client that observes that distinction after the final projection.

## 2. Baseline and exact governing sections

Only pinned committed semantic bytes were read. Upcoming D0 producer output,
dirty coordination documents, and the pending readinvoke question are excluded.
The q1/a1 bundle matches the pinned bytes, its approved answer embeds the full
draft, and its receipt records integration and the limited approved scope.

| Source | Governing use |
| --- | --- |
| Root-policy `successor-generalize-root-policy/q1`, approved `a1`, decision items 1–5 and receipt | Actual target is a displayable transformed scheme plus necessary use information; hiding the full source relation under another name fails. Sufficiency, concrete representation and implementation remain open. |
| FVIEW §§1.1–2, 3, 5 | Public/source/internal layers; joint source incidences and `xi=(nu,K,D)`; actual callable role unchanged by formal-view inference; comparison-independent formation and separate production obligations. |
| Source-contracts §§2.2, 3.1–3.4 | Independently meaningful active descriptor; Name and aliases retain original providers; Value entry precedes body; independent initial/response/resumption/future-use admission; rigid imports and whole transport. |
| Source-contracts §3.7, especially its grammar and conditions 1–5 | Option 2 can have unanchored licensed extras; guard, primitives, exhaustive alternatives and abstract-provider domains are additional premises. |
| Source-contracts §5.3, Whole Function introduction; §9 | Actual-root `Direct` needs a local resolution-conformance rule; source emission and semantic inclusion do not imply it. |
| Charter Gates D–E; §§18, 21, 24 | Representation/implementation gates; fixed result forwarding; whole inert argument with actual Value entry force/rebind; ordinary unannotated receiver is Pure. |
| Source-result-synthesis §§1–4; typed core §6, §7 Function contracts, §9 Entry | Fresh ordinary parameter, Name forwarding, Value Result, complete invocation and preservation of actual entry. The typed-core construction remains conditional on typed primitive/path premises. |
| Source-generalization eligibility attack §§3–4.1 | Fresh local binder, fixed transitive capture closure, aligned source family; later equality constraints and full eligibility/principality remain open. |
| Principal-scheme acceptance criteria, expected examples and proof boundary | `id : 'a -> 'a`; unconstrained constant input can present as `any`; no permission to expose arbitrary value refinements or infer full principality from a skeleton. |
| Prior id descriptor bridge §§5–6 | S1–S6 are distinct suppliers. Uniform conventions and conservative result contracts are already possible routes, without a proved nonempty-alpha lower bound. |

## 3. Collision lemma and the required claim class

Let a source-free decoder receive

```text
I = (Sigma, alpha, external_public_contracts, xi, actual_call_inputs)
```

and use fixed uniform rules `Psi`. Let `T` be the promised complete decoded
contract or use judgment. If two admissible interpretations satisfy

```text
I_0 = I_1, Psi_0 = Psi_1, but T_0 != T_1,
```

no deterministic decoder of those inputs can return the required exact `T`
in both. Proof: its arguments are identical, hence so is its output. This
established mathematical lemma does not establish that such a pair exists
under the selected Yulang semantics. Every application below states its
additional premises.

For **safety containment**, exact inequality of contracts is insufficient:
one conservative output might be sound for both. An actual safety separator
needs a checked challenge outside one actual domain, or an actual observation
outside the checked guarantee, under the same whole scope and projection.
For **natural inference/principality**, a difference matters only if an approved
valid view must remain accepted and the common conservative output loses it.
Neither approved result-provider equality for every production member nor exact
execution precision is inferred from the expected repeated arrow.

Consequently a lower bound can establish that some distinguishing information
must be available, not that a particular field name, provider ID, source node,
or per-export tag is mandatory. Already supplied use inputs, complete imports,
or `Psi` can carry the information. The q1 target permits all three routes
provided use typing does not traverse the original definition.

## 4. A restricted tag-elimination derivation

Consider only the candidate's two source-base templates, with these additional
encoding hypotheses:

1. The complete pre-instantiation scheme is retained with binder scopes and
   sharing. No residual equation identifies the fresh local input binder with
   an outer endpoint, and normalization has not erased that distinction.
2. The only templates are a terminal formal projection and a terminal fixed
   outer-value projection. No annotation, body call, extra selected capture,
   mutable capture, adapter or result conversion is included.
3. Formal projection has no selected result import. Captured projection has
   exactly one fixed result import `ImportIncidence(0,C_z)`; its contract is
   independently supplied and its original incidence is preserved. This does
   not assume that `C_z` is already sufficient for all future uses.
4. The decoder already supplies the common typed receipt/Value-entry/rebind/
   Value-result/return schema. This is a conditional schema transformation,
   not a derivation of D0 or its descriptor typing.

Under these hypotheses the extra selector tag is reconstructible:

```text
forall a. a -> a, no selected result import
    => source-base result operand is the rebound formal

forall a. a -> B_z, exactly one selected rigid result import
    => source-base result operand is that import
```

The unique-import inventory also suffices to choose the second branch. One
uniform decoder can therefore remove `FormalResult` versus `FixedCapture(0)`
and regenerate the same operand/schema before running any descriptor or query
rule. Substitute that same operand into the common schema; every remaining
operand, ordered suffix and capture contract is identical. This proves exact
syntactic/source-base schema reconstruction within these hypotheses. It does
not prove descriptor activation, domain preservation, production membership,
generalization eligibility or public factorization.

At an individual instantiation `a := B_z`, both displayed arrows can be
`B_z -> B_z`. That is not an identical-input counterexample to this decoder:
the original scoped scheme and import inventory remain different. Conversely,
if residual equations, normalization, multiple imports, or a broader source
class erase those distinctions, this derivation stops. It gives no universal
tag-elimination rule. The principal constant presentation might eliminate the
unused input binder; it needs its own derivation and is not selected here.

This is a concrete challenge to asserting that the candidate's selector field
is *minimally necessary*. The committed candidate itself makes no such claim.

## 5. Small conditional separators and their missing source premises

### 5.1 Fixed import erased to its printed endpoint

The source rules establish the following source-base fact, relative to typed
outer bindings: `pick ignored = z` returns the original captured provider
after argument entry. Same endpoint `B` does not rewrite that provider. They
do not supply two particular admissible complete provider contracts at `B`.

For a conditional safety countermodel, supply two latent providers `p,q` at
the same printed endpoint `B`. After a common returning initial invocation,
let one future challenge `h` at the designated returned-provider port satisfy

```text
D_p = {h}, P_p(h) = {o};       D_q = empty.
checked result contract: D_C = {h}, P_C(h) = {o}.
```

Supply independently typed provider/context contracts realizing these sets;
the challenge is at its actual provider port, not an endpoint-ID equality
test. Assume the difference survives `Pi_xi`. A checked use of the returned
`p` satisfies the domain/inclusion conditions; the corresponding use of `q`
fails `D_C subseteq D_q`. Now mutate the import to retain only `B`, deleting
the fixed provider's future-use/domain incidence. Both public inputs become
`forall a. a -> B`, `FixedCapture(0)` and the same erased import. The collision
lemma proves that this mutated interface cannot decide both judgments.

This model uses two providers, one distinguishing future challenge and one
observation; two alternatives are needed for a collision. Empty versus singleton
future domains are enough for a domain separator. It is not a raw-source or
production witness. The missing source premise is the independently admitted
provider pair plus a typed projected distinguishing client, and the missing
representation premise is that the chosen public `C_z` actually erases that
distinction. The full candidate promises fixed complete capture contracts and
does not make that erasure. Thus this is a conditional lower bound on retained
contract information, not a falsification of its complete-import hypothesis.

An alias Name to `p` still names `p`; introducing a second spelling is not the
second provider needed above. A legitimate distinct instantiation event must
be independently established before using an instance `p'`. The local binder
of `pick` does not create that event. All subsequent invocations retain the
capture chosen at closure construction, including its transitive contract and
original `K,D`; copying only its endpoint is the attacked mutation.

### 5.2 Production completion unseen by source-base data

Fix a one-history domain `{h}`, one source-base observation `r`, a licensed
non-source observation `z != r`, one whole scope and `G={r,z}`. Require
independent typing/authority/bound certificates for `z`, and that its projected
observation differs from `r`. Consider two completions of the otherwise open
Option 2 grammar, with no rewrite edges:

```text
completion 0: R={r}, Z=empty, H_G(R)={r}
completion 1: R={r}, Z={z},   H_G(R)={r,z}.
```

Both satisfy the supplied positive grammar shape and retain the same source
base, printed scheme and selector. This applies source-contracts §3.7's
finite algebra to the decoder's information boundary; it does not claim a new
Yulang primitive or rerun that algebra as source evidence. It demonstrates
that source-base construction does not select the exhaustive production
interpretation. In particular, a source-tight decoded result cannot certify
complete containment of completion 1.

The pair is a **conditional semantic countermodel to deduction from the open
premises**, not two concurrent meanings of the already selected language.
If the global decoder rule `Psi` supplies and certifies one complete grammar,
the inputs differ at that supplier and the collision disappears. No per-export
`Z` metadata lower bound follows. Domain variation for abstract providers is
an additional independent obligation: this unchanged-domain pair proves none.
The named source blocker is a licensed actual production-only observation and
its complete guard/domain rule at the transformed root; these have not been
selected by the inspected documents. No second equivalent model is attempted.

### 5.3 Entry and receiver cannot be inferred from the repeated arrow

Charter §21 and source-result §3 already give the decorated-source entry
discriminator: a retained-computation constant body can return without running
a pure divergent carrier; an ordinary Value-entry constant body diverges first.
An actually requesting admitted carrier analogously exposes its request during
Value entry, even when the body returns a captured value without effects.
These are established reductions under the stated typed carrier premise,
already recorded in the governing sources; no new probe is claimed.

They forbid decoding the candidate's unused parameter as retained, or treating
body purity as complete-call purity. They do not force an entry tag here:
every callable in the assigned two-template envelope is actually Pure with
Value entry. Those rules can be uniform. Broader callable entry/role variation
must be represented by its actual contract or supplied use input before a
repeated erased arrow can support that larger class. The approved formal-view
inference for `apply` does not rewrite actual provider role.

Two actual calls can share the same export and have different receivers,
receipts, carriers and current configurations. Those coordinates are part of
`actual_call_inputs`; they are not identical inputs to the collision lemma.
Uniform rules must construct the invocation at that actual activation. Reusing
a static receiver identity or replaying receipt after resumption is a failure
of that construction, not evidence that each export needs a stored runtime
receiver or argument-effect tag.

### 5.4 A hidden-root success supplies no actual-root query rule

Hold semantic domains/observations fixed at a source root `s` and transformed
root `u`. A partial sound resolver may have a proof rule for a query at `s`
and no corresponding rule at `u`; rejection alone does not violate soundness.
This conditional resolver countermodel is permitted only in the unspecified
comparison fragment and does not override a mandated ordinary comparison.
It separates semantic/source correspondence from the local conformance
hypothesis of source-contracts §5.3. A `Direct(s,F)` certificate cannot be
submitted as `Direct(u,F)`. The complete clauses and one checked proof must
be exposed at `u` under the original incidence map.

The missing rule belongs to the uniform resolver/formation supplier. A selector
or imported provider identity cannot by itself create that rule. No executable
query counterexample is claimed: actual transformed root formation and local
resolution behavior remain unspecified in the inspected baseline.

## 6. Field classification and stopping conclusion

| Candidate information | What is supported by this attack |
| --- | --- |
| Scheme binder sharing/scope and fixed outer endpoints | Required by the selected source family. Concrete printed equality after instantiation does not preserve all those relationships by itself. |
| `FormalResult` / `FixedCapture(j)` selector | Useful construction certificate; redundant under §4's explicit restricted encoding hypotheses. Exact provider selection can be stronger than a conservative public contract requires. No universal necessity or sufficiency result. |
| Fixed import contract and incidence | Source-base capture preservation is required. If contracts vary as in §5.1, their distinguishable future-use information must occur somewhere among import, export, use inputs or uniform derivable rules. Raw identity tags or a particular encoding are not proved necessary. |
| Pure role, Value entry, Value Result, invocation suffix | Uniform rules suffice for the assigned source envelope, conditional on independent formation/typing. Unused input does not remove entry. |
| Actual receiver/receipt/current-state operands | Use-supplied dynamic coordinates; preserve them jointly. Their variation does not require per-export copies. |
| Option 2 guard, complete alternatives and provider domains | Must be independently supplied and certified. The source selector does not determine them; §5.2 gives no per-export size lower bound. |
| Actual-root ordinary query law | A formation/resolution rule and finite proof obligation, not implied by any selector tag or hidden-root success. |

There is no new raw-source-admitted counterexample, all-model impossibility
claim, alpha-size bound, complete public sufficiency proof, or gate closure.
Stop at the named missing premises above. Adding another transition checker
would leave them untouched. The best next action is to freeze one actual
source-free decoder with its import interface and complete root clauses, then
use §4 to remove only demonstrably redundant selector data and §5.1 to test
whether its chosen import retains every admission-live distinction. This is
a supplier/design review request to the primary, not semantic adoption here.

## 7. Checks, independence, resources and commit packet

Commands used: bounded `git show <baseline>:<path>` reads and section extraction,
read-only `git status`, `git rev-parse HEAD`, `git branch --show-current`, and
one Python SHA-256/current-byte comparison of the listed dependencies and
approved-draft embedding. Final document integrity checks are reported on return.
The initial dependency comparison found no changes and HEAD equaled the baseline.
Only this leased path is written. No Git mutations, children, shared-record
writes, questions writes, tests, builds, formatting or executable semantic probes.

There is no executable oracle, seed, enumeration range or mutation execution.
The logical mutations in §5 delete one named supplier or input distinction.
The collision lemma is independent of source transitions. Its Yulang applications
share selected entry/Name rules and the conditional typed primitive/transport
premises of the source package. The countermodels do not independently validate
source admission, `DescMem`, public-import sufficiency, Option 2 licensing or
ordinary query generation. The minimum finite sets are symbolic witness sizes,
not measured source or production coverage.

No numeric CPU/RAM/process/wall-time budget was supplied. Work uses serial
lightweight read/integrity processes and no heavy processes; each captured
read/hash command completed below one second. CPU time, peak RAM and total
research wall time are uninstrumented. No enumeration timed out or was omitted
after launch. General recursive SCCs, annotations, multiple captures, aliases
as a compiler fixture, legitimate distinct instance construction, adapters,
mutable state, raw `pick` acceptance, runtime observations and full principality
remain unverified.

SHA-256 of pinned direct dependencies:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `questions/2026-10-08-successor-generalize-root-policy/question.md` | `69f43d833a0237523c88a26125f3cf4878e599e38903f84b458d437da662072b` |
| `questions/2026-10-08-successor-generalize-root-policy/answer-draft.md` | `6234a26dd6491b67d92b3f86421160becf52779ef3188b12fbe49fa84c28bbed` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/theory/2026-10-08-id-pick-transformed-public-export-candidate.md` | `f940ae9bf9b01af471075477513e040821d8619cd12b9023d83e9302b467f5c3` |
| `notes/theory/2026-10-08-id-descriptor-source-bridge.md` | `dcc91b8cb958f68208b61f490b68cbc3d42318b65f14604b0ad80742b1798a10` |
| `notes/progress/2026-10-06-source-generalization-eligibility-attack.md` | `2445a67ab8ce3372e7acd62fd90d598ca1ea3bc92872ff9b8588f176fc077d3e` |
| `notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md` | `13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337` |

Commit packet:

- Exact leased paths: `notes/theory/2026-10-08-id-pick-public-export-falsification.md` only.
- Baseline SHA: `d67fab6fbd81837a0be15b1cf35b06a6e1046f16`.
- Changed dependency hashes: none at initial comparison; final recheck on return.
- Claim/review status: unreviewed conditional collision/minimality derivations;
  producer output, no independent review or authority claim.
- Checks already run: authority and receipt reads, dependency byte/hash equality,
  approved-draft embedding, read-only HEAD/branch/status; final document integrity
  results on return. No executable semantic checks, tests or builds.
- Proposed one-line research checkpoint message:
  `research: bound id and pick public export collisions and selector minimality`.
- Shared-record deltas intentionally left to primary/curator: optional link to
  this independent attack; retain all decoder/import/production/query gates;
  record selector redundancy only with §4's hypotheses and provider-domain
  separation only as conditional. No status promotion, semantic adoption or
  gate retirement is proposed.

Writing stops before frozen review submission.
