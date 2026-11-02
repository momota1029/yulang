> **Withdrawn as premature — 2026-11-03.** The A/B/C decision below is not
> requested. The user questioned the premise that a Union branch is selected.
> Independent source review found that the Union at issue is relational proof
> notation, and the Bool tag is derivation provenance, not a runtime choice or
> evidence of disjoint alternatives. The missing child/result packet
> correspondence is a proof-construction obligation; it has not been shown to
> require new language semantics. See
> `tasks/agent-loop/history/20261103-union-question-premise-review.md`.
> The R159 bridge remains open. The original question is retained below as
> historical context, not an authoritative semantic decision.

# Original typed Union branch/result rule

Question ID: `original-typed-union-rule`
Question revision: `q1`
Predecessor/history: R163 `EFFECT-PERMISSION-TYPED-ALT` and R164 `EFFECT-PERMISSION-ORIGINAL-TYPED-UNION`; no prior question bundle found for this exact decision
Original worktree: `/home/momota1029/rust/yulang`
Branch: `yulang3`
Current source revision: `92b7b726e35476254b4772dc59a7881667e65916`
Task/thread locator: unavailable; no stable conversation locator is exposed

## Governing premises and frozen evidence

The original parent remains `YulangClosure.SourceAppAdmissionR159.app_admission_iff`; R159's quantifiers, source domain, annotations, Local premises, finite Checking judgments, arbitrary operands and shared occurrence/data/extension remain fixed. Independent P and A and the production gates remain open.

Relevant frozen inputs:

- R164 contract r2: `tasks/agent-loop/sprints/effect-permission-original-typed-union-20261102-r164.md`, SHA-256 `fbd0895f1cb48f1741ac8c438659dab32d2133c48291df833bbcd35aa439db48`.
- R164 reviewed source analysis: `notes/theory/2026-11-02-original-typed-union-r164.md`, SHA-256 `07bddab9fb32bbc54fe069e3148859930a439d5a0adec71a9cf1095a83a0e6a6`.
- R164 source handoff: `tasks/agent-loop/inbox/effect-permission-original-typed-union-r164-source.md`, SHA-256 `22be5539e2c3aa3e42f98166e83e5dbabd3a8b1d18f67b84dbafda7eaeb32049`.
- R164 independent review: `tasks/agent-loop/history/effect-permission-original-typed-union-r164-review.md`, SHA-256 `ff32a65fc351eba62e74fe834542ef1dd292aa4b07514cc3855ae9c22864b182`.
- R164 Lean stop module: `notes/theory/lean/YulangClosure/OriginalTypedUnionR164.lean`, SHA-256 `0b5eced7c0ae575d07accc3c94d144792b09a08de08455a4f678b2f46566fc7d`.
- Generic relation semantics, source-contracts §2.1: `notes/design/2026-10-05-source-contracts-and-common-allowance.md`, SHA-256 `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
- IF constructors §3.2: `notes/theory/2026-10-08-call-source-interface-construction.md`, SHA-256 `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`.
- Native signature authority §§2–5: `notes/design/2026-10-08-native-signature-formation-definition.md`, SHA-256 `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`.
- Incidence construction §§2–8: `notes/theory/2026-10-08-source-signature-incidence-construction.md`, SHA-256 `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`.

## Requested decision

Identify the original typed rule or operator contract that defines how an actually selected Union branch relates to the original result telescope, including its dependent field action; or explicitly authorize drafting a new semantic rule for independent design review.

The decision is needed because the selected contracts currently say:

- generic `Union` is one alternative on an original whole tuple;
- IF retains both branch interfaces, the original result interface and tagged branch-to-result clauses, while contextual inclusion alone does not assert a satisfying map;
- incidence §3.4 requires an actual selected branch/result relation and dependent governed-field equations, but the audited sources do not provide their constructor; and
- Lean `Relations.alternative` consumes a supplied relation, while its projection transports an already licensed child field without proving that it is a governed field of the original result.

## Choices and consequences

### A. Locate an existing original rule

Name the exact authoritative source rule and its version/section. It must give the premises for both complete branch telescopes and the original result telescope, the selected branch witness, the branch-to-result relation, and the dependent field equations. This would preserve current semantics if those equations are already specified. A pointer to the generic whole-tuple alternative is insufficient.

### B. Authorize a new Union semantic rule for design review

Authorize a separate proposal only. The proposal must state, for each selected branch `b`, the complete typed premises and a field equation of the form

```text
read_result(j, whole, result_witness)
  = transport_b,j(read_branch(k, whole, branch_witness))
```

for every governed result field, with actual dependent types, transports and derivations. It must also specify how both branch schemas and the unchanged result telescope are retained; how original owner and route are preserved; how shared coordinates retain their equations; and why empty/unselected fibers gain no license. This option does not approve an implementation or close P/A. The exact equations remain undecided until a proposal is reviewed and expressly approved.

### C. Decline a Union semantic rule

Keep the typed-Union bridge blocked and leave the original R159 parent open at this source domain. No implementation or proof may assume the missing correspondence. Other work may resume only after a separate goal/scope decision.

## Scope affected

Blocked: instantiate `Relations.alternative`, derive an authentic selected-branch result-field map, apply the guarded Alt constructor, and any Rust implementation or consumer claim that requires those fields.

No impact on already reviewed conditional Alt projection/insertion results, the five-owner Rust `NO_SAFE_CODE_SLICE` map, or the separate open P/A and production obligations. No code, Lean axiom, expected output or tests are changed by choosing A or approving only a proposal under B.

Requested answer: choose A and supply the exact existing source locator/equations; choose B to authorize a proposal (not its adoption); or choose C. A general instruction to continue does not determine the missing field equations.
