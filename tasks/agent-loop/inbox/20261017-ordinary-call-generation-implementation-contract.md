# Frozen Luna implementation-recipe handoff

Sprint-ID: `ordinary-call-original-generation-20261017`  
Contract revision: 2  
Contract SHA-256: `a1a409b84b5f9750266eea3790a9e098fce8af32e30348f17ee2d1ac1ffb1c21`  
Assignment-ID: `/root/ordinary_call_generation_implementation_recipe`  
Handoff revision: **1**  
Parent gate: original Simple-sub inference/execution theorem; original A/B
claims, quantifiers, source domain and source/native correspondence unchanged  
Baseline: `0717a882c`

## Worker and outputs

Role: Luna/high implementation/source recipe author  
Requested model/effort: `gpt-6-luna` / high  
Observed effective model/effort: UNKNOWN / UNKNOWN  
Session: current session; direct primary task and rev2 SHA acknowledgement  
Authors/contributors: `/root/ordinary_call_generation_implementation_recipe`;
no descendants  
Exact leased paths:

- `notes/design/2026-10-17-ordinary-call-generation-implementation-contract.md`
- `tasks/agent-loop/inbox/20261017-ordinary-call-generation-implementation-contract.md`

No compiler or test paths were leased. No code/tests/Cargo/build/probe/
formatter/Git operation was run. No scratch or generated paths were created.

## Frozen evidence and outcome

Recipe SHA-256:
`d1be33f49459fa6539aebf9e80fd213ab3dccb64fa8cfe56749563d3609c8f5b`  
Original-generation proof SHA-256:
`bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab`  
Proof handoff revision 1 SHA-256:
`1ff0c3dc71c4b7e09de5e00ff47b158627cc67320d29d820d38d76ed330b98d3`  
Spec/conformance review: CLEAN within the conditional/unadopted scope.  
Compiler/source-owner review: CLEAN within the conditional/unadopted scope.

Fixed source: `my id x = x; my answer = id 0`.

Outcome class: owner-mapped implementation recipe with one narrow,
provisional candidate source-evidence code slice. The current source producer
already retains the module Name, Lambda/formal, literal, Apply and candidate
ports; `Action::Module` routes the module use; candidate Apply admission forms
and propagates a four-port demand; candidate observations expose the source
call, fresh-use observation and export. The candidate graph is not runtime
execution or original source typing.

Original theorem conditions closed: **0**. There is no authentic original
`e_c`, no O0 application/substitution into Code-Call, and no production
promotion. The proof's `Gen-ModuleName-Literal*` remains a conditional,
unadopted formation proposal.

## Exact future code slice and falsifier

Safe only under a new reviewed source lease. Minimum paths:

- `crates/yu-solver/src/candidate_call.rs`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`

Add a borrowed exact `ModuleDef` callee observation to `CandidateSourceCall`
and expose the already unresolved module source typing/admission and module
receiving/export obligations as pending suppliers for that direct callee.
Add a vertical candidate test for the fixed source: actual `id` ModuleDef
callee; actual Integer `0` argument; no formal registration; original Call,
whole-carrier, complete-result and module suppliers still pending; no candidate
conflicts; candidate fresh-use observed for the callee; nonempty `answer`
candidate export. Test success means candidate-source evidence only, never
source admission, authentic original Call formation or execution.

Falsifiers: target resolves to anything except actual module `id`; formal and
module declarations/roots are conflated; argument ceases to be the actual
literal; source occurrence/native ports fail to agree; module fresh use or
candidate export fails; or any original/module supplier disappears before an
authentic owner supplies it. Cleanup owner: Luna removes this candidate-only
accessor/supplier instrumentation when an authentic original producer
supersedes it, or when the proposal is declined. Keep canonical unresolved
premises until their owners derive them.

No code lease is active. `candidate_source.rs`, `candidate_scheme.rs`,
`shadow_apply.rs` and `lib.rs` need no edit for this observation-only slice;
their current owners already generate Apply/module inputs, route module uses,
propagate candidate pairs and expose candidate consumers. The actual runtime
executor remains outside this path. If the focused regression falsifies any
one of those stages, return that owner-specific blocker to Luna before
expanding the lease.

## Source-to-consumer mapping and open owner TODOs

```text
source Lambda/formal + module Name(id) + Integer literal 0
  -> LambdaRecipe / formal table; separate PendingDefinitionUse + Action::Module
  -> ApplySourceInput + CandidateRelation::Apply
  -> module-use route in candidate_scheme/lib.rs
  -> candidate negative Function demand and callee <: demand in lib.rs
  -> candidate propagation, borrowed source_call, candidate fresh_use/export
```

The mapping is for candidate implementation only. The original path still
stops at these owner-specific proof inputs:

- `MODULE-DECL-USE-SCOPE`: Source Generalize/FinalRoot and actual module
  registration/reference owner must supply one complete whole-tuple source
  use map with the fixed provider and anchors. Candidate routing/fresh use is
  insufficient.
- `MODULE-CALL-SIGNATURE-APPLICATION`: original Application/Call owner must
  supply the full dependent telescope, all guards/carrier/arms/result
  incidences, unsolved conjunction and authentic occurrence before
  satisfaction. Candidate `admit_candidate_fact` is not that producer.
- `MODULE-GENCALL-ORIGINAL-EMBED`: after those owners and any separately
  authorized adoption, embed the proposed constructors in the original family
  and apply O0 to authentic `e_c`, then substitute into Code-Call.

Literal emission remains only the original whole-argument conjunct after its
real demand/reification premises. The native ID result does not identify the
actual source root. Rejected shortcuts include Name/Name Gen-Call-0,
formal-callee Gen-Call-Syntax, endpoint agreement, candidate/native facts,
O0 without `e_c`, and withdrawn Simple-sub bypasses.

The proposed observation is O(1) per call and adds no per-call storage; the
static pending-supplier iterator adds a constant number of items. No
asymptotic change is needed for this slice. If a later authorized producer
joins U module uses with C Calls, an expected O(U+C) keyed pass with O(U)
index space is the default; repeated scans cost O(U*C) and less index space.
The user's complexity clarification permits either measured tradeoff, but
neither can alter admission or supply missing semantic judgments.

No semantic selection is made. The possible formation extension remains
unadopted because its original-family embedding and consumer acceptance are
unproved. All parent gates, including F1/FK1, N-Transport, complete Call
satisfaction, source/native adequacy, soundness, principality and termination,
remain open.

## Budgets and cessation

Author cap: 720 seconds. Runtime/model telemetry is unavailable. The
assignment's active-work duration cannot be measured exactly, so charge the
full 720-second author envelope conservatively; remaining assignment budget:
0. A clock receipt during work is not treated as an exact active-time meter.
No tests were run. Writes stop when this handoff is submitted. Pending review
is the recipe spec review followed by architect/source-feasibility review;
only a clean independent review can precede a separate code-lease decision.
