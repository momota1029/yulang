# Native first-Call result origin: static falsification attempt

Date: 2026-10-16 (task-local date; tool clock was 2026-10-15 UTC)
Status: independently reviewed bounded falsification; no actual counterexample found
Primary-pinned native baseline: `0a9af0da5080469f930da0032aa96d7d89d358c5`
Write lease: this file only

Independent review: `ordinary_carrier_semantic` found no findings at SHA-256
`77618560dbe8f2537e7f9be648d5eda2ed611badbbb5a71a96d38726393086a7`.
The deletion discriminators are static decoder-validation arguments; no mutation
was executed. Negative search evidence does not close native transport adequacy.

## Objective, exact target and dependencies

Attack the claim that the existing source-indexed native construction can
preserve the correlation between the **same** original first-Call returning
witness `W` and its two tagged packet inputs under `xi=(nu,K,D)`, without
adding a new outer-formal seed. The original source case remains

```yu
my receive (f: () -> 'a) = {
    my g = f();
    g()
}
```

The target is a forward source-to-native interpretation of the actual
`ApplySourceInput`, authentic demand field 3 and parent Function/Result
dependency, including their retained copy history. It is not a unique inverse
from an interned row, a theorem that every native row inhabitant executes as
a source return, or proof that the native consumer implements typed packet
transport. Those are different statements.

The governing [source classification](2026-10-15-callback-result-exposure-classification.md)
§§1,3–5 fixes the original shared Call witness, actual-value packet input,
matching callee-result input and binding/read identities. Its review at
`f267a08e2` is supplied by the primary. Governing policy remains
[typed transport](../design/2026-10-02-typed-boundary-realization-draft.md)
§6, [directional introduction](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4,6, [callback B](../design/2026-10-03-callback-context-delivery.md)
§§2,2.1,4 and [top-level inference](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–4. The preceding [owning audit](../progress/2026-10-15-native-call-result-profile-transport-audit.md)
is a source locator and inventory, not a premise proving the interpretation.
The concurrently produced constructive proof was not read.

**Falsifier sought:** an actual supported source history and original
`(xi,W)` whose required two-input correlation has no compatible image through
the retained first-Apply Result construction, or two histories that the full
retained artifact cannot distinguish although the proposed same source-fiber
interpretation requires incompatible results. A collision after discarding
source inputs, parent edges or transport witnesses does not meet this target.

## Outcome and exact information retained

No such source-qualified witness or missing edge was found in this bounded
static attack. This is negative search evidence, not proof of preservation or
the original A/B parent. No new native field or source restriction follows.

The attempted erased observation was a bare native result row. The actual
observation inspected was larger:

```text
original LocalSource owner / Apply occurrence
  + ApplySourceInput(callee, argument, result, checking, recipe)
  + NativeInterface(demand, result)
  + actual parent Function relation
  + FunctionPort(parent, child, Result, Preserve)
  + Replay / Transport predecessors and their ordered bound keys
  + retained bound admissions, snapshots and use origins.
```

The original source reference is not inferred from a solved type.
`candidate_source.rs:978–1020` constructs the recipe and input together;
`shadow_apply.rs:1510–1540` validates their source fields before admission.
At `1548–1625` the same result component supplies the negative Function's
field 3 and the retained native result. `lib.rs:12590–12618` constructs the
Result child from the actual two Function field-3 endpoints.
`candidate_context.rs:3020–3063` records its exact parent, field and operation.
The temporary FunctionDispatch frame may finish; the dependency is retained
by `dependency` at `2660–2715`. The argument and ResultEffect fields remain
separate.

## Independent attacks and why they do not supply a counterexample

| Attack | Owning construction inspected | Outcome |
| --- | --- | --- |
| Two source calls happen to have equal result rows/types | `ApplySourceInput` at `candidate_call.rs:37–55`; source registration at `candidate_source.rs:1009–1019`; origins at `candidate_context.rs:2926–2934` | Original Apply owner/expression/checking identity and source indices remain available. Equal rows are an erased observation, not equality of the retained source-indexed construction. |
| One source call returns different callable packets in different source fibers | Original source classification §§1,3–4; actual result field/parent edge above | Distinct `W` or `xi` indices may inhabit the same relational native artifact. A single-valued inverse from the artifact is not required by forward embedding. This candidate does not show that one fixed original fiber loses either tagged inlet. |
| Provider lower and source upper meet at a shared row and source sets become a union | Replay at `candidate_context.rs:3410–3456`; `Dependency::Replay` at `267–273` | The source set is not the only evidence. Replay retains ordered lower/upper RelationIds and both original input BoundKeys. Multiple replays can share a child relation while retaining different dependency records. A set union therefore does not establish recombination of unrelated providers/returns. |
| Relation interning collapses different derivations | `RelationKey` at `candidate_context.rs:223–228`; interning at `2569–2600`; dependency interning at `2660–2715` | A RelationId is a node, not a unique derivation. Dependency identity includes the parent references and field or transport witness. Origin records are retained separately. Derivation-indexed fibers remain possible; the audit does not prove their complete semantic valuation. |
| Endpoint memoization omits a new source-specific Function/Result edge | `pair_is_current` at `lib.rs:11546–11555`; actual dispatch at `12349–12382,12739–12763` | In candidate mode completion is checked for the actual processing relation and current generation, not only the endpoint pair. The proposed endpoint-only suppression argument does not match this code. No source history producing the alleged missing edge was established. |
| Level copies or FreshUse merge the result with an older shared anchor | `candidate_extrusion.rs:93–128,325–370`; `candidate_scheme.rs:557–609,1088–1099,1333–1379`; `candidate_context.rs:3658–3669` | Actual source/destination bound keys, antecedent evidence and transport parent/use origin remain available. Nonlocal rows intentionally remain session anchors. Fresh child relation interning does not erase the separately retained Transport records. Complete semantic preservation through all histories is not proved here. |
| Two result packet inputs have equal endpoints or equal protection entries, so their tags must disappear | Source classification §4 and actual parent/source construction | Equal endpoint denotations do not require packet-inlet tags to be stored as different row IDs. The source result rule fixes two indexed inputs of the same Call witness. A source-indexed valuation can keep those indices. No actual producer forcing an untagged semantic union was found; a consumer implementing the required joint image is separately unverified. |

In particular, a fully retained source occurrence can denote all its original
returning fibers. Supplying a different returned profile at the same source
occurrence is not an indistinguishability contradiction unless the claim also
requires that the artifact choose that return without the original fiber
index. This attack does not impose that stronger claim. Conversely, merely
declaring a valuation indexed by the source is not enough to prove its
compatibility with the actual copy maps or native constraints. That positive
construction remains the prover's obligation.

## Static mutation discriminant: what the real Result edge contributes

No mutation was applied or executed. This is a paper check of a named shortcut,
using the actual field sorts and constructors rather than a toy transition
model.

The real construction has the local square

```text
ApplySourceInput.result = r
          | candidate_endpoint(_, Negative)
          v
demand.result = r−                  [Function field 3]
          ^
          | actual Result child
parent.lower.result = R+  --------> r−
```

The local install uses the original initializer endpoint `r`, rather than
an independently chosen endpoint. A transport step may replace an endpoint
by its actual copied image; its retained transport references then supply
the corresponding square rather than literal row equality.

Counterfactually replace demand field 3 with a correctly negative **unrelated
Value endpoint** `z−`, while leaving the recorded Apply result and local
install at `r`. Then native Result decomposition concludes `R+ <: z−`.
There is no longer a Result edge into the recorded initializer `r−`. The
native/source endpoint square fails at construction, before packet-profile
reasoning or the second call. This discriminates a real use of the retained
Result edge from an interpretation that simply labels an arbitrary row with
the source answer. It supplies no evidence that this mutation occurs.

Moving field 3 to ResultEffect would additionally violate the actual
Value/Effect field distinction and is an easier, less useful mutation.
Deleting only the `FunctionPort` record while retaining all Function terms,
source inputs and scalar child tasks removes this direct derivation
certificate, but does **not** prove information-theoretic impossibility:
those remaining owners might permit an alternative reconstruction. This note
does not claim that any one redundant metadata field is individually
necessary. The real edge, source attribution and copy witnesses must be
considered together.

## Claim boundary, coverage and next action

This lane supplies bounded falsification evidence against the proposed loss
argument. It does not certify the forward embedding. It especially does not
establish that every native model has an original source witness, that all
source histories reach Function dispatch/capture, that consumers preserve
joint `K,D`/profile meaning, or that a native evaluator performs complete Call
and live protection. Producer representation, forward semantic interpretation,
all-model soundness and executable consumer closure remain distinct gates.

The exact second-Apply scoped Local-callee guard remains experiment coverage,
not a source-qualified loss witness. No new seed is generated at `g` from
this sequence; independently justified evidence is retained as an obligation.
No source acceptance boundary, parent scope or language meaning is changed.

Recommended next action: independently review the constructive lane's explicit
source-indexed valuation against these actual source, Result and transport
owners, paying particular attention to use of the **same** original `(xi,W)`
for both tagged inlets. Do not demand a unique inverse or infer consumer
closure from successful forward interpretation.

## Checks, resources and commit packet

Method independence: this attack read actual production owners and the
previous source classification, not the moving constructive proof. Shared
assumptions are the pinned native baseline and accepted source rules. There
is no independent operational oracle, executable model, probe or test. The
mutation above is static source inspection only. Seeds, enumerated ranges,
runtime sample counts and mutations executed: none. The search is not an
exhaustive enumeration of source programs or histories.

Commands: bounded `cat`, `rg`, `sed`, `nl`, dependency `sha256sum`, and clock
reads. Up to two lightweight read-only shell processes were batched; zero
heavy processes. No Git, compiler edits, builds, tests, probes, delegates or
other output paths. Budget: 20 minutes; CPU/RAM uninstrumented. Native hashes
below match the earlier audit where it records those files; two newly read
owners have hashes recorded without a no-Git baseline comparison.

```text
26abb65f09f2dcf7b3f798329d7f9cf867d3e6196b4cd79c03b3b558d90566e5  crates/yu-solver/src/candidate_source.rs
4689e2ee34c69c9492ecc1a58af15d7c802f44dca82d69f76e3e1520d8d5f3dd  crates/yu-solver/src/candidate_call.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
1a3c55abf2da669342076465c53d72aff185a9d7307374a9011d47ddd7458ef5  crates/yu-solver/src/candidate_value_graph.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
6f2bc05137e451c38391655bb2d45e9224f12eebf7d58c7f5a78c8abd69c93f4  notes/theory/2026-10-15-callback-result-exposure-classification.md
9e3cf4d00f50a897d00cb211d8bca3517551f33d4274bef556cefd96c9c2ff82  notes/progress/2026-10-15-native-call-result-profile-transport-audit.md
```

- Exact lease: `notes/theory/2026-10-16-native-result-origin-falsification.md`.
- Baseline: `0a9af0da5080469f930da0032aa96d7d89d358c5`.
- Changed dependencies: no native delta against the earlier audit's overlapping
  hash inventory; direct baseline comparison of newly inspected files remains
  primary-owned. The completed audit was only read, not edited.
- Claim/review: honest negative static search; fresh independent review pending.
- Checks run: owning-source inspection and dependency hashes; no executable
  validation. Artifact frozen on handoff.
- Proposed message: `research: attack native first-Call result origin correlation`.
- Shared deltas left to primary/curator: record no actual falsifier found;
  retain all original A/B parent gates and separate producer interpretation,
  whole-history coverage and executable consumer closure. No theorem promotion.

### Primary integration (2026-10-16)

The producer handoff above is historical; independent review is recorded in
the header. The primary checked the combined 16-dependency inventory against
current files, and all 10 native source files against `0a9af0da5`; every hash
matches, including the newly inspected owners. No executable mutation or test
was run. This note and its constructive companion share one M2 referee review;
task, laboratory and design-index records preserve their limited conclusions.
