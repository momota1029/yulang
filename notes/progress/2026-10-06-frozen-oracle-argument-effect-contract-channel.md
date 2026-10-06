# Frozen Oracle argument-effect contract channel

Date: 2026-10-06
Status: bounded historical characterization; independently compiler-referee-reviewed
(no findings); research-only; implementation and semantic authority: none
Yulang3 baseline: `32672661f`
Frozen historical source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`

## Question and result

The current open source producer must form a comparison-independent original
Function relation from resolved source structure, including annotation and
ordinary-call incidences, a complete static profile, typed paths/receipts, and
one joint `(nu,K,D)`. The earlier Oracle archaeology located annotation
constraints and formal-keyed call subtraction, but did not trace a distinct
annotation-to-call metadata channel.

The frozen Oracle contains a partial historical mechanism: annotation-derived
argument-effect markers are stored by resolved parameter `DefId`, looked up
for selected direct call arguments, and supplied to function-adapter hygiene.
This is a concrete annotation → definition → selected-use → guard-plan path.
The marker representation loses directed port position and has no annotation
occurrence, typed endpoint, owner/receiver, or receipt identity. It therefore
does not form the current original relation or close O. It supplies mechanism
evidence only; Oracle semantics, tests, and output are not authority.

## Historical producer and consumers

All paths below refer to the frozen source SHA above.

1. `crates/infer/src/lowering/expr/lambda.rs:1244–1335` builds a
   `LambdaPatternAnnotation.argument_effect_contract` while elaborating a
   parameter annotation. The unannotated branch at `:1257` stores `None`.
2. `lambda.rs:1357–1433` extracts concrete annotation effects into markers
   containing nominal `path`, Function nesting `depth`, and
   `PreserveMatchingPath` policy.
3. `lambda.rs:896–909` associates that contract with the resolved `DefId` of a
   variable or as-pattern parameter.
4. `crates/poly/src/expr.rs:81,148–163` retains a map
   `DefId -> ArgEffectContract`. The marker itself carries no annotation
   occurrence, directed port path, typed endpoint, owner, receiver, or receipt.
5. `crates/specialize/src/specialize2/emit.rs:249–266,1149–1231` resolves a
   call-spine head and argument ordinal to a defined Lambda parameter, looks
   up its contract, then passes it into argument-boundary adaptation.
6. `crates/specialize/src/hygiene.rs:15–88` combines supplied actual/expected
   Function types with these markers to construct
   `FunctionAdapterHygiene.arg_markers`.
7. `crates/specialize/src/specialize2/runtime_evidence.rs:1731–1759,1863–1930`
   separately records contract presence at application/Lambda evidence sites.
   Its actual and consumer slots are read from `SolvedExprType` at `:1818–1840`;
   they are not produced by the marker extractor.

This is a split pipeline: source lowering retains a limited annotation-derived
fact; specialization selects a call argument; hygiene combines the fact with
already supplied type endpoints. No single step constructs a complete
source-indexed typed call relation. Extraction itself does not consume Q, but
the enclosing historical flow also generates annotation constraints, while
adaptation consumes solved endpoints. This does not establish Q-independent
admission or its current proof obligation.

## A precise information-loss witness

Assume a concrete effect atom with nominal path `p`, and consider these already
formed annotation shapes:

```text
A = Function(param=_, arg_eff=[p], ret_eff=None, ret=_)
B = Function(param=_, arg_eff=None, ret_eff=[p], ret=_)
```

`collect_argument_contract_markers` visits both effect rows at `depth + 1`.
At root depth zero its output is therefore identical:

```text
M(A) = M(B) = [(p, 1, PreserveMatchingPath)]
```

The input distinguishes argument-effect from return-effect position while
the marker channel does not. This is a direct non-injectivity result for that
channel alone; downstream supplied types may still distinguish the endpoints.
Parser acceptance of these exact surface forms was not checked.

## Exact candidate and current correspondence boundary

Conditional on the earlier traced lowering path for
`my apply f = { my step x = f x; step }`, unannotated `f` produces no such
contract. At `f x`, the callee resolves to `Def::Arg`; the inspected lookup
requires a `Def::Let` whose body is a Lambda, so this path supplies no marker
for the candidate's formal call.

| Historical state | Current obligation it resembles | Missing bridge |
|---|---|---|
| Parameter annotation lowered to a `DefId`-keyed marker | Preserve annotation contribution through definition/use | No source annotation occurrence or complete annotation boundary/profile map |
| Selected call argument gets marker lookup | Associate a formal's call use with the declared contract | Only selected defined-Lambda argument slots; not a general formal/use relation |
| Hygiene plan combines markers with actual/expected types | Retain effect adaptation evidence at a call boundary | Endpoints arrive from solved types; no source-derived typed path/receipt producer |
| Runtime-evidence record flags contract presence | Carry a narrow fact into evidence construction | No owner/receiver activation or certified receipt correspondence |

The marker data is a useful historical shape for carrying annotation-derived
evidence across a definition/use boundary. It does not supply `beta` or
`Slots(beta)`, role resolution, Q-independent complete admission, original
joint `(nu,K,D)`, current Handler seed/discharge, soundness, principality, or
source adequacy. No current implementation should inherit marker semantics.

## Scope and verification

Claim class: bounded code-level characterization and a local representation
fact. The exact candidate is conditional on the previously inspected lowering
route; no candidate was executed or instrumented. Source paths were read at
the frozen SHA and their decisive files were byte-checked against Git blobs.
No build, tests, Oracle execution, randomized probes, mutation, or performance
measurement was performed. The absent-field claims apply only to the listed
marker definitions and inspected dataflow, not the entire Oracle repository.

Any later bridge must be derived from current approved rules and preserve
unresolved source constructors as explicit premises until proved. A newly
found historical field/path narrows only the historical characterization; it
does not confer semantic or implementation authority.
