# Nested block returning a captured function: scoped source interpretation

Status: Authoritative
Scope: The source meaning of `my apply f = { my step x = f x; step }` only
Approved-by: user through `nested-block-function-source-realization/q1` answer `a1`
Approved-at: 2026-10-06
Drafted-by: primary
Reviewed-by: `architect` (pre-write authority/scope review); `spec_auditor` (exact approved-scope conformance; no findings)
Supersedes: the syntax architecture's deferred block-value interpretation only for the exact candidate named in this document

This addendum records the exact source interpretation selected in the
[approved question-board answer](../../questions/2026-10-05-nested-block-function-source-realization/approved-answer.md)
and its [integration receipt](../../questions/2026-10-05-nested-block-function-source-realization/receipt.md).
It resolves one source-to-core premise. It does not close the proof or
production-implementation gates for type inference.

## 1. Candidate and authority

The scope is the following exact candidate, using the existing one-parameter
Pattern application expansion for the outer and local binding headers:

```text
my apply f = { my step x = f x; step }
```

The Authoritative syntax architecture keeps the outer syntax node as
`BracedStatementBlockExpression` and leaves block-value interpretation to
later HIR/inference design. This addendum resolves that deferred interpretation
only for the candidate above. It does not change the grammar, CST ownership,
recovery, or interpretation of any other braced form.

The selected meaning comes from the user's approval of
`nested-block-function-source-realization/q1 a1`; the earlier approved
`function-call-view-formation/q1 a2` remains in force. The frozen Yulang2
material is compatibility evidence only. It supplies neither Yulang3 source
authority nor implementation permission.

## 2. Selected source meaning

For this candidate:

1. The block evaluates its local binding sequentially. The local `step`
   function is available to the final expression.
2. The final expression `step` yields the function value. It does not invoke
   that function.
3. In the local function body, `f` resolves to the outer `apply` formal and
   `x` resolves to the `step` formal.
4. The returned `step` function retains the lexical capture of that same outer
   `f` for later calls.

In the notation of the existing typed computation-core elaboration, the
intended structural correspondence is a one-parameter closure whose body
sequentially binds the local closure and returns its value:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

Here `bind` uses the existing ordinary binding rule, and `lambda`, `result`,
and `call` are the core derivation constructors, not new surface syntax or
new core operations. The `step` closure's lexical environment includes the
resolved outer `f`; the rule fixes that source identity and observable capture
across later calls, not a runtime allocation or storage strategy. The
application `f x` continues to use the approved Function call-view and
ordinary call rules. This structural correspondence does not itself prove
that current production HIR accepts or constructs the candidate.

## 3. Preserved boundaries

This addendum makes no decision about:

- exact-byte parser or typechecked-program acceptance by the current compiler;
- brace forms other than the exact candidate, including empty-record or
  record-like interpretations;
- recursive local definition groups or broader local polymorphism;
- effect execution, handler selection, or a new call-view registration rule;
- general closure allocation, lifetime, mutation, or capture policy;
- solver algorithms, production inference membership, or implementation.

Existing callback-literal B and role/entry decisions, annotation boundaries,
effect-protection decisions, and shared `nu,K,D` evidence remain unchanged.
Neither the type shape nor success of a Function comparison creates the
lexical binding, call path, capture, receipt, or authority used by this
candidate.

## 4. Remaining gates

Before implementation, derive and review the raw-brace to core correspondence
for this candidate against the source and typed-core rules, with explicit
premises for the typed call view and capture/evidence transport. Prove the
required principality and source-adequacy properties, establish current
production source acceptance and conformance, and close the remaining
inference-replacement soundness obligations. This addendum closes none of
those gates and grants no implementation authority.
