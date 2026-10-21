# R259 — derive local sample evaluation roots

Status: primary-only read-only source derivation; no independent review.
Parent: Authoritative R149 Types/Console behavior. No change to accepted sample
bytes or expected output. No code, tests, builds, sample runs or production
admission.

## Inputs and exact owners

Y2 oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`. Reuse R257's exact
Web-to-WASM-to-root-source path and R258's conditional sample syntax-to-name
registration join. Reuse the admitted R152/R149 owner pins and R154's reviewed
generic registration/query relation. The additional name-reference owner is:

| Path | Blob | Role |
|---|---|---|
| `crates/infer/src/lowering/name_ref.rs` | `929e21b022c5f7015c8168fb936ba590691100a4` | Local-before-module name lookup and Value-classified reference construction. |

Other required owners are already pinned in R149/R152: `typing.rs`
(`7d8ad7846aaf4942512a23ad3710ddfd9d2e78be`), `body/mod.rs`
(`f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`), `body/methods.rs`
(`086d42bc63f1c12414a42898671dda22c8ac1084`), `expr/mod.rs`
(`5bbedd550c1edf877f4a7c254548ea02f47bcae8`), `expr/chain.rs`
(`e85beb100231264e210062bd56d8532b09b6200f`), `expr/tail.rs`
(`8289bfdc6a17b2469ae168ac7939d34813fda474`), `expr/lambda.rs`
(`724b103cda8b4e2c457aacf0a674372fb191e3d6`), and `expr/block_local.rs`
(`a406f4f9b7bc8e7e976014f2b348978e002a1191`).

## Conditional local-root derivation

- `our id x = x`: the registered header has one argument pattern. The
  successful defined-lambda path wraps the body in `Expr::Lambda` and returns
  `Computation::value`; it is a value fetch, not a ComputedDef initializer.
- `pub answer = id 42` and `pub name = id "Yulang"`: each has no binding
  argument pattern. Its body application lowers through `apply_arguments` and
  `make_source_app`; `make_app_with_origins` returns
  `Computation::computation`. On successful commit with publication enabled,
  each is recorded as `BindingFetch::FetchComputation` and emits a
  `RuntimeRoot::ComputedDef`.
- `pub pair = (answer, name)`: each name reference is a value-classified
  `Expr::Var` with a pure effect slot. `lower_paren` lowers the ordered
  expressions and `synthetic_tuple_value` chooses `Evaluation::Value` when no
  item is expansive. Conditional on both references lowering successfully,
  the pair binding is a value fetch, not a ComputedDef initializer. Its tuple
  value may still contain references to computations; this result does not
  claim their demand or runtime materialization behavior.
- `pair.say`: a successfully lowered direct root expression is pushed to
  `runtime_roots` as `RuntimeRoot::Expr`. The same separate path preserves the
  two Console expressions in source order. It does not depend on their
  expression-level Evaluation tag to be classified as expression roots.

R149's pinned `commit_provisional_binding` emits ComputedDef exactly when the
binding's `BindingFetch` runs a computation and the captured publication flag
is true. The source initializes root lowering with runtime-root suppression
off; the located production suppression scope is for copied act bodies. Thus,
conditional on successful sample root lowering and no enclosing copied-act
scope, the sample-local runtime-root subsequence is:

```text
Types:   ComputedDef(answer), ComputedDef(name), Expr(pair.say)
Console: Expr(println ...), Expr(say: 1 + 2)
```

The sample-local order follows the pinned unchanged source order and
source-order root traversal. This is a local subsequence, not the full mixed
module schedule; imported roots can precede or interleave through module
composition and remain separately required.

## Limits and falsifiers

This derivation is conditional on exact parse identity, successful name lookup,
successful body lowering/commit, and the recorded publication premises. It
does not observe numeric DefIds, prove that `answer`/`name` resolve to the
local `id`, prove accepted public types, or establish that pair display forces
and caches either initializer. It does not census any of the 40 imported
library files, determine composed order/cycles, specialize roots, or decide
sample-specific Request reachability. The previously identified runtime
EvalInstance host-request boundary remains conditional, not a sample failure.

Falsifiers include a source branch that wraps the application without
Computation classification, successful tuple lowering whose reference items
are expansive, a root sample binding under copied-act suppression, or a
consumer that does not preserve the listed local root subsequence. Parent
proofs, source/native correspondence, R70/R71, principality, soundness and
production remain OPEN. The full source-native design still requires
independent review before use as an implementation certificate.
