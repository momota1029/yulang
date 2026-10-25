# LEAN-CALL-FINITE-TYPING-20261025/r1 — typed finite Call prefixes and terminal views

Status: **FROZEN**, Luna primary. Baseline `c28827b29` (post-integration state checkpoint, branch `research/simple-sub-intrusion`). This fresh bounded sprint extends accepted existing-step preservation without claiming progress or reachability.

## Packet P — arbitrary finite-prefix preservation

In `YulangClosure.Control`, prove the exact proposition:

```lean
theorem call_state_typed_prefix_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {n : Nat} {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hp : YulangClosure.Prefix (CallControlStep md) n s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix
```

Use the existing length-indexed `YulangClosure.Prefix` from `Contracts.lean` (`refl`, `snoc`) and the accepted one-step theorem. Keep arbitrary `n`, initial typed state, metadata, and independently typed suffix. The snoc case composes equalities in final-to-initial direction. A zero-length prefix is included. The generic Prefix comment does not add external resumptions to `CallControlStep`.

## Packet Q — conditional terminal typing

In `YulangClosure.Control`, prove both statements, retaining empty frames explicitly:

```lean
theorem returned_call_state_typed
    {W : Type} {sig : Signature} {s : CallState W}
    {result : Ty} {v : TypedCall.Value}
    (ht : CallStateTyped sig s result)
    (hempty : s.frames = []) (hhead : s.head = .returned v) :
    TypedCall.ValueTyped Original.emptyContext v s.resultType
```

```lean
theorem requested_call_state_typed
    {W : Type} {sig : Signature} {s : CallState W}
    {result : Ty} {op : TypedCall.OperationInstance}
    {payload : TypedCall.Value} {continuation : TypedCall.Comp}
    (ht : CallStateTyped sig s result)
    (hempty : s.frames = []) (hhead : s.head = .requested op payload continuation) :
    TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
    TypedCall.CompTyped
      (Original.extend Original.emptyContext op.responseType)
      continuation s.resultType
```

Invert `CallStateTyped`, use `hempty` to invert empty `ContextTyping`, then invert the corresponding `CallHeadTyped` constructor. Do not equate the outer `result : Control.Ty` with `s.resultType : Original.Ty`; do not drop the response binder; do not assert that terminal heads are reached.

## Luna composition theorem

Luna owns one composition module. It may establish the initial-state helper:

```lean
theorem call_state_typed_start
    {W : Type} {sig : Signature}
    (term : TypedCall.CallTerm) (world : W)
    (suffix : List Frame) {result : Ty}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result) :
    CallStateTyped sig (CallState.initial term world suffix) result
```

Then prove the exact end-to-end conditional statement:

```lean
theorem initial_call_prefix_terminal_typing
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {target : CallState W}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) target) :
    CallStateTyped sig target result ∧
      target.resultType = term.resultType ∧ target.literalSuffix = suffix ∧
      (∀ v, target.frames = [] → target.head = .returned v →
        TypedCall.ValueTyped Original.emptyContext v target.resultType) ∧
      (∀ op payload continuation, target.frames = [] →
        target.head = .requested op payload continuation →
        TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
        TypedCall.CompTyped
          (Original.extend Original.emptyContext op.responseType)
          continuation target.resultType)
```

This asserts properties conditional on a supplied Prefix and, for terminal extraction, an explicitly empty frame stack. It proves neither a terminal-reaching trace nor progress, successor coverage, external resumption, conversion to ordinary Control, or a source/native theorem.

## Exact author leases

Packet P author writes only:

- `notes/theory/lean/YulangClosure/CallPrefixTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-prefix-typing.md`

Packet Q author writes only:

- `notes/theory/lean/YulangClosure/CallTerminalTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-terminal-typing.md`

Two separate Sol/high authors, at most 600 seconds each, may work in parallel. No Lean, tests, Git, descendants, extra sources, or other files. Each freezes exact hashes and STOPs before Luna verification. A proof needing a new premise or changed proposition stops and reports the exact obstruction.

## Luna verification and review leases

Luna alone writes/runs:

- `notes/theory/lean/YulangClosure/CallFiniteTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-verification.jsonl`
- `notes/theory/lean/.lake/call-finite-typing-r1-check.lean`
- `.olean` and `.ilean` for `CallPrefixTyping`, `CallTerminalTyping`, and `CallFiniteTyping` under `notes/theory/lean/.lake/build/lib/lean/YulangClosure/`
- `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-review.md`
- `tasks/agent-loop/sprints/call-finite-typing-20261025-r1-outcome.md`

After both authors STOP, Luna revalidates all pinned inputs and serially runs P compilation, Q compilation, composition compilation, then exact signature/axiom query. Each uses `-j1 -M1024`, timeout 120 seconds. Stop on the first failure, mismatch, or missing receipt; no automatic repair loop. After successful checks, a fresh nonauthor `compiler_referee` reviews the coherent three-module artifact and full receipts. CLEAN review and Luna adjudication are required.

## Pinned inputs and reusable successful outputs

| Source | SHA-256 |
|---|---|
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| r2 accepted outcome | `803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20` |
| r2 clean review | `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f` |
| r2 verification JSONL | `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a` |

Reuse only after hash revalidation: accepted `CallStepTypingRepair.olean` `d3ce599691c41652fb5663b843862cb250664a06279ce777721069d980456d98`, `.ilean` `8d56de64b33870fac7ed6b9a9ff7fc248d612ff12b638e498663625eb8920ed4`; `ControlTyping.olean` `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e`, `.ilean` `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f`; `ControlSyntax.olean` `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28`, `.ilean` `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1`; `Contracts.olean` `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc`, `.ilean` `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8`; `CoreSyntax.olean` `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751`, `.ilean` `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629`.
`CoreSubstitution.olean` `4539c98dfa46d89504823b389df535a336a7754abcca1b7005769d32bfa282e7`, `.ilean` `8a2761cb0e6ffa2df1fe2e66b34b0854dd30e0735a41c933d033c35fdb8fece2`; `CoreExecution.olean` `ff2fda0ecc175ae831f070d16e2a2382b3735f079338c60aee98f05cecddc05a`, `.ilean` `4818998f613d24fa6ab31bea7de36f77f407bf978438a85b25013afbdc798817`; `CallContextTyping.olean` `42c711d21b1f2d1cbd5486581448fce252d1b2bb9958329338ecf4dc9ac42204`, `.ilean` `1d32860c9c11b40785582a37f360987701b11d8f38dd3e85c8f5e0851e2d283a`; `CallEntryTypingRepair.olean` `0417fe931dda913d46712a601369424799963710c40cd1749afcc6b450e8de1e`, `.ilean` `967866bbd5badbe7b8deeb7d5bb4cd464ed95cbecf3d496702aab94fede1e7c5`; `CallPeelingTyping.olean` `de469ab6f25559f8c79b0f5242c310620b170e202dbdbebfba37f9343fa22df5`, `.ilean` `5d6b7afd92956b7ffe6ac715bf5e29aea0e49aea5a8fdb36601bc445179e5b4d`.

## Fresh budget and non-goals

Fresh cap **2,460 seconds**, no carryover: P 600, Q 600, Luna composition 180, serialized verification 480, fresh review 420, integration 180. Four Lean invocations maximum; one process/CPU, 1 GiB, timeout 120 seconds per invocation; Astra 0. Preserve all three historical UNKNOWN reservations. No Rust, runtime, source semantics, tests, docs, paper, or production edits.

Success proves finite-prefix preservation and conditional typing for returned/requested heads only when the supplied endpoint has no Call frames. It does not prove progress, terminal reachability, arbitrary endpoint emptiness, world/effect/receipt invariants, source/native correspondence, original Call A/B, inference A/B, or production. The `.force (.view (.delay body) occurrence)` gap stays OPEN; r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`.
