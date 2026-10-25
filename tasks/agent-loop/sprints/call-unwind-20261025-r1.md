# LEAN-CALL-UNWIND-20261025/r1 — bounded request/failure propagation

Status: **FROZEN**, Luna primary. Baseline: `64d39df59` on `research/simple-sub-intrusion`, after accepted finite Call typing r1. This sprint constructs only the existing relation's frame-unwind segments and composes them with supplied finite prefixes.

## P — actual request unwind

Author writes only `notes/theory/lean/YulangClosure/CallRequestUnwind.lean` and `tasks/agent-loop/inbox/20261025-call-request-unwind.md`. Define `CallState.captureFrames` by the existing `CallControlStep` equations, consuming the innermost frame first:

```lean
def CallState.captureFrames :
    List TypedCall.ContextFrame → TypedCall.Comp → TypedCall.Comp
  | [], continuation => continuation
  | .bind body :: frames, continuation =>
      captureFrames frames (CallState.captureBind continuation body)
  | .adapter _ _ body :: frames, continuation =>
      captureFrames frames (CallState.captureBind continuation body)
  | .scope owner :: frames, continuation =>
      captureFrames frames (.scope owner continuation)
  | .expose effectView resultView :: frames, continuation =>
      captureFrames frames (.expose effectView resultView continuation)
```

Prove in `YulangClosure.Control` the exact raw existence statement:

```lean
theorem call_request_unwind_exists
    {W : Type} (md : Metadata W)
    (world : W)
    (op : TypedCall.OperationInstance)
    (payload : TypedCall.Value)
    (continuation : TypedCall.Comp)
    (observed : List TypedCall.ViewOccurrence)
    (frames : List TypedCall.ContextFrame)
    (view : TypedCall.CallView)
    (result : Original.Ty)
    (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence)
    (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    ∃ (world' : W) (scopes' : List Nat),
      YulangClosure.Prefix (CallControlStep md) (frames.length + 1)
        ⟨world, .requesting op payload continuation observed,
          frames, view, result, scopes, views, receipts, suffix⟩
        ⟨world', .requested op payload
            (CallState.captureFrames frames continuation),
          [], view, result, scopes', observed, receipts, suffix⟩
```

The existence proof is unconditional for the represented requesting state and any four-constructor `ContextFrame` list. It must follow requestBind/requestAdapter/requestScope/requestExpose and finishRequest exactly. In particular, do not assert world/scope restoration; endpoint `viewContext` is `observed`; expose order is effectView then resultView; bind/adapter capture uses the existing binder-lifting `captureBind`.

## Q — actual failure unwind

Author writes only `notes/theory/lean/YulangClosure/CallFailureUnwind.lean` and `tasks/agent-loop/inbox/20261025-call-failure-unwind.md`. Prove:

```lean
theorem call_failure_unwind_exists
    {World : Type} (md : Metadata World)
    (world : World) (reason : Original.Failure)
    (frames : List TypedCall.ContextFrame)
    (view : TypedCall.CallView) (result : Original.Ty)
    (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence)
    (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    ∃ nextWorld : World,
      YulangClosure.Prefix (CallControlStep md) (frames.length + 1)
        ⟨world, .active (.fail reason), frames,
          view, result, scopes, views, receipts, suffix⟩
        ⟨nextWorld, .failed reason, [],
          view, result, scopes, views, receipts, suffix⟩
```

Induct over frames and use only the existing total cleanup witness `md.failWorld_total` with the exact `CallState.contextControlFrame` mapping and failBind/failAdapter/failScope/failExpose/finishFailure constructors. The final world is existential and may differ from the initial world. This empties only Call frames; it does not establish source reachability, cleanup correctness, or lifecycle restoration.

## Luna composition

Luna owns `notes/theory/lean/YulangClosure/CallUnwindTyping.lean`. Define an explicit `Prefix` concatenation lemma and prove two initial-trace corollaries. Both take an independently typed suffix and a supplied finite prefix from `CallState.initial term world suffix` to a state `s`; both preserve the exact combined length `n + (s.frames.length + 1)`. Apply accepted `CallFiniteTyping` formation/prefix preservation to the composed prefix. Do not claim that a signal state is reached.

The request corollary has premises:

```lean
(hsuffix : FramesTyped sig suffix (.original term.resultType) result)
(hp : YulangClosure.Prefix (CallControlStep md) n
  (CallState.initial term world suffix) s)
(hhead : s.head = .requesting op payload continuation observed)
```

and concludes existence of `t` with all of:

```lean
YulangClosure.Prefix (CallControlStep md) (n + (s.frames.length + 1))
  (CallState.initial term world suffix) t
t.head = .requested op payload (CallState.captureFrames s.frames continuation)
t.frames = []
CallStateTyped sig t result
t.resultType = term.resultType
t.literalSuffix = suffix
t.callView = s.callView
t.receiptSlots = s.receiptSlots
t.viewContext = observed
TypedCall.ValueTyped Original.emptyContext payload op.payloadType
TypedCall.CompTyped
  (Original.extend Original.emptyContext op.responseType)
  (CallState.captureFrames s.frames continuation) t.resultType
```

The failure corollary replaces `hhead` with `s.head = .active (.fail reason)` and concludes a `t` satisfying:

```lean
YulangClosure.Prefix (CallControlStep md) (n + (s.frames.length + 1))
  (CallState.initial term world suffix) t
t.head = .failed reason
t.frames = []
CallStateTyped sig t result
t.resultType = term.resultType
t.literalSuffix = suffix
t.callView = s.callView
t.scopeContext = s.scopeContext
t.viewContext = s.viewContext
t.receiptSlots = s.receiptSlots
```

No world equality is permitted for either corollary. The request corollary also makes no scopeContext equality claim. Retain the distinction between outer `result : Control.Ty` and `Original.Ty t.resultType`, the exact response binder, and `viewContext = observed`.

## Falsifiers and non-goals

A missing frame case, wrong length, reversed nesting, swapped expose views, ordinary bind instead of `captureBind`, lost response index shift, false world/scope equality, wrong request endpoint viewContext, or failure cleanup that does not use the actual metadata witness blocks the claim. Stop on the first elaboration or pin failure; no repair loop or proposition change under this revision.

No global progress, arbitrary terminal reachability, successor coverage, external resumption, metadata correctness, cleanup correctness, ordinary-Control handoff, source/native correspondence, original Call A/B, inference A/B, or production closure is claimed. The `.force (.view (.delay body) occurrence)` gap and r9 remain OPEN/UNACCEPTED. No Rust/runtime implementation slice is authorized; source construction/cleanup applicability remains an independent open lane.

## Exact leases, runtime and review

- Separate P and Q Sol/high authors, fresh caps 900s and 600s, disjoint two-path leases; no Lean/tests/Git/descendants/other writes.
- Luna composition cap 240s; serialized verification cap 480s; fresh nonauthor compiler_referee review cap 600s; integration cap 180s. Total fresh cap 3000s; Astra 0.
- Exactly four Lean invocations maximum: P, Q, composition, exact signature/axiom query, in that serial order. Each `-j1 -M1024`, timeout 120s; first failure/mismatch/missing receipt ends verification.
- The review is read-only and audits exact propositions, transition/frame coverage, capture order/binders, cleanup premises, endpoint metadata/world scope, composed length and full receipt/artifact hashes. P/Q authors and Luna cannot review.
- Preserve the three historical UNKNOWN quarantines. The active assignment ceiling is six including those three quarantines, Luna, and P/Q; review starts only after authors STOP.

## Frozen dependencies

The table below pins the accepted finite-typing dependency chain, its source/evidence, and reusable compiled outputs. Revalidate every pin after both authors STOP. The three new output pairs must be absent at activation. Contract SHA is recorded by current state after freezing.


| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `tasks/agent-loop/sprints/call-finite-typing-20261025-r1.md` | `dfff6b8af11651122ebc0b3be6cb6a8722b3ce7a60845eb4e82ba1a9488eee68` |
| `tasks/agent-loop/sprints/call-finite-typing-20261025-r1-outcome.md` | `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d` |
| `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-review.md` | `5ad32dc61b81056348607ba8bda344fd6c117806f14bf67dbcc8ae7b268c94c4` |
| `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-verification.jsonl` | `50a0c45503460cc166c45d5099698a1f7b8c3cd6a2cc5bd980f9386a1a86f108` |
| `notes/theory/lean/YulangClosure/CallPrefixTyping.lean` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `notes/theory/lean/YulangClosure/CallTerminalTyping.lean` | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| `notes/theory/lean/YulangClosure/CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| `tasks/agent-loop/inbox/20261025-call-prefix-typing.md` | `9a2e420d7fa7c19bfcf6509ad5a7fd8542abb500c08efa5ade7e4d469066a229` |
| `tasks/agent-loop/inbox/20261025-call-terminal-typing.md` | `3b749fe6ce042a3e2c2f62c3e687fe6494778686cf73689a048faefb8d27c399` |
| `tasks/agent-loop/sprints/call-step-typing-20261025-r2-outcome.md` | `803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20` |
| `tasks/agent-loop/inbox/20261025-call-step-typing-r2-review.md` | `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f` |
| `tasks/agent-loop/inbox/20261025-call-step-typing-r2-verification.jsonl` | `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.olean` | `d3ce599691c41652fb5663b843862cb250664a06279ce777721069d980456d98` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.ilean` | `8d56de64b33870fac7ed6b9a9ff7fc248d612ff12b638e498663625eb8920ed4` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.olean` | `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.ilean` | `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.olean` | `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.ilean` | `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.olean` | `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.ilean` | `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.olean` | `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.ilean` | `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.olean` | `4539c98dfa46d89504823b389df535a336a7754abcca1b7005769d32bfa282e7` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.ilean` | `8a2761cb0e6ffa2df1fe2e66b34b0854dd30e0735a41c933d033c35fdb8fece2` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.olean` | `ff2fda0ecc175ae831f070d16e2a2382b3735f079338c60aee98f05cecddc05a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.ilean` | `4818998f613d24fa6ab31bea7de36f77f407bf978438a85b25013afbdc798817` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.olean` | `42c711d21b1f2d1cbd5486581448fce252d1b2bb9958329338ecf4dc9ac42204` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.ilean` | `1d32860c9c11b40785582a37f360987701b11d8f38dd3e85c8f5e0851e2d283a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.olean` | `0417fe931dda913d46712a601369424799963710c40cd1749afcc6b450e8de1e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.ilean` | `967866bbd5badbe7b8deeb7d5bb4cd464ed95cbecf3d496702aab94fede1e7c5` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.olean` | `de469ab6f25559f8c79b0f5242c310620b170e202dbdbebfba37f9343fa22df5` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.ilean` | `5d6b7afd92956b7ffe6ac715bf5e29aea0e49aea5a8fdb36601bc445179e5b4d` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.olean` | `a33de65647d6815ca017a570423f0818c02725b5b11e9487f68a8e2e017e5b4f` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.ilean` | `c72378488754c04a78ce95e0407081dadde9828a7b8cd8c03680c92b862c3573` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.olean` | `2ce15a4d3116b463b561eae036414a3093fd76bc0b9d1d5ee65b2db561fae5cd` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.ilean` | `69898b2f1e3ddba8884e675351d59b109accd0fb43142abf6f15578f1c5bf725` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.olean` | `b7a78e73cfa6514255a48e5acccedd44ee8e13c57901304717a66c0b10c11101` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.ilean` | `035b106a76738aed9fca788f7c8814c197cbbe91f9b65300d4915e941cfbc791` |

Pinned records: 50. Reusable module output pairs: 26.
