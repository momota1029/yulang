# LEAN-CALL-UNWIND-20261025/r2 — initial-prefix composition repair

Status: **FROZEN**, Luna primary. Baseline: `33cd9e0a5` on `research/simple-sub-intrusion`, after r1 was adjudicated `FAILED_VERIFICATION / UNACCEPTED`.

## Goal and exact scope

Keep both r1 raw unwind propositions unchanged. Prove the two r1 initial-trace corollaries with the same supplied-prefix premises, exact combined length `n + (s.frames.length + 1)`, all endpoint fields, and response-binder typing. The only proof construction change is to normalize the two equalities from finite-prefix preservation before destructing `s`:

```lean
have hresult0 : s.resultType = term.resultType :=
  hresult.trans (by rfl)
have hliteral0 : s.literalSuffix = suffix :=
  hliteral.trans (by rfl)
```

These normalized equalities must be used for the result and literal-suffix conjuncts after constructing the endpoint. Do not import or reuse failed `CallUnwindTyping.lean`; the new module is `CallUnwindTypingRepair.lean`. This is a fresh revision, not repair authority under r1. Add no premise and change no theorem quantifier or conclusion.

### Request corollary

```lean
theorem call_request_unwind_initial_typed
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {continuation : TypedCall.Comp}
    {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload continuation observed) :
    ∃ t : CallState W,
      YulangClosure.Prefix (CallControlStep md)
        (n + (s.frames.length + 1))
        (CallState.initial term world suffix) t ∧
      t.head = .requested op payload
        (CallState.captureFrames s.frames continuation) ∧
      t.frames = [] ∧ CallStateTyped sig t result ∧
      t.resultType = term.resultType ∧ t.literalSuffix = suffix ∧
      t.callView = s.callView ∧ t.receiptSlots = s.receiptSlots ∧
      t.viewContext = observed ∧
      TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
      TypedCall.CompTyped
        (Original.extend Original.emptyContext op.responseType)
        (CallState.captureFrames s.frames continuation) t.resultType
```

### Failure corollary

```lean
theorem call_failure_unwind_initial_typed
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {reason : Original.Failure}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .active (.fail reason)) :
    ∃ t : CallState W,
      YulangClosure.Prefix (CallControlStep md)
        (n + (s.frames.length + 1))
        (CallState.initial term world suffix) t ∧
      t.head = .failed reason ∧ t.frames = [] ∧
      CallStateTyped sig t result ∧
      t.resultType = term.resultType ∧ t.literalSuffix = suffix ∧
      t.callView = s.callView ∧ t.scopeContext = s.scopeContext ∧
      t.viewContext = s.viewContext ∧ t.receiptSlots = s.receiptSlots
```

The theorem bodies must compose the two actual r1 unwind prefixes with an explicit `Prefix` concatenation lemma, then use accepted `CallFiniteTyping` preservation and terminal typing. Retain outer `result : Control.Ty` separately from `Original.Ty t.resultType`. No endpoint world equality, request scope equality, cleanup correctness, source reachability, or terminal reachability follows.

## Exact new paths and resource contract

Luna owns exactly:

- `notes/theory/lean/YulangClosure/CallUnwindTypingRepair.lean`
- `tasks/agent-loop/inbox/20261025-call-unwind-r2-verification.jsonl`
- `notes/theory/lean/.lake/call-unwind-r2-check.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallUnwindTypingRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallUnwindTypingRepair.ilean`
- this frozen contract, `tasks/agent-loop/inbox/20261025-call-unwind-r2-review.md`, and `tasks/agent-loop/sprints/call-unwind-20261025-r2-outcome.md`

Fresh cap **1260 seconds**: Luna composition 240, serialized verification 240, independent review 600, integration 180; Astra 0. Maximum two Lean invocations, in strict order: composition module, then exact signature/axiom query. Each invocation uses `lake env lean -j1 -M1024`, timeout 120 seconds, one CPU and 1024 MiB. No automatic retry. Stop on the first failed elaboration, pin mismatch, changed proposition or missing output/receipt.

The new module imports accepted `CallFiniteTyping` and the two unchanged r1 raw modules only. A fresh nonauthor `compiler_referee` reviews P, Q and the repaired composition together only after both invocations pass. P/Q authors cannot review; their source candidates and compiled outputs remain pending independent review until then. Luna owns verification, exact query, adjudication and Git.

## Frozen dependency pins

Revalidate every listed path/hash before authoring and immediately before verification. The first 50 rows are the exact frozen r1 dependency table; the additional 12 bind the r1 contract/outcome/receipt, P/Q source and handoffs, successful P/Q Lean outputs, and failed r1 composition candidate. New source/query/output paths must be absent at preflight.

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.ilean` | `1d32860c9c11b40785582a37f360987701b11d8f38dd3e85c8f5e0851e2d283a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.olean` | `42c711d21b1f2d1cbd5486581448fce252d1b2bb9958329338ecf4dc9ac42204` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.ilean` | `967866bbd5badbe7b8deeb7d5bb4cd464ed95cbecf3d496702aab94fede1e7c5` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.olean` | `0417fe931dda913d46712a601369424799963710c40cd1749afcc6b450e8de1e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFailureUnwind.ilean` | `626bbf215edc01f265b275963afca26855dd7a8c8283dd48d8f2376de4b3ce31` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFailureUnwind.olean` | `403a1deef6cb5939caf411032b9d824756f52d61de2f4bba45af5e19c2434367` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.ilean` | `035b106a76738aed9fca788f7c8814c197cbbe91f9b65300d4915e941cfbc791` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.olean` | `b7a78e73cfa6514255a48e5acccedd44ee8e13c57901304717a66c0b10c11101` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.ilean` | `5d6b7afd92956b7ffe6ac715bf5e29aea0e49aea5a8fdb36601bc445179e5b4d` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.olean` | `de469ab6f25559f8c79b0f5242c310620b170e202dbdbebfba37f9343fa22df5` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.ilean` | `c72378488754c04a78ce95e0407081dadde9828a7b8cd8c03680c92b862c3573` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.olean` | `a33de65647d6815ca017a570423f0818c02725b5b11e9487f68a8e2e017e5b4f` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestUnwind.ilean` | `0b671539a4205f6d94a8c9696eb6da97ce085d6eeb998f7e65d6a7bdf8b418f6` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestUnwind.olean` | `2016df0aa921033597505516d27d67ac715272d5146972a8c8c1bcb4e0008a23` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.ilean` | `8d56de64b33870fac7ed6b9a9ff7fc248d612ff12b638e498663625eb8920ed4` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.olean` | `d3ce599691c41652fb5663b843862cb250664a06279ce777721069d980456d98` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.ilean` | `69898b2f1e3ddba8884e675351d59b109accd0fb43142abf6f15578f1c5bf725` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.olean` | `2ce15a4d3116b463b561eae036414a3093fd76bc0b9d1d5ee65b2db561fae5cd` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.ilean` | `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.olean` | `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.ilean` | `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.olean` | `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.ilean` | `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.olean` | `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.ilean` | `4818998f613d24fa6ab31bea7de36f77f407bf978438a85b25013afbdc798817` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.olean` | `ff2fda0ecc175ae831f070d16e2a2382b3735f079338c60aee98f05cecddc05a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.ilean` | `8a2761cb0e6ffa2df1fe2e66b34b0854dd30e0735a41c933d033c35fdb8fece2` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.olean` | `4539c98dfa46d89504823b389df535a336a7754abcca1b7005769d32bfa282e7` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.ilean` | `5f369fcbe65119c88b59e2127bbeddecf2d53a6a68ffb6be347633572bb43629` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.olean` | `daefef78abdae103e9a6e8af2e439301680751991552b8ef14fa84620a423751` |
| `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `notes/theory/lean/YulangClosure/CallFailureUnwind.lean` | `2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c` |
| `notes/theory/lean/YulangClosure/CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `notes/theory/lean/YulangClosure/CallPrefixTyping.lean` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `notes/theory/lean/YulangClosure/CallRequestUnwind.lean` | `e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9` |
| `notes/theory/lean/YulangClosure/CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `notes/theory/lean/YulangClosure/CallTerminalTyping.lean` | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| `notes/theory/lean/YulangClosure/CallUnwindTyping.lean` | `57afc331d735c7b9680c8b1391ced1f86b72a0ab10ca37e9f620cf0388af1cc1` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `tasks/agent-loop/inbox/20261025-call-failure-unwind.md` | `880f530091fce6f2994c0b69a4b6f22a91a9fd6fbba9f1ee559c14d952d37437` |
| `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-review.md` | `5ad32dc61b81056348607ba8bda344fd6c117806f14bf67dbcc8ae7b268c94c4` |
| `tasks/agent-loop/inbox/20261025-call-finite-typing-r1-verification.jsonl` | `50a0c45503460cc166c45d5099698a1f7b8c3cd6a2cc5bd980f9386a1a86f108` |
| `tasks/agent-loop/inbox/20261025-call-prefix-typing.md` | `9a2e420d7fa7c19bfcf6509ad5a7fd8542abb500c08efa5ade7e4d469066a229` |
| `tasks/agent-loop/inbox/20261025-call-request-unwind.md` | `4aacb47b569a1bba3df4519e1540dbedd07cc3d42f0ce255641f5cd3119a710b` |
| `tasks/agent-loop/inbox/20261025-call-step-typing-r2-review.md` | `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f` |
| `tasks/agent-loop/inbox/20261025-call-step-typing-r2-verification.jsonl` | `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a` |
| `tasks/agent-loop/inbox/20261025-call-terminal-typing.md` | `3b749fe6ce042a3e2c2f62c3e687fe6494778686cf73689a048faefb8d27c399` |
| `tasks/agent-loop/inbox/20261025-call-unwind-r1-verification.jsonl` | `daa39582fc9455d444e6acb9daa61665b4bebfb65e53fc168d438b1b46ba273f` |
| `tasks/agent-loop/sprints/call-finite-typing-20261025-r1-outcome.md` | `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d` |
| `tasks/agent-loop/sprints/call-finite-typing-20261025-r1.md` | `dfff6b8af11651122ebc0b3be6cb6a8722b3ce7a60845eb4e82ba1a9488eee68` |
| `tasks/agent-loop/sprints/call-step-typing-20261025-r2-outcome.md` | `803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20` |
| `tasks/agent-loop/sprints/call-unwind-20261025-r1-outcome.md` | `331aab9fffd7f17fe7cbfdae98d723111a7a331b92cb672a7012a664557ef405` |
| `tasks/agent-loop/sprints/call-unwind-20261025-r1.md` | `efeaabb27416bd9cb51066c37f8a36d13b3a4ced3eeba7f1f9488ac4ada38a2a` |

## Falsifiers and non-goals

A changed theorem statement, added premise, incorrect equality bridge, lost capture binder, changed view or cleanup endpoint, wrong prefix length, unexpected axiom, or failed compilation blocks r2. Do not edit r1 artifacts or import its failed composition. P/Q can be accepted only with the fresh combined review.

No global progress/reachability, successor coverage, external resumption, metadata correctness, cleanup correctness, source/native correspondence, original Call A/B, inference A/B, or production closure is claimed. The `.force (.view (.delay body) occurrence)` gap and r9 remain OPEN/UNACCEPTED. No Rust/runtime implementation is authorized.
